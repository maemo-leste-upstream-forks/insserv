/*
 * insserv(.c)
 *
 * Copyright 2000-2005 Werner Fink, 2000 SuSE GmbH Nuernberg, Germany,
 *				    2003 SuSE Linux AG, Germany.
 *				    2004 SuSE LINUX AG, Germany.
 *				    2005 SUSE LINUX Products GmbH
 * Copyright 2005 Petter Reinholdtsen
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 */

#include <pwd.h>
#include <string.h>
#include <unistd.h>
#include <ctype.h>
#include <stdio.h>
#include <stdarg.h>
#include <stdlib.h>
#include <fcntl.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <dirent.h>
#include <regex.h>
#include <errno.h>
#include <limits.h>
#include <getopt.h>
#include "listing.h"

static char *map_runlevel_to_location(const int runlevel);
static const int map_runlevel_to_lvl (const int runlevel) __attribute__ ((unused));
static const int map_runlevel_to_seek(const int runlevel) __attribute__ ((unused));

#ifndef  INITDIR
# define INITDIR	"/etc/init.d"
#endif
#ifndef  INSCONF
# define INSCONF	"/etc/insserv.conf"
#endif

/*
 * For a description of regular expressions see regex(7).
 */
#define COMM		"^#[[:blank:]]*"
#define VALUE		":[[:blank:]]*([[:print:][:blank:]]*)"
/* The second substring contains our value (the first is all) */
#define SUBNUM		2
#define SUBNUM_SHD	3
#define START		"[-_]+start"
#define STOP		"[-_]+stop"

/* The main regular search expressions */
#define PROVIDES	COMM "provides" VALUE
#define REQUIRED	COMM "required"
#define SHOULD		COMM "(x[-_]+[a-z0-9_-]+)?should"
#define DEFAULT		COMM "default"
#define REQUIRED_START  REQUIRED START VALUE
#define REQUIRED_STOP	REQUIRED STOP  VALUE
#define SHOULD_START	SHOULD   START VALUE
#define SHOULD_STOP	SHOULD   STOP  VALUE
#define DEFAULT_START	DEFAULT  START VALUE
#define DEFAULT_STOP	DEFAULT  STOP  VALUE
#define DESCRIPTION	COMM "description" VALUE

/* System facility search within /etc/insserv.conf */
#define EQSIGN		"([[:blank:]]?[=:]+[[:blank:]]?|[[:blank:]]+)"
#define CONFLINE	"^(\\$[a-z0-9_-]+)" EQSIGN "([[:print:][:blank:]]*)"
#define CONFLINE2	"^(<[a-z0-9_-]+>)"  EQSIGN "([[:print:][:blank:]]*)"
#define SUBCONF		2
#define SUBCONFNUM	4

/* The main line buffer if unique */
static char buf[LINE_MAX];

/* When to be verbose */
static boolean verbose = false;

/* When to be verbose */
static boolean dryrun = false;

/* Search results points here */
typedef struct lsb_struct {
    char *provides;
    char *required_start;
    char *required_stop;
    char *should_start;
    char *should_stop;
    char *default_start;
    char *default_stop;
    char *description;
} lsb_t;

/* Search results points here */
typedef struct reg_struct {
    regex_t prov;
    regex_t req_start;
    regex_t req_stop;
    regex_t shl_start;
    regex_t shl_stop;
    regex_t def_start;
    regex_t def_stop;
    regex_t desc;
} reg_t;

static lsb_t script_inf;
static reg_t reg;
static char empty[1] = "";

/* Delimeters used for spliting results with strsep(3) */
const char *const delimeter = " ,;\t";

/*
 * push and pop directory changes: pushd() and popd()
 */
typedef struct pwd_struct {
    list_t	deep;
    char	*pwd;
} pwd_t;
#define getpwd(list)	list_entry((list), struct pwd_struct, deep)

static list_t pwd = { &(pwd), &(pwd) }, * topd = &(pwd);

static void pushd(const char *const path)
{
    pwd_t *  dir;

    dir = (pwd_t *)malloc(sizeof(pwd_t));
    if (dir) {
	if (!(dir->pwd = getcwd(NULL, 0)))
	    goto err;
	insert(&(dir->deep), topd->prev);
	goto out;
    }
err:
    error("%s", strerror(errno));
out:
    if (chdir(path) < 0)
	    error ("pushd() can not change to directory %s: %s\n", path, strerror(errno));
}

static void popd(void)
{
    list_t * tail = topd->prev;
    pwd_t *  dir;

    if (tail == topd)
	goto out;
    dir = getpwd(tail);
    if (chdir(dir->pwd) < 0)
	error ("popd() can not change directory %s: %s\n", dir->pwd, strerror(errno));
    free(dir->pwd);
    delete(tail);
    free(dir);
out:
    return;
}

/*
 * Linked list of system facilities services and their replacment
 */
typedef struct faci {
    list_t	 list;
    char	*name;
    char	*repl;
} faci_t;
#define getfaci(arg)	list_entry((arg), struct faci, list)

static list_t sysfaci = { &(sysfaci), &(sysfaci) }, *sysfaci_start = &(sysfaci);

/*
 * Linked list of required services of a service
 */
typedef struct req_serv {
    list_t	  list;
    unsigned int flags;
    char        * serv;
} req_t;
#define	REQ_MUST	0x00000001
#define	REQ_SHLD	0x00000002
#define getreq(arg)	list_entry((arg), struct req_serv, list)
#define getrev(arg)	list_entry((arg), struct req_serv, list)

/*
 * Linked list to hold hold information of services
 */
#define SERV_KNOWN	0x00000001
#define SERV_NOTLSB	0x00000002
#define SERV_DOUBLE	0x00000004
#define SERV_ACTIVE	0x00000008
#define SERV_ENABLED	0x00000010
#define SERV_ALL	0x00000020
#define SERV_DUPLET	0x00000040

typedef struct sort_struct {
    list_t req, rev;
} sort_t;

struct serv_struct;
typedef struct serv_struct serv_t;

struct serv_struct {
    list_t	   id;
    sort_t	 sort;
    unsigned int opts;
    char	order;
    char       * name;
    serv_t     * main;
    unsigned int lvls;
#ifndef SUSE
    unsigned int lvlk;
#endif /* not SUSE */
};
#define getserv(arg)	list_entry((arg), struct serv_struct, id)

static list_t serv = { &(serv), &(serv) }, *serv_start = &(serv);

/*
 * Find or add and initialize a service
 */
static serv_t * addserv(const char *const serv)
{
    serv_t * this;
    list_t * ptr;

    list_for_each(ptr, serv_start) {
	if (!strcmp(getserv(ptr)->name, serv))
	    goto out;
    }

    this = (serv_t *)malloc(sizeof(serv_t));
    if (this) {
	list_t * req_start = &(this->sort.req);	// List head for required servs of this
	list_t * rev_start = &(this->sort.rev); // List head for servs which requires this

	insert(&(this->id), serv_start->prev);

	req_start->next = req_start;
	req_start->prev = req_start;

	rev_start->next = rev_start;
	rev_start->prev = rev_start;

	this->opts  = 0;
	this->name  = xstrdup(serv);
	this->main  = (serv_t *)0;
	this->order = 0;
	this->lvls  = 0;
#ifndef SUSE
	this->lvlk  = 0;
#endif /* not SUSE */
	ptr = serv_start->prev;
	goto out;
    }
    ptr = NULL;
    error("%s", strerror(errno));
out:
    return getserv(ptr);
}

static serv_t * findserv(const char *const serv)
{
    list_t * ptr;
    serv_t * ret = NULL;

    if (!serv)
	goto out;

    list_for_each(ptr, serv_start) {
	if (!strcmp(getserv(ptr)->name, serv)) {
	    ret = getserv(ptr);
	    break;
	}
    }
out:
    return ret;
}

/*
 * Remember requests for required or should services and expand `$' token
 */
static void rememberreq(serv_t *serv, unsigned int bit, char * required)
{
    char * token, * tmp = strdupa(required);
    list_t * ptr;
    unsigned int old = bit;

    while ((token = strsep(&tmp, delimeter))) {
	boolean found = false;
	req_t * this;

	if (!*token)
	    continue;

	bit = old;
again:
	switch(*token) {
	default:
	    list_for_each(ptr, &(serv->sort.req)) {
		if (!strcmp(getreq(ptr)->serv, token)) {
		    found = true;
		    break;
		}
	    }
	    if (found) {
		getreq(ptr)->flags |= bit;
		break;
	    }

	    this = (req_t *)malloc(sizeof(req_t));
	    if (!this)
		error("%s", strerror(errno));
	    insert(&(this->list), (&(serv->sort.req))->prev);
	    this->serv  = xstrdup(token);
	    this->flags = bit;

	    break;
	case '$':
	    if (strcasecmp(token, "$all") == 0) {
		serv->opts |= SERV_ALL;
		break;
	    }
	    /* Expand the `$' token recursively down */
	    list_for_each(ptr, sysfaci_start) {
		if (!strcmp(token, getfaci(ptr)->name)) {
		    rememberreq(serv, bit, getfaci(ptr)->repl);
		    break;
		}
	    }
	    break;
	case '+':
	    /* This is an optional token */
	    token++;
	    bit = REQ_SHLD;
	    goto again;
	    break;
	}
    }

    /* Expand requested services for sorting */
    list_for_each(ptr, &(serv->sort.req)) {
	char * needed = getreq(ptr)->serv;
	if (needed)
	    requiresv(serv->name, needed);
    }
}

/*
 * Check required services for name
 */
static boolean chkrequired(const char *const name)
{
    serv_t * serv = findserv(name);
    list_t * req_start, * pos;
    boolean ret = true;

    if (serv && !list_empty(&(serv->sort.req)))
	req_start = &(serv->sort.req);
    else
	goto out;

    list_for_each(pos, req_start) {
	req_t *req = getreq(pos);
	serv_t * must;
	if (!(req->flags & REQ_MUST))
	    continue;

	if (!(must = findserv(req->serv)) || !(must->opts & SERV_ENABLED)) {
	    warn("Service %s has to be enabled for service %s\n", req->serv, name);
	    ret = false;
	}
    }
out:
    return ret;
}

/*
 * Check dependencies for name as a service
 */
static boolean chkdependencies(const char *const name)
{
    list_t * srv;
    boolean ret = true;

    list_for_each(srv, serv_start) {
	serv_t * cur = getserv(srv);
	list_t * pos;

	if (!cur || list_empty(&(cur->sort.req)) || !(cur->opts & SERV_ENABLED))
	    continue;

	list_for_each(pos, &(cur->sort.req)) {
	    req_t *req = getreq(pos);

	    if (!(req->flags & REQ_MUST))
		continue;

	    if (!strcmp(req->serv, name)) {
		warn("Service %s has to be enabled for service %s\n", name, cur->name);
		ret = false;
	    }
	}
    }
    return ret;
}

/*
 * This helps us to work out the current symbolic link structure
 */
static serv_t * current_structure(const char *const this, const char order, const int runlvl)
{
    serv_t * serv = addserv(this);

    if (serv->order < order)
	serv->order = order;

    switch (runlvl) {
	case 0: serv->lvls |= LVL_HALT;   break;
	case 1: serv->lvls |= LVL_ONE;    break;
	case 2: serv->lvls |= LVL_TWO;    break;
	case 3: serv->lvls |= LVL_THREE;  break;
	case 4: serv->lvls |= LVL_FOUR;   break;
	case 5: serv->lvls |= LVL_FIVE;   break;
	case 6: serv->lvls |= LVL_REBOOT; break;
	case 7: serv->lvls |= LVL_SINGLE; break;
	case 8: serv->lvls |= LVL_BOOT;   break;
	default: break;
    }

    return serv;
}

static void setlsb(const char* const name)
{
    serv_t * serv = findserv(name);
    if (serv)
	serv->opts &= ~SERV_NOTLSB;
}

/*
 * This helps us to set none LSB conform scripts to required
 * max order, therefore we set a dependency to the first
 * lsb conform service found in current link scheme.
 */
static inline void nonlsb_script(void)
{
    list_t * pos;

    list_for_each(pos, serv_start) {
	if (getserv(pos)->opts & SERV_NOTLSB) {
	    list_t * tmp, * req = NULL;
	    char max = 0;

	    list_for_each(tmp, serv_start) {
		if (getserv(tmp)->opts & SERV_NOTLSB)
		    continue;
		if (!getserv(tmp)->order)
		    continue;
		if (!(getserv(pos)->lvls & getserv(tmp)->lvls))
		    continue;
		if (getserv(tmp)->order >= getserv(pos)->order)
		    continue;
		if (max < getserv(tmp)->order) {
		    max = getserv(tmp)->order;
		    req = tmp;
		}
	    }

	    if (req)
		requiresv(getserv(pos)->name, getserv(req)->name);
	}
    }
}

/*
 * This helps us to get interactive scripts to be the only service
 * within on start or stop service group. Remaining problem is that
 * if required scripts are missed the order can be wrong.
 */
static inline void active_script(void)
{
    list_t * pos;
    int deep = 1;

    for (deep = 0; deep < 100; deep++) {
	list_for_each(pos, serv_start) {
	    serv_t * serv = getserv(pos);
	    list_t * tmp;

	    if (!(serv->opts & SERV_ACTIVE))
		continue;

	    if (serv->order != deep)
		continue;

	    list_for_each(tmp, serv_start) {
		serv_t * cur = getserv(tmp);
		serv_t * chk = NULL;
		list_t * req;
		const char *name;
		boolean ignore = false;

		if (!(serv->lvls & cur->lvls))
		    continue;

		if (cur->opts & SERV_DUPLET)
		   continue;		/* Duplet */

		if (cur == serv)
		    continue;

		if (serv->main && (serv->main == cur))
		    continue;		/* Duplet */

		/*
		 * Expand aliases to the real script name
		 */
		if ((name = getscript(cur->name)) == NULL)
		    name = cur->name;

		/*
		 * Ignore services which the active service requires
		 */
		list_for_each(req, &(serv->sort.req)) {
		    if (!strcmp(getreq(req)->serv, cur->name))
			ignore = true;
		    if (!strcmp(getreq(req)->serv, name))
			ignore = true;
		}
		if (ignore) continue;

		/*
		 * Increase order of members of the same start
		 * group and recalculate dependency order (`true')
		 */
		serv->order = getorder(serv->name);
		cur->order  = getorder(name);

		if (serv->order == cur->order)
		    setorder(name, ++cur->order, true);

		/* Remember the order even for the alias */
		if ((chk = findserv(name)) && (cur != chk))
		    chk->order = cur->order;
	    }
	}
    }
}

/*
 * Alt last but not least the `$all' scripts will be set to the of
 * current the start order.
 */

static inline void all_script(void)
{
    list_t * pos;

    list_for_each(pos, serv_start) {
	serv_t * serv = getserv(pos);
	list_t * tmp;
	int neworder;

	if (!(serv->opts & SERV_ALL))
	    continue;

	neworder = 0;
	list_for_each(tmp, serv_start) {
	    serv_t * cur = getserv(tmp);

	    if (!(serv->lvls & cur->lvls))
		continue;

	    if (cur == serv)
		continue;

	    if (cur->opts & SERV_ALL)
		continue;

	    if ((cur->order = getorder(cur->name)) > neworder)
		neworder = cur->order;
	}
	neworder++;
	if      (neworder > 99)
	    neworder = maxorder;
	else if (neworder > maxorder)
	    maxorder = neworder;
	setorder(serv->name, neworder, false);
    }
}

/*
 * Remember reverse requests for required services
 */
static void reverse(char *stop, char *request)
{
    serv_t * srv = addserv(stop);
    list_t * ptr;
    req_t  * this;

    list_for_each(ptr, &(srv->sort.rev)) {
	if (!strcmp(getrev(ptr)->serv, request))
	    goto out;
    }

    this = (req_t *)malloc(sizeof(req_t));
    if (!this)
	error("%s", strerror(errno));
    insert(&(this->list), (&(srv->sort.rev))->prev);
    this->serv  = request;	/* xstrdup not needed */
    this->flags = 0;
out:
    return;
}

/*
 * Make the dependency files
 */
static inline void makedep(void)
{
    list_t * srv;
    FILE *boot, *start, *stop, *out;
    const char *name;

    if (dryrun) {
	info("dryrun, not creating .depend.boot, .depend.start and .depend.stop\n");
	return;
    }
    if (!(boot  = fopen(".depend.boot",  "w"))) {
	warn("fopen(.depend.stop): %s\n", strerror(errno));
	return;
    }
    if (!(start = fopen(".depend.start", "w"))) {
	warn("fopen(.depend.start): %s\n", strerror(errno));
	fclose(boot);
	return;
    }
    info("creating .depend.boot\n");
    info("creating .depend.start\n");

    name = NULL;
    fprintf(boot, "TARGETS =");
    while (listscripts(&name, LVL_BOOT))
	fprintf(boot, " %s", name);
    putc('\n', boot);

    name = NULL;
    fprintf(start, "TARGETS =");
    while (listscripts(&name, LVL_ALL))		/* LVL_ALL: nearly all but not BOOT */
	fprintf(start, " %s", name);
    putc('\n', start);

    fprintf(boot,  "INTERACTIVE =");
    fprintf(start, "INTERACTIVE =");
    list_for_each(srv, serv_start) {
	serv_t * cur = getserv(srv);

	if (!cur || list_empty(&(cur->sort.req)))
	    continue;

	if (cur->lvls & LVL_BOOT)
	    out = boot;
	else
	    out = start;

	if ((name = getscript(cur->name)) == 0)
	    name = cur->name;

	if (cur->opts & SERV_DUPLET)
	    continue;				/* Duplet */

	if (cur->opts & SERV_ACTIVE)
	    fprintf(out, " %s", name);
    }
    putc('\n', boot);
    putc('\n', start);

    list_for_each(srv, serv_start) {
	serv_t * cur = getserv(srv);
	list_t * pos;

	if (!cur || list_empty(&(cur->sort.req)))
	    continue;

	if (cur->lvls & LVL_BOOT)
	    out = boot;
	else
	    out = start;

	if ((name = getscript(cur->name)) == 0)
	    name = cur->name;

	if (cur->opts & SERV_DUPLET)
	    continue;				/* Duplet */

	fprintf(out, "%s:", name);

	if (cur->opts & SERV_ALL) {
	    list_for_each(pos, serv_start) {
		serv_t * dep = getserv(pos);

		/*
		 * No self dependcies or from the last
		 */
		if ((dep == cur) || (dep && (dep->opts & SERV_ALL)))
		    continue;

		/*
		 * Skip not existing services even if they are used
		 * otherwise the make call will skip all dependencies
		 */
		if (!dep) continue;

		if ((dep->opts & SERV_DUPLET) && dep->main)
		    dep = dep->main;		/* Duplet */

		if ((name = getscript(dep->name)) == NULL)
		    name = dep->name;

		if (cur->lvls & dep->lvls)
		    fprintf(out, " %s", name);
	    }
	} else {
	    list_for_each(pos, &(cur->sort.req)) {
		req_t  * req = getreq(pos);
		serv_t * dep = findserv(req->serv);

		/*
		 * No self dependcies or from the last
		 */
		if ((dep == cur) || (dep && (dep->opts & SERV_ALL)))
		    continue;

		reverse(req->serv, cur->name);

		/*
		 * Skip not existing services even if they are used
		 * otherwise the make call will skip all dependencies
		 */
		if (!dep) continue;

		if ((dep->opts & SERV_DUPLET) && dep->main)
		    dep = dep->main;		/* Duplet */

		if ((name = getscript(req->serv)) == NULL)
		    name = req->serv;

		if (cur->lvls & dep->lvls)
		    fprintf(out, " %s", name);
	    }
	}
	putc('\n', out);
    }

    fclose(boot);
    fclose(start);

    if (!(stop  = fopen(".depend.stop",  "w"))) {
	warn("fopen(.depend.stop): %s\n", strerror(errno));
	return;
    }
    info("creating .depend.stop\n");

    name = NULL;
    fprintf(stop, "TARGETS =");
    while (listscripts(&name, LVL_NORM))	/* LVL_NORM: nearly all but not BOOT and not SINGLE */
	fprintf(stop, " %s", name);
    putc('\n', stop);

    list_for_each(srv, serv_start) {
	serv_t * cur = getserv(srv);
	serv_t * chk;
	list_t * pos;
	char pr = 1;

	if (!cur || list_empty(&(cur->sort.rev)))
	    continue;

	if (cur->lvls & LVL_BOOT)
	    continue;

	if ((name = getscript(cur->name)) == NULL)
	    name = cur->name;

	if ((chk = findserv(name)) && (cur != chk))
	    continue;				/* Duplet */

	list_for_each(pos, &(cur->sort.rev)) {
	    req_t  * rev = getrev(pos);
	    serv_t * dep = findserv(rev->serv);

	    if (dep && (dep->lvls & LVL_BOOT))
		continue;

	    if (pr == 1) {
		fprintf(stop, "%s:", name);
		pr++;
	    }

	    if (!dep) continue;

	    if ((dep->opts & SERV_DUPLET) && dep->main)
		dep = dep->main;		/* Duplet */

	    if ((name = getscript(rev->serv)) == NULL)
		name = rev->serv;

	    fprintf(stop, " %s", name);
	}
	if (pr > 1)
	    putc('\n', stop);
    }

    fclose(stop);
}

/*
 * Internal logger
 */
char *myname = NULL;
static void _logger (const char *const fmt, va_list ap)
{
    char buf[strlen(myname)+2+strlen(fmt)+1];
    strcat(strcat(strcpy(buf, myname), ": "), fmt);
    vfprintf(stderr, buf, ap);
    return;
}

/*
 * Cry and exit.
 */
void error (const char *const fmt, ...)
{
    static char called;
    if (called++)
	exit (1);
    va_list ap;
    va_start(ap, fmt);
    _logger(fmt, ap);
    va_end(ap);
    popd();
    exit (1);
}

/*
 * Warn the user.
 */
void warn (const char *const fmt, ...)
{
    va_list ap;
    va_start(ap, fmt);
    _logger(fmt, ap);
    va_end(ap);
    return;
}

/*
 * Print message when verbose is enabled
 */
void info(const char *fmt, ...) {
    va_list ap;
    if (!verbose)
	goto out;
    va_start(ap, fmt);
    _logger(fmt, ap);
    va_end(ap);
out:
    return;
}

/*
 * Open a runlevel directory, if it not
 * exists than create one.
 */
static DIR * openrcdir(const char *const  rcpath)
{
   DIR * rcdir;
   struct stat st;

    if (stat(rcpath, &st) < 0) {
	if (errno == ENOENT) {
	    info("creating directory '%s'\n", rcpath);
	    if (!dryrun)
		mkdir(rcpath, (S_IRWXU|S_IRGRP|S_IXGRP|S_IROTH|S_IXOTH));
	} else
	    error("can not stat(%s): %s\n", rcpath, strerror(errno));
    }

    if ((rcdir = opendir(rcpath)) == NULL) {
	if (dryrun)
	    warn ("can not opendir(%s): %s\n", rcpath, strerror(errno));
	else
	    error("can not opendir(%s): %s\n", rcpath, strerror(errno));
    }

    return rcdir;
}

/*
 * Wrapper for regcomp(3)
 */
static inline void regcompiler (regex_t *preg, const char *regex, int cflags)
{
    register int ret = regcomp(preg, regex, cflags);
    if (ret) {
	regerror(ret, preg, buf, sizeof (buf));
	regfree (preg);
	error("%s\n", buf);
    }
    return;
}

/*
 * Wrapper for regexec(3)
 */
static inline boolean regexecutor (regex_t *preg, const char *string,
			size_t nmatch, regmatch_t pmatch[], int eflags)
{
    register int ret = regexec(preg, string, nmatch, pmatch, eflags);
    if (ret > REG_NOMATCH) {
	regerror(ret, preg, buf, sizeof (buf));
	regfree (preg);
	error("%s\n", buf);
    }
    return (ret ? false : true);
}

/*
 * The script scanning engine.
 * We have to alloc the regular expressions first before
 * calling scan_script_defaults().  After the last call
 * of scan_script_defaults() we may free the expressions.
 */
static inline void scan_script_regalloc()
{
    regcompiler(&reg.prov,      PROVIDES,       REG_EXTENDED|REG_ICASE);
    regcompiler(&reg.req_start, REQUIRED_START, REG_EXTENDED|REG_ICASE|REG_NEWLINE);
    regcompiler(&reg.req_stop,  REQUIRED_STOP,  REG_EXTENDED|REG_ICASE|REG_NEWLINE);
    regcompiler(&reg.shl_start, SHOULD_START,   REG_EXTENDED|REG_ICASE|REG_NEWLINE);
    regcompiler(&reg.shl_stop,  SHOULD_STOP,    REG_EXTENDED|REG_ICASE|REG_NEWLINE);
    regcompiler(&reg.def_start, DEFAULT_START,  REG_EXTENDED|REG_ICASE|REG_NEWLINE);
    regcompiler(&reg.def_stop,  DEFAULT_STOP,   REG_EXTENDED|REG_ICASE|REG_NEWLINE);
    regcompiler(&reg.desc,      DESCRIPTION,    REG_EXTENDED|REG_ICASE|REG_NEWLINE);
}

static boolean scan_script_defaults(const char *const path)
{
    regmatch_t subloc[SUBNUM_SHD+1], *val = &subloc[SUBNUM-1], *shl = &subloc[SUBNUM_SHD-1];
    FILE *script;
    char *pbuf = buf;
    char *begin = NULL, *end = NULL;
    boolean ret = false;

#define provides	script_inf.provides
#define required_start	script_inf.required_start
#define required_stop	script_inf.required_stop
#define should_start	script_inf.should_start
#define should_stop	script_inf.should_stop
#define default_start	script_inf.default_start
#define default_stop	script_inf.default_stop
#define description	script_inf.description

    info("Loading %s\n", path);
    script = fopen(path, "r");
    if (!script)
	error("fopen(%s): %s\n", path, strerror(errno));

    /* Reset old results */
    xreset(provides);
    xreset(required_start);
    xreset(required_stop);
    xreset(should_start);
    xreset(should_stop);
    xreset(default_start);
    xreset(default_stop);
    xreset(description);

#define COMMON_ARGS	buf, SUBNUM, subloc, 0
#define COMMON_SHD_ARGS	buf, SUBNUM_SHD, subloc, 0
    while (fgets(buf, sizeof(buf), script)) {

	/* Skip scanning above from LSB magic start */
	if (!begin && !(begin = strstr(buf, "### BEGIN INIT INFO")))
	    continue;

	if (!provides       && regexecutor(&reg.prov,      COMMON_ARGS) == true) {
	    if (val->rm_so < val->rm_eo) {
		*(pbuf+val->rm_eo) = '\0';
	        provides = xstrdup(pbuf+val->rm_so);
	    } else
		provides = empty;
	}
	if (!required_start && regexecutor(&reg.req_start, COMMON_ARGS) == true) {
	    if (val->rm_so < val->rm_eo) {
		*(pbuf+val->rm_eo) = '\0';
		required_start = xstrdup(pbuf+val->rm_so);
	    } else
		required_start = empty;
	}
#ifndef SUSE
	if (!required_stop  && regexecutor(&reg.req_stop,  COMMON_ARGS) == true) {
	    if (val->rm_so < val->rm_eo) {
		*(pbuf+val->rm_eo) = '\0';
		required_stop = xstrdup(pbuf+val->rm_so);
	    } else
		required_stop = empty;
	}
#endif /* not SUSE */
	if (!should_start && regexecutor(&reg.shl_start,   COMMON_SHD_ARGS) == true) {
	    if (shl->rm_so < shl->rm_eo) {
		*(pbuf+shl->rm_eo) = '\0';
		should_start = xstrdup(pbuf+shl->rm_so);
	    } else
		should_start = empty;
	}
#ifndef SUSE
	if (!should_stop  && regexecutor(&reg.shl_stop,    COMMON_SHD_ARGS) == true) {
	    if (shl->rm_so < shl->rm_eo) {
		*(pbuf+shl->rm_eo) = '\0';
		should_stop = xstrdup(pbuf+shl->rm_so);
	    } else
		should_stop = empty;
	}
#endif /* not SUSE */
	if (!default_start  && regexecutor(&reg.def_start, COMMON_ARGS) == true) {
	    if (val->rm_so < val->rm_eo) {
		*(pbuf+val->rm_eo) = '\0';
		default_start = xstrdup(pbuf+val->rm_so);
	    } else
		default_start = empty;
	}
#ifndef SUSE
	if (!default_stop   && regexecutor(&reg.def_stop,  COMMON_ARGS) == true) {
	    if (val->rm_so < val->rm_eo) {
		*(pbuf+val->rm_eo) = '\0';
		default_stop = xstrdup(pbuf+val->rm_so);
	    } else
		default_stop = empty;
	}
#endif /* not SUSE */
	if (!description    && regexecutor(&reg.desc,      COMMON_ARGS) == true) {
	    if (val->rm_so < val->rm_eo) {
		*(pbuf+val->rm_eo) = '\0';
		description = xstrdup(pbuf+val->rm_so);
	    } else
		description = empty;
	}

	/* Skip scanning below from LSB magic end */
	if ((end = strstr(buf, "### END INIT INFO")))
	    break;
    }
#undef COMMON_ARGS
#undef COMMON_SHD_ARGS

    fclose(script);
    ret = begin && end;

    if (begin && !end) {
	char *name = basename(path);
	if (*name == 'S' || *name == 'K')
	    name += 3;
	warn("script %s is broken: missing end of LSB comment.\n", name);
	error("exiting now!\n");
    }

#ifdef SUSE
    if (verbose && (begin && end && (!provides || !required_start)))
#else
    if (verbose && (begin && end && (!provides || !required_start || !required_stop)))
#endif
    {
	char *name = basename(path);
	if (*name == 'S' || *name == 'K')
	    name += 3;
	warn("script %s could be broken: incomplete LSB comment.\n", name);
	if (!provides)
	    warn("Missing entry for Provides: please add even if empty.\n", name);
	if (!required_start)
	    warn("Missing entry for Required-Start: please add even if empty.\n", name);
#ifndef SUSE
	if (!required_stop)
	    warn("Missing entry for Required-Stop: please add even if empty.\n", name);
#endif
    }

#undef provides
#undef required_start
#undef required_stop
#undef should_start
#undef should_stop
#undef default_start
#undef default_stop
#undef description

    return ret;
}

static inline void scan_script_regfree()
{
    regfree(&reg.prov);
    regfree(&reg.req_start);
    regfree(&reg.req_stop);
    regfree(&reg.shl_start);
    regfree(&reg.shl_stop);
    regfree(&reg.def_start);
    regfree(&reg.def_stop);
    regfree(&reg.desc);
}

static struct {
    char *location;
    const int lvl;
    const int seek;
} runlevel_locations[] = {
#ifdef SUSE	/* SuSE's SystemV link scheme */
    {"rc0.d/",    LVL_HALT,   LVL_NORM},
    {"rc1.d/",    LVL_ONE,    LVL_NORM},
    {"rc2.d/",    LVL_TWO,    LVL_NORM},
    {"rc3.d/",    LVL_THREE,  LVL_NORM},
    {"rc4.d/",    LVL_FOUR,   LVL_NORM},
    {"rc5.d/",    LVL_FIVE,   LVL_NORM},
    {"rc6.d/",    LVL_REBOOT, LVL_NORM},
    {"rcS.d/",    LVL_SINGLE, LVL_NORM}, /* runlevel S */
    {"boot.d/",   LVL_BOOT,   LVL_BOOT}, /* runlevel B */
#else		/* not SUSE (actually, Debian) */
    {"../rc0.d/", LVL_HALT,   LVL_NORM},
    {"../rc1.d/", LVL_SINGLE, LVL_NORM},
    {"../rc2.d/", LVL_TWO,    LVL_NORM},
    {"../rc3.d/", LVL_THREE,  LVL_NORM},
    {"../rc4.d/", LVL_FOUR,   LVL_NORM},
    {"../rc5.d/", LVL_FIVE,   LVL_NORM},
    {"../rc6.d/", LVL_REBOOT, LVL_NORM},
    {"../rcS.d/", LVL_BOOT,   LVL_BOOT}, /* runlevel S */
		/* On e.g. Debian there exist no boot.d */
#endif		/* not SUSE */
};

#define RUNLEVLES (sizeof(runlevel_locations)/sizeof(runlevel_locations[0]))

static char *map_runlevel_to_location(const int runlevel)
{
    return runlevel_locations[runlevel].location;
}

static const int map_runlevel_to_lvl(const int runlevel)
{
    return runlevel_locations[runlevel].lvl;
}

static const int map_runlevel_to_seek(const int runlevel)
{
    return runlevel_locations[runlevel].seek;
}

/*
 * Scan current service structure
 */
static void scan_script_locations(const char *const path)
{
    int runlevel;

    pushd(path);
    for (runlevel = 0; runlevel < RUNLEVLES; runlevel++) {
	char * rcd = NULL;
	DIR  * rcdir;
	struct dirent *d;
	char * token;
	struct stat st_script;

	rcd = map_runlevel_to_location(runlevel);
	rcdir = openrcdir(rcd); /* Creates runlevel directory if necessary */
	if (rcdir == NULL)
	    break;
	pushd(rcd);
	while ((d = readdir(rcdir)) != NULL) {
	    char * ptr = d->d_name;
	    char order = 0;
	    char* begin = (char*)NULL; /* Remember address of ptr handled by strsep() */
	    boolean lsb;

	    if (*ptr != 'S')
		continue;
	    ptr++;

	    if (strspn(ptr, "0123456789") < 2)
		continue;
	    order = atoi(ptr);
	    ptr += 2;

	    if (stat(d->d_name, &st_script) < 0) {
		xremove(d->d_name);	/* dangling sym link */
		continue;
	    }

	    lsb = scan_script_defaults(d->d_name);
	    if (!script_inf.provides || script_inf.provides == empty)
		script_inf.provides = xstrdup(ptr);

	    begin = script_inf.provides;
	    while ((token = strsep(&script_inf.provides, delimeter)) && *token) {
		serv_t * service = NULL;
		if (*token == '$') {
		    warn("script %s provides system facility %s, skipped!\n", d->d_name, token);
		    continue;
		}
		service = current_structure(token, order, runlevel);

		if (service->opts & SERV_KNOWN)
		    continue;
		service->opts |= (SERV_KNOWN|SERV_ENABLED);

		if (!lsb)
		    service->opts |= SERV_NOTLSB;
		if (script_inf.required_start && script_inf.required_start != empty) {
		    rememberreq(service, REQ_MUST, script_inf.required_start);
		    requiresv(token, script_inf.required_start);
		}
		if (script_inf.should_start && script_inf.should_start != empty) {
		    rememberreq(service, REQ_SHLD, script_inf.should_start);
		    requiresv(token, script_inf.should_start);
		}
#ifndef SUSE
		/*
		 * required_stop and should_stop arn't used in SuSE Linux.
		 * Note: Sorting is done symetrical in stop and start!
		 * The stop_order is given by max_order + 1 - start_order.
		 */
		if (script_inf.required_stop && script_inf.required_stop != empty) {
		    rememberreq(service, REQ_MUST, script_inf.required_stop);
		    requiresv(token, script_inf.required_stop);
		}
		if (script_inf.should_stop && script_inf.should_stop != empty) {
		    rememberreq(service, REQ_SHLD, script_inf.should_stop);
		    requiresv(token, script_inf.should_stop);
		}
#endif /* not SUSE */
	    }
	    script_inf.provides = begin;

	    xreset(script_inf.provides);
	    xreset(script_inf.required_start);
	    xreset(script_inf.required_stop);
	    xreset(script_inf.should_start);
	    xreset(script_inf.should_stop);
	    xreset(script_inf.default_start);
	    xreset(script_inf.default_stop);
	    xreset(script_inf.description);
	}
	popd();
	closedir(rcdir);
    }
    popd();
    return;
}

/*
 * The /etc/insserv.conf scanning engine.
 */
static void scan_conf_file(const char* file)
{
    regex_t reg_conf, reg_conf2;
    regmatch_t subloc[SUBCONFNUM], *val = NULL;
    FILE *conf;
    char *pbuf = buf;

    regcompiler(&reg_conf,  CONFLINE,  REG_EXTENDED|REG_ICASE);
    regcompiler(&reg_conf2, CONFLINE2, REG_EXTENDED|REG_ICASE);

    info("Loading %s\n", file);

    do {
	const char * fptr = file;
	if (*fptr == '/')
	    fptr++;
	/* Try relativ location first */
	if ((conf = fopen(fptr, "r")))
	    break;
	/* Try absolute location */
	if ((conf = fopen(file, "r")))
	    break;
	goto err;
    } while (1);

    while (fgets(buf, sizeof(buf), conf)) {
	if (*pbuf == '#')
	    continue;
	if (regexecutor(&reg_conf, buf, SUBCONFNUM, subloc, 0) == true) {
	    char * virt = NULL, * real = NULL;
	    val = &subloc[SUBCONF - 1];
	    if (val->rm_so < val->rm_eo) {
		*(pbuf+val->rm_eo) = '\0';
		virt = pbuf+val->rm_so;
	    }
	    val = &subloc[SUBCONFNUM - 1];
	    if (val->rm_so < val->rm_eo) {
		*(pbuf+val->rm_eo) = '\0';
		real = pbuf+val->rm_so;
	    }
	    if (virt) {
		list_t * ptr;
		boolean found = false;
		list_for_each(ptr, sysfaci_start) {
		    if (!strcmp(getfaci(ptr)->name, virt)) {
			found = true;
			if(real)
			{
			    char* repl = getfaci(ptr)->repl;
			    repl = realloc(repl, strlen(repl)+strlen(real)+2);
			    strcat(repl, " ");
			    strcat(repl, real);
			    getfaci(ptr)->repl = repl;
			}
			break;
		    }
		}
		if (!found) {
		    faci_t * this = (faci_t *)malloc(sizeof(faci_t));
		    if (!this)
			error("%s", strerror(errno));
		    insert(&(this->list), sysfaci_start->prev);
		    this->name = xstrdup(virt);
		    this->repl = xstrdup(real);
		}
	    }
	}
	if (regexecutor(&reg_conf2, buf, SUBCONFNUM, subloc, 0) == true) {
	    char * key = NULL, * servs = NULL;
	    val = &subloc[SUBCONF - 1];
	    if (val->rm_so < val->rm_eo) {
		*(pbuf+val->rm_eo) = '\0';
		key = pbuf+val->rm_so;
	    }
	    val = &subloc[SUBCONFNUM - 1];
	    if (val->rm_so < val->rm_eo) {
		*(pbuf+val->rm_eo) = '\0';
		servs = pbuf+val->rm_so;
	    }
	    if (key && *key == '<' && servs && *servs) {
		if (!strncmp("<interactive>", key, strlen(key))) {
		    char * token;
		    while ((token = strsep(&servs, delimeter))) {
			serv_t *service = addserv(token);
			service->opts |= SERV_ACTIVE;
		    }
		}
	    }
	}
    }
    regfree(&reg_conf);
    regfree(&reg_conf2);
    fclose(conf);
    return;
err:
    warn("fopen(%s): %s\n", file, strerror(errno));
}

static int cfgfile_filter(const struct dirent* d)
{
    const char* end;
    if ((end = strrchr(d->d_name, '.'))) {
	end++;
	if (!strcmp(end,  "local")	||
	    !strncmp(end, "rpm", 3)	|| /* .rpmorig, .rpmnew, .rmpsave, ... */
	    !strncmp(end, "ba", 2)	|| /* .bak, .backup, ... */
	    !strcmp(end,  "old")	||
	    !strcmp(end,  "new")	||
	    !strncmp(end, "dpkg", 3)	|| /* .dpkg-old, .dpkg-new ... */
	    !strcmp(end,  "save")	||
	    !strcmp(end,  "swp")	|| /* Used by vi like editors */
	    !strcmp(end,  "core"))	   /* modern core dump */
	{
	    return 0;
	}
    }
    return 1;
}

static void scan_conf()
{
    struct dirent** namelist = NULL;
    const char dir[] = INSCONF ".d";
    char buf[PATH_MAX];
    int n;

    scan_conf_file(INSCONF);

    n = scandir(dir, &namelist, cfgfile_filter, alphasort);
    if(n > 0)
    {
	while(n--)
	{
	    snprintf(buf, sizeof(buf), "%s/%s", dir, namelist[n]->d_name);
	    scan_conf_file(buf);
	}
    }

    free(namelist);
}

/*
 * Expand the system facilitis after all scripts have been scanned.
 */
static void expand_conf()
{
    list_t * ptr;
    list_for_each(ptr, sysfaci_start)
	virtprov(getfaci(ptr)->name, getfaci(ptr)->repl);
}

/*
 * Scan for a Start or Kill script within a runlevel directory.
 * We start were we leave the directory, the upper level
 * has to call rewinddir(3) if necessary.
 */
static inline char *  scan_for(DIR *const rcdir, const char *const script, char type)
{
    struct dirent *d;
    char * ret = NULL;

    while ((d = readdir(rcdir)) != NULL) {
	char * ptr = d->d_name;

	if (*ptr != type)
	    continue;
	ptr++;

	if (strspn(ptr, "0123456789") < 2)
	    continue;
	ptr += 2;

	if (!strcmp(ptr, script)) {
	    ret = d->d_name;
	    break;
	}
    }
    return ret;
}

/*
 *  Check for script in list.
 */
static int curr_argc = -1;
static inline boolean chkfor(const char *const script, char ** const list, const int cnt)
{
    boolean isinc = false;
    register int c = cnt;

    curr_argc = -1;
    while (c--) {
	if (!strcmp(script, list[c])) {
	    isinc = true;
	    curr_argc = c;
	    break;
	}
    }
    return isinc;
}

static struct option long_options[] =
{
    {"verbose",	0, NULL, 'v'},
    {"dryrun",	0, NULL, 'n'},
    {"default",	0, NULL, 'd'},
    {"remove",	0, NULL, 'r'},
    {"force",	0, NULL, 'f'},
    {"help",	0, NULL, 'h'},
    { 0,	0, NULL,  0 },
};

static void help(const char *const  name)
{
    printf("Usage: %s [<options>] [init_script|init_directory]\n", name);
    printf("Available options:\n");
    printf("  -h, --help       This help.\n");
    printf("  -r, --remove     Remove the listed scripts from all runlevels.\n");
    printf("  -f, --force      Ignore if a required service is missed.\n");
    printf("  -v, --verbose    Provide information on what is being done.\n");
    printf("  -n, --dryrun     Do not change the system, only talk about it.\n");
    printf("  -d, --default    Use default runlevels a defined in the scripts\n");
}


/*
 * Do the job.
 */
int main (int argc, char *argv[])
{
    DIR * initdir;
    struct dirent *d;
    struct stat st_script;
    char * argr[argc];
    char * path = INITDIR;
    int runlevel, c;
    boolean del = false;
    boolean defaults = false;
    boolean ignore = false;

    myname = basename(*argv);

    for (c = 0; c < argc; c++)
	argr[c] = NULL;

    while ((c = getopt_long(argc, argv, "dfrhvn", long_options, NULL)) != -1) {
	switch (c) {
	    case 'd':
		defaults = true;
		break;
	    case 'r':
		del = true;
		break;
	    case 'f':
		ignore = true;
		break;
	    case 'v':
		verbose = true;
		break;
	    case 'n':
		verbose = true;
		dryrun = true;
		break;
	    case '?':
		error("For help use: %s -h\n", myname);
	    case 'h':
		help(myname);
		exit(0);
	    default:
		break;
	}
    }
    argv += optind;
    argc -= optind;

    if (!argc && del)
	error("usage: %s [[-r] init_script|init_directory]\n", myname);

    if (*argv) {
	char * token = strpbrk(*argv, delimeter);

	/*
	 * Let us separate the script/service name from the additional arguments.
	 */
	if (token && *token) {
	    *token = '\0';
	    *argr = ++token;
	}

	/* Catch `/path/script', `./script', and `path/script' */
	if (strchr(*argv, '/')) {
	    if ( stat(*argv, &st_script) < 0)
		error("%s: %s\n", *argv, strerror(errno));
	} else {
	    pushd(path);
	    if (stat(*argv, &st_script) < 0)
		error("%s: %s\n", *argv, strerror(errno));
	    popd();
	}

	if (S_ISDIR(st_script.st_mode)) {
	    path = *argv;
	    if (del)
		error("usage: %s [[-r] init_script|init_directory]\n", myname);
	    argv++;
	    argc--;
	    if (argc)
		error("usage: %s [[-r] init_script|init_directory]\n", myname);
	} else {
	    char * base, * ptr = xstrdup(*argv);

	    if ((base = strrchr(ptr, '/'))) {
		*(++base) = '\0';
		path = ptr;
	    } else
		free(ptr);
	}
    }

    c = argc;
    while (c--) {
	char * base;
	char * token = strpbrk(argv[c], delimeter);

	/*
	 * Let us separate the script/service name from the additional arguments.
	 */
	if (token && *token) {
	    *token = '\0';
	    argr[c] = ++token;
	}

	if (stat(argv[c], &st_script) < 0) {
	    if (errno != ENOENT)
		error("%s: %s\n", argv[c], strerror(errno));
	    pushd(path);
	    if (stat(argv[c], &st_script) < 0)
		error("%s: %s\n", argv[c], strerror(errno));
	    popd();
	}
	if ((base = strrchr(argv[c], '/'))) {
	    base++;
	    argv[c] = base;
	}
    }

#if defined(DEBUG) && (DEBUG > 0)
    for (c = 0; c < argc; c++)
	if (argr[c])
	    printf("Overwrite argument for %s is %s\n", argv[c], argr[c]);
#endif

    /*
     * Scan and set our configuration for virtual services.
     */
    scan_conf();

    /*
     * Initialize the regular scanner for the scripts.
     */
    scan_script_regalloc();

    /*
     * Scan always for the runlevel links to see the current
     * link scheme of the services.
     */
#if 0
    if (!defaults)
#endif
    scan_script_locations(path);

    if ((initdir = opendir(path)) == NULL)
	error("can not opendir(%s): %s\n", path, strerror(errno));
    /*
     * Now scan for the service scripts and their LSB comments.
     */
    pushd(path);
    while ((d = readdir(initdir)) != NULL) {
	serv_t * service = NULL;
	char * token;
	char* begin = (char*)NULL;  /* Remember address of ptr handled by strsep() */
	boolean lsb = false;
	errno = 0;

	/* d_type seems not to work, therefore use stat(2) */
	if (stat(d->d_name, &st_script) < 0) {
	    warn("can not stat(%s)\n", d->d_name);
	    continue;
	}
	if (!S_ISREG(st_script.st_mode) ||
	    !(S_IXUSR & st_script.st_mode))
	{
	    if (chkfor(d->d_name, argv, argc))
		warn("script %s is not executable, skipped!\n", d->d_name);
	    continue;
	}

	if (!strncmp(d->d_name, "README", strlen("README"))) {
	    if (chkfor(d->d_name, argv, argc))
		warn("script name %s is not valid, skipped!\n", d->d_name);
	    continue;
	}

	if (!strncmp(d->d_name, "Makefile", strlen("Makefile"))) {
	    if (chkfor(d->d_name, argv, argc))
		warn("script name %s is not valid, skipped!\n", d->d_name);
	    continue;
	}

	if (!strncmp(d->d_name, "core", strlen("core"))) {
	    if (chkfor(d->d_name, argv, argc))
		warn("script name %s is not valid, skipped!\n", d->d_name);
	    continue;
	}

	/* Common scripts not used within runlevels */
	if (!strcmp(d->d_name, "rx")	   ||
	    !strcmp(d->d_name, "skeleton") ||
	    !strcmp(d->d_name, "powerfail"))
	{
	    if (chkfor(d->d_name, argv, argc))
		warn("script name %s is not valid, skipped!\n", d->d_name);
	    continue;
	}

#ifdef SUSE
	if (!strcmp(d->d_name, "boot") || !strcmp(d->d_name, "rc"))
#else  /* not SUSE */
	if (!strcmp(d->d_name, "rcS") || !strcmp(d->d_name, "rc"))
#endif /* not SUSE */
	{
	    if (chkfor(d->d_name, argv, argc))
		warn("script name %s is not valid, skipped!\n", d->d_name);
	    continue;
	}

	if (cfgfile_filter(d) == 0) {
	    if (chkfor(d->d_name, argv, argc))
		warn("script name %s is not valid, skipped!\n", d->d_name);
	    continue;
	}

	/* Leaved by emacs like editors */
	if (d->d_name[strlen(d->d_name)-1] == '~') {
	    if (chkfor(d->d_name, argv, argc))
		warn("script name %s is not valid, skipped!\n", d->d_name);
	    continue;
	}

	if (strspn(d->d_name, "$.#%_+-\\*[]^:()~")) {
	    if (chkfor(d->d_name, argv, argc))
		warn("script name %s is not valid, skipped!\n", d->d_name);
	    continue;
	}

	/* main scanner for LSB comment in current script */
	lsb = scan_script_defaults(d->d_name);

	/* Common script ... */
	if (!strcmp(d->d_name, "halt")) {
	    makeprov("halt",   d->d_name);
	    runlevels("halt",   "0");
	    addserv("halt");
	    continue;
	}

	/* ... and its link */
	if (!strcmp(d->d_name, "reboot")) {
	    makeprov("reboot", d->d_name);
	    runlevels("reboot", "6");
	    addserv("reboot");
	    continue;
	}

	/* Common script for single mode */
	if (!strcmp(d->d_name, "single")) {
	    serv_t *serv = addserv("single");
	    makeprov("single", d->d_name);
	    runlevels("single", "1 S");
	    requiresv("single", "kbd");
	    serv->opts |= SERV_ALL;
	    rememberreq(serv, REQ_SHLD, "kbd");
	    continue;
	}

	/*
	 * Oops, no comment found, guess one
	 */
	if (!script_inf.provides || script_inf.provides == empty) {
	    serv_t *guess;
	    script_inf.provides = xstrdup(d->d_name);

	    /*
	     * Use guessed service to find it within the the runlevels
	     * (by using the list from the first scan for script locations).
	     */
	    if ((guess = findserv(script_inf.provides))) {
		/*
		 * Try to guess required services out from current scheme.
		 * Note, this means that all services are required.
		 */
		if (!script_inf.required_start || script_inf.required_start == empty) {
		    list_t * ptr = NULL;

		    list_for_each_prev(ptr, serv_start) {
			if (getserv(ptr)->order >= guess->order)
			    continue;
			if (getserv(ptr)->lvls & guess->lvls) {
			    script_inf.required_start = xstrdup(getserv(ptr)->name);
			    break;
			}
		    }
		}
		if (!script_inf.default_start || script_inf.default_start == empty) {
		    if (guess->lvls)
			script_inf.default_start = xstrdup(lvl2str(guess->lvls));
		}
	    } else {
		/*
		 * Find out which levels this service may have out from current scheme.
		 * Note, this means that the first requiring service wins.
		 */
		if (!script_inf.default_start || script_inf.default_start == empty) {
		    list_t * ptr;

		    list_for_each(ptr, serv_start) {
			serv_t * cur = getserv(ptr);
			list_t * req;

			if (script_inf.default_start && script_inf.default_start != empty)
			   break;

			if (!cur || list_empty(&(cur->sort.req)) || !(cur->opts & SERV_ENABLED))
			    continue;

			list_for_each(req, &(cur->sort.req)) {
			    if (!strcmp(getreq(req)->serv, script_inf.provides)) {
				script_inf.default_start = xstrdup(lvl2str(getserv(ptr)->lvls));
				break;
			    }
			}
		    }
		}
	    } /* !(guess = findserv(script_inf.provides)) */
	}

	/*
	 * Use guessed service to find it within the the runlevels
	 * (by using the list from the first scan for script locations).
	 */
	if (!service) {
	    int count = 0;
	    char * provides = xstrdup(script_inf.provides);

	    begin = provides;
	    while ((token = strsep(&provides, delimeter)) && *token) {

		if (*token == '$') {
		    warn("script %s provides system facility %s, skipped!\n", d->d_name, token);
		    continue;
		}

		if (makeprov(token, d->d_name) < 0) {
		    boolean isarg = chkfor(d->d_name, argv, argc);

		    if (!del || (del && !isarg))
			warn("script %s: service %s already provided!\n", d->d_name, token);

		    if (!del && !ignore && isarg)
			error("exiting now!\n");

		    if (!del || (del && !ignore && !isarg))
			continue;

		    /* Provide this service with an other name to be able to delete it */ 
		    makeprov(d->d_name, d->d_name);
		    service = addserv(d->d_name);
		    service->opts |= SERV_DOUBLE;

		    continue;
	    	}

		if (!(service = findserv(token)))
		    service = addserv(token);
		count++;					/* Count token */

		if (service) {
		    boolean known = (service->opts & SERV_KNOWN);
		    service->opts |= SERV_KNOWN;

		    if (!provides && (count > 1)) {		/* Last token */ 
			const char * script = getscript(service->name);

			if (script) {
			    list_t * srv;

			    list_for_each(srv, serv_start) {
				serv_t * cur = getserv(srv);
				const char * chk;

				if (!cur || !(chk = getscript(cur->name)))
				    continue;

				if (!strcmp(chk, script) && (service != cur)) {
				    cur->opts |= SERV_DUPLET; 
				    cur->main = service;	/* Remember main service */
				}
			    }
			}
		    }

		    if (!known && script_inf.required_start && script_inf.required_start != empty) {
			rememberreq(service, REQ_MUST, script_inf.required_start);
			requiresv(token, script_inf.required_start);
		    }
		    if (!known && script_inf.should_start && script_inf.should_start != empty) {
			rememberreq(service, REQ_SHLD, script_inf.should_start);
			requiresv(token, script_inf.should_start);
		    }
#ifndef SUSE
		    /*
		     * required_stop and should_stop arn't used in SuSE Linux.
		     * Note: Sorting is done symetrical in stop and start!
		     * The stop order is given by max order - start order.
		     */
		    if (!known && script_inf.required_stop && script_inf.required_stop != empty) {
			rememberreq(service, REQ_MUST, script_inf.required_stop);
			requiresv(token, script_inf.required_stop);
		    }
		    if (!known && script_inf.should_stop && script_inf.should_stop != empty) {
			rememberreq(service, REQ_SHLD, script_inf.should_stop);
			requiresv(token, script_inf.should_stop);
		    }
#endif /* not SUSE */
		    /*
		     * Use information from symbolic link structure to
		     * check if all services are around for this script.
		     */
		    if (chkfor(d->d_name, argv, argc) && !ignore) {
			boolean ok = true;
			if (del)
			    ok = chkdependencies(token);
			else
			    ok = chkrequired(token);
			if (!ok)
			    error("exiting now!\n");
		    }

		    if (script_inf.default_start && script_inf.default_start != empty) {
		 	unsigned int deflvls = str2lvl(script_inf.default_start);

			/*
			 * Compare all bits, which means `==' and not `&' and overwrite
			 * the defaults of the current script.
			 */
			if (service->lvls) {
			    /*
			     * Currently linked into service runlevel scheme, check
			     * if the defaults are overwriten.
			     */
			    if (!defaults && (deflvls != service->lvls)) {
				if (!del && chkfor(d->d_name, argv, argc) && !(argr[curr_argc]))
				    warn("Warning, current runlevel(s) of script `%s' overwrites defaults.\n",
					 d->d_name);
			    }
			} else
			    /*
			     * Currently not linked into service runlevel scheme, info
			     * needed for enabling interactive services at first time.
			     */
			    service->lvls = deflvls;

		    } else {
			if (service->lvls)
			    /*
			     * Could be a none LSB script, use info from current link scheme.
			     */
			    script_inf.default_start = lvl2str(service->lvls);
			else
			    /*
			     * Ahh ... set default multiuser with network
			     */
			    script_inf.default_start = xstrdup("3 5");
		    }
#ifndef SUSE
		    /*
		     * default_stop arn't used in SuSE Linux.
		     */
		    if (script_inf.default_stop && script_inf.default_stop != empty) {
		 	unsigned int deflvlk = str2lvl(script_inf.default_stop);

			/*
			 * Compare all bits, which means `==' and not `&' and overwrite
			 * the defaults of the current script.
			 */
			if (service->lvlk) {
			    /*
			     * Currently linked into service runlevel scheme, check
			     * if the defaults are overwriten.
			     */
			    if (!defaults && (deflvlk != service->lvlk)) {
				if (!del && chkfor(d->d_name, argv, argc) && !(argr[curr_argc]))
				    warn("Warning, current runlevel(s) of script `%s' overwrites defaults.\n",
					 d->d_name);
			    }
			} else
			    /*
			     * Currently not linked into service runlevel scheme, info
			     * needed for enabling interactive services at first time.
			     */
			    service->lvlk = deflvlk;

		    } else {
			if (service->lvlk)
			    /*
			     * Could be a none LSB script, use info from current link scheme.
			     */
			    script_inf.default_stop = lvl2str(service->lvlk);
			/*
			 * Do _not_ set default stop levels
			 */
		    }
#endif /* not SUSE */
		}
	    }
	    free(begin);
	}

#ifdef SUSE
	/* Ahh ... set default multiuser with network */
	if (!script_inf.default_start || script_inf.default_start == empty)
	    script_inf.default_start = xstrdup("3 5");
#else  /* not SUSE */
	if (!script_inf.default_start || script_inf.default_start == empty)
	    script_inf.default_start = xstrdup("2 3 4 5");	/* for Debian*/
	if (!script_inf.default_stop  || script_inf.default_start == empty)
	    script_inf.default_stop  = xstrdup("S 0 1 6");	/* for Debian*/
#endif /* not SUSE */

	if (chkfor(d->d_name, argv, argc) && !defaults) {
	    if (argr[curr_argc]) {
		char * ptr = argr[curr_argc];
		struct _mark {
		    const char * wrd;
		    char * order;
		    char ** str;
		} mark[] = {
		    {"start=", NULL, &script_inf.default_start},
		    {"stop=",  NULL, &script_inf.default_stop },
		    {NULL, NULL, NULL}
		};

		for (c = 0; mark[c].wrd; c++) {
		    char * order = strstr(ptr, mark[c].wrd);
		    if (order)
			mark[c].order = order;
		}

		for (c = 0; mark[c].wrd; c++)
		    if (mark[c].order) {
			*(mark[c].order) = '\0';
			mark[c].order += strlen(mark[c].wrd);
		    }

		for (c = 0; mark[c].wrd; c++)
		    if (mark[c].order) {
			xreset(*(mark[c].str));
			*(mark[c].str) = xstrdup(mark[c].order);
		    }
	    }
	}

	begin = script_inf.provides;
	while ((token = strsep(&script_inf.provides, delimeter)) && *token) {
	    if (*token == '$')
		continue;

	    if (service && del)
		runlevels(token, lvl2str(service->lvls));
	    else
		runlevels(token, script_inf.default_start);
#ifndef SUSE
	    /*
	     * default_stop arn't used in SuSE Linux.
	     */
	    if (script_inf.default_stop && script_inf.default_stop != empty) {
		if (service && !del)
		    service->lvlk = str2lvl(script_inf.default_stop);
	    }
#endif /* not SUSE */
	}
	script_inf.provides = begin;

	/* Remember if not LSB conform script */
	if (!lsb && service)
	    service->opts |= SERV_NOTLSB;
    }
    /* Reset remaining pointers */
    xreset(script_inf.provides);
    xreset(script_inf.required_start);
    xreset(script_inf.required_stop);
    xreset(script_inf.should_start);
    xreset(script_inf.should_stop);
    xreset(script_inf.default_start);
    xreset(script_inf.default_stop);
    xreset(script_inf.description);

    /*
     * Free the regular scanner for the scripts.
     */
    scan_script_regfree();

    /* back */
    popd();
    closedir(initdir);

    expand_conf();

    /*
     *  Set initial order of some services
     */
    setorder("network",	 5, false); setlsb("network");
    setorder("inetd",	20, false); setlsb("inetd");
    setorder("halt",	20, false); setlsb("halt");
    setorder("reboot",	20, false); setlsb("reboot");
    setorder("single",	20, false); setlsb("single");
    setorder("serial",	10, false); setlsb("serial");
    setorder("gpm",	20, false); setlsb("gpm");
    setorder("boot.setup", 20, false);

    /*
     * Set virtual dependencies for already enabled none LSB scripts.
     */
    nonlsb_script();

    /*
     * Now generate for all scripts the dependencies
     */
    follow_all();

    /*
     * Re-order some well known scripts to get
     * a more stable order collection.
     * Stable means that new scripts should not
     * force a full re-order of all starting numbers.
     */
    setorder("route",	(getorder("network") + 2), true);
    setorder("single",	(getorder("kbd") + 2),	   true);

    /*
     * Be sure that interactive scripts are the only member of
     * a start group (for parallel start only).
     */
    active_script();

    /*
     * Move the `$all' scripts to the end of all
     */
    all_script();

    /*
     * Sorry but we support only [KS][0-9][0-9]<name>
     */
    if (maxorder > 99)
	error("Maximum of 99 in ordering reached\n");

#if defined(DEBUG) && (DEBUG > 0)
    printf("Maxorder %d\n", maxorder);
    show_all();
#else
# ifdef SUSE	/* SuSE's SystemV link scheme */
    pushd(path);
    for (runlevel = 0; runlevel < 9; runlevel++) {
	int order;
	const char * script;
	char nlink[PATH_MAX+1], olink[PATH_MAX+1];
	char * rcd = NULL;
	DIR  * rcdir;

	rcd = map_runlevel_to_location(runlevel);

	script = NULL;
	rcdir = openrcdir(rcd); /* Creates runlevel directory if necessary */
	if (rcdir == NULL)
	    break;
	pushd(rcd);

	/*
	 * See if we found scripts which should not be
	 * included within this runlevel directory.
	 */
	while ((d = readdir(rcdir)) != NULL) {
	    const char * ptr = d->d_name;
	    serv_t * serv = NULL;

	    if (*ptr != 'S' && *ptr != 'K')
		continue;
	    ptr++;

	    if (strspn(ptr, "0123456789") != 2)
		continue;
	    ptr += 2;

	    if (stat(d->d_name, &st_script) < 0)
		xremove(d->d_name);	/* dangling sym link */

	    if (defaults && notincluded(ptr, runlevel))
		xremove(d->d_name);

	    if (del && ignore && notincluded(ptr, runlevel)) {
		if ((serv = findserv(getprovides(ptr))) && (serv->opts & SERV_DOUBLE))
		    xremove(d->d_name);
	    }
	}

	/*
	 * Seek for scripts which are included, link or
	 * correct order number if necessary.
	 */

	while (foreach(&script, &order, runlevel)) {
	    const boolean this = chkfor(script, argv, argc);
	    boolean found, slink;
	    char * clink;

	    if (*script == '$')		/* Do not link in virtual dependencies */
		continue;

	    sprintf(olink, "../%s",   script);
	    sprintf(nlink, "S%.2d%s", order, script);

	    found = false;
	    rewinddir(rcdir);
	    while ((clink = scan_for(rcdir, script, 'S'))) {
		found = true;
		if (strcmp(clink, nlink)) {
		    xremove(clink);		/* Wrong order, remove link */
		    if (!this)
			xsymlink(olink, nlink);	/* Not ours, but correct order */
		    if (this && !del)
			xsymlink(olink, nlink);	/* Restore, with correct order */
		} else {
		    if (del && this)
			xremove(clink);		/* Found it, remove link */
		}
	    }

	    if (this) {
		/*
		 * If we haven't found it and we shouldn't delete it
		 * we try to add it.
		 */
		if (!del && !found) {
		    xsymlink(olink, nlink);
		    found = true;
		}
	    }

	    /* Start link done, now Kill link */

	    if (!strcmp(script, "kbd"))
		continue;  /* kbd should run on any runlevel change */

	    sprintf(nlink, "K%.2d%s", (maxorder + 1) - order, script);

	    slink = found;
	    found = false;
	    rewinddir(rcdir);
	    while ((clink = scan_for(rcdir, script, 'K'))) {
		found = true;
		if (strcmp(clink, nlink)) {
		    xremove(clink);		/* Wrong order, remove link */
		    if (!this)
			xsymlink(olink, nlink);	/* Not ours, but correct order */
		    if (this && !del)
			xsymlink(olink, nlink);	/* Restore, with correct order */
		} else {
		    if (del && this)
			xremove(clink);		/* Found it, remove link */
		}
	    }

	    /*
	     * One way runlevels:
	     * Remove kill links from rc0.d/, rc6.d/, and rcS.d/.
	     */
	    if (runlevel < 1 || runlevel == 6 || runlevel == 7) {
		if (found)
		    xremove(nlink);
	    } else {
		/*
		 * Restore kill links for boot.d/, should we do this for
		 * _all_ runlevels if we're not removing a service?
		 */
		if (this || runlevel > 7) {
		    /*
		     * If we haven't found it and we shouldn't delete it
		     * we try to add it.
		     */
		    if (!del && !found && slink)
			xsymlink(olink, nlink);
		}
	    }
	}

	popd();
	closedir(rcdir);
    }
# else  /* !SUSE, standard SystemV link scheme */
   /*
    * Remark: At SuSE we use boot scripts for system initialization which
    * will be executed by /etc/init.d/boot (which is equal to rc.sysinit).
    * At system reboot or system halt the stop links of those boot scripts
    * will be executed by /etc/init.d/halt.  Don't know how todo this for
    * a traditional standard SystemV link scheme.  Maybe for such an
    * approach a new directory halt.d/ whould be an idea.
    */
    pushd(path);
    for (runlevel = 0; runlevel < RUNLEVLES; runlevel++) {
	int lvl = 0, seek = 0;
	const char * script;
	char nlink[PATH_MAX+1], olink[PATH_MAX+1];
	char * rcd = NULL;
	DIR  * rcdir;

	rcd = map_runlevel_to_location(runlevel);
	lvl  = map_runlevel_to_lvl(runlevel);
	seek = map_runlevel_to_seek(runlevel);

	script = NULL;
	rcdir = openrcdir(rcd); /* Creates runlevel directory if necessary */
	if (rcdir == NULL)
	    break;
	pushd(rcd);

	/*
	 * See if we found scripts which should not be
	 * included within this runlevel directory.
	 */
	while ((d = readdir(rcdir)) != NULL) {
	    const char * ptr = d->d_name;
	    serv_t * serv;

	    if (*ptr != 'S' && *ptr != 'K')
		continue;
	    ptr++;

	    if (strspn(ptr, "0123456789") != 2)
		continue;
	    ptr += 2;
	    serv = findserv(getprovides(ptr));

	    if (stat(d->d_name, &st_script) < 0)
		xremove(d->d_name);	/* dangling sym link */

	    if (!serv) continue;

	    if (defaults && !(serv->opts & SERV_ENABLED))
		xremove(d->d_name);

	    if (del && ignore && !(serv->opts & SERV_ENABLED)) {
		if (serv->opts & SERV_DOUBLE)
		    xremove(d->d_name);
	    }
	}

	while (listscripts(&script, seek)) {
	    const boolean stop = notincluded(script, runlevel);
	    const boolean this = chkfor(script, argv, argc);
	    const serv_t *serv = findserv(getprovides(script));
	    const char mode = (stop ? 'K' : 'S');
	    int order = getorder(script);
	    boolean found;
	    char * clink;

	    if (*script == '$')		/* Do not link in virtual dependencies */
		continue;

	    if (!serv) continue;			/* Should not happen */

	    if (!(serv->opts & SERV_ENABLED) && !this)
		continue;

	    if (stop) {
#  ifdef USE_KILL_IN_SINGLE
		if (runlevel == 7)			/* No kill links in rcS.d */
			continue;
#  endif
		if ((serv->lvlk & lvl) == 0)		/* No default_stop provided */
			continue;
		order = (maxorder + 1) - order;
	    }

	    sprintf(olink, "../init.d/%s", script);
	    sprintf(nlink, "%c%.2d%s", mode, order, script);

	    found = false;
	    rewinddir(rcdir);
	    while ((clink = scan_for(rcdir, script, mode))) {
		found = true;
		if (strcmp(clink, nlink)) {
		    xremove(clink);		/* Wrong order, remove link */
		    if (!this)
			xsymlink(olink, nlink);	/* Not ours, but correct order */
		    if (this && !del)
			xsymlink(olink, nlink);	/* Restore, with correct order */
		} else {
		    if (del && this)
			xremove(clink);		/* Found it, remove link */
		}
	    }

	    if (this) {
		/*
		 * If we haven't found it and we shouldn't delete it
		 * we try to add it.
		 */
		if (!del && !found) {
		    xsymlink(olink, nlink);
		    found = true;
		}
	    }

	    /*
	     * Restore kill links for normal runlevels.
	     */
	    if (runlevel >= 0 && runlevel <= 6) {
		    if (!del && !found && (serv->opts & SERV_ENABLED))
			xsymlink(olink, nlink);
	    }
	}

	popd();
	closedir(rcdir);
    }
# endif /* !SUSE, standard SystemV link scheme */
#endif  /* !DEBUG */

    /*
     * Do the makedep
     */
    makedep();

    /*
     * Back to the root(s)
     */
    popd();

    return 0;
}
