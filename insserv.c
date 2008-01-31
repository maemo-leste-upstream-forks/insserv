/*
 * insserv(.c)
 *
 * Copyright 2000-2008 Werner Fink, 2000 SuSE GmbH Nuernberg, Germany,
 *				    2003 SuSE Linux AG, Germany.
 *				    2004 SuSE LINUX AG, Germany.
 *			       2005-2008 SUSE LINUX Products GmbH, Germany.
 * Copyright 2005,2008 Petter Reinholdtsen
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 */

#define MINIMAL_MAKE	1	/* Remove disabled scripts from .depend.boot,
				 * .depend.start and .depend.stop */
#define FACI_EXPANSION	0	/* Expand all system facilities before use
				   them in dependcies */

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
#include <sys/param.h>
#include <dirent.h>
#include <regex.h>
#include <errno.h>
#include <limits.h>
#include <getopt.h>
#include "listing.h"

static const char *map_runlevel_to_location(const int runlevel);
#ifndef SUSE
static int map_runlevel_to_seek(const int runlevel);
#endif /* not SUSE */

#ifdef SUSE
#define DEFAULT_START_LVL "3 5"
#undef  USE_STOP_TAGS
#undef  USE_KILL_IN_SINGLE
#else /* not SUSE, but Debian */
#define DEFAULT_START_LVL "2 3 4 5"
#define DEFAULT_STOP_LVL  "0 1 6"
#define DEFAULT_DEPENDENCY "$remote_fs $syslog"
#define USE_STOP_TAGS
#undef  USE_KILL_IN_SINGLE
#endif /* not SUSE, but Debian */

#ifndef  INITDIR
# define INITDIR	"/etc/init.d"
#endif
#ifndef  OVERRIDEDIR
# define OVERRIDEDIR	"/etc/insserv/overrides"
#endif
#ifndef  INSCONF
# define INSCONF	"/etc/insserv.conf"
#endif

/*
 * For a description of regular expressions see regex(7).
 */
#define COMM		"^#[[:blank:]]*"
#define VALUE		":[[:blank:]]*([[:print:]]*)"
/* The second substring contains our value (the first is all) */
#define SUBNUM		2
#define SUBNUM_SHD	3
#define START		"[-_]+start"
#define STOP		"[-_]+stop"

/* The main regular search expressions */
#define PROVIDES	COMM "provides" VALUE
#define REQUIRED	COMM "required"
#define SHOULD		COMM "(x[-_]+[a-z0-9_-]*)?should"
#define BEFORE		COMM "(x[-_]+[a-z0-9_-]*)?start[-_]+before"
#define AFTER		COMM "(x[-_]+[a-z0-9_-]*)?stop[-_]+after"
#define DEFAULT		COMM "default"
#define REQUIRED_START  REQUIRED START VALUE
#define REQUIRED_STOP	REQUIRED STOP  VALUE
#define SHOULD_START	SHOULD   START VALUE
#define SHOULD_STOP	SHOULD   STOP  VALUE
#define START_BEFORE	BEFORE   VALUE
#define STOP_AFTER	AFTER    VALUE
#define DEFAULT_START	DEFAULT  START VALUE
#define DEFAULT_STOP	DEFAULT  STOP  VALUE
#define DESCRIPTION	COMM "description" VALUE

/* System facility search within /etc/insserv.conf */
#define EQSIGN		"([[:blank:]]*[=:][[:blank:]]*|[[:blank:]]+)"
#define CONFLINE	"^(\\$[a-z0-9_-]+)" EQSIGN "([[:print:]]*)"
#define CONFLINE2	"^(<[a-z0-9_-]+>)"  EQSIGN "([[:print:]]*)"
#define SUBCONF		2
#define SUBCONFNUM	4

/* The root file system */
static char *root;

/* The main line buffer if unique */
static char buf[LINE_MAX];

/* When to be verbose */
static boolean verbose = false;

/* When to be verbose */
static boolean dryrun = false;

/* When paths set do not add root if any */
static boolean set_override = false;
static boolean set_insconf = false;

/* Search results points here */
typedef struct lsb_struct {
    char *provides;
    char *required_start;
    char *required_stop;
    char *should_start;
    char *should_stop;
    char *start_before;
    char *stop_after;
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
    regex_t start_bf;
    regex_t stop_af;
    regex_t def_start;
    regex_t def_stop;
    regex_t desc;
} reg_t;

typedef struct creg_struct {
    regex_t isysfaci;
    regex_t isactive;
} creg_t;

static lsb_t script_inf;
static reg_t reg;
static creg_t creg;
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

static void pushd(const char *const __restrict path);
static void pushd(const char *const path)
{
    pwd_t *  dir;

    dir = (pwd_t *)malloc(sizeof(pwd_t));
    if (dir) {
	if (!(dir->pwd = getcwd((char*)0, 0)))
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
    uint	 flags;
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
    uint	 opts;
    char	order;
    char       * name;
    serv_t     * main;
    uint	 lvls;
#ifdef USE_STOP_TAGS
    uint	 lvlk;
#endif /* USE_STOP_TAGS */
};
#define getserv(arg)	list_entry((arg), struct serv_struct, id)

static list_t serv = { &(serv), &(serv) }, *serv_start = &(serv);

/*
 * Find or add and initialize a service
 */
static serv_t * addserv(const char *const __restrict serv) __attribute__((nonnull(1)));
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
#ifdef USE_STOP_TAGS
	this->lvlk  = 0;
#endif /* USE_STOP_TAGS */
	ptr = serv_start->prev;
	goto out;
    }
    ptr = (list_t*)0;
    error("%s", strerror(errno));
out:
    return getserv(ptr);
}

static serv_t * findserv(const char *const __restrict serv) __attribute__((nonnull(1)));
static serv_t * findserv(const char *const serv)
{
    list_t * ptr;
    serv_t * ret = (serv_t*)0;

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
static void rememberreq(serv_t *__restrict serv, uint bit, const char *__restrict required) __attribute__((noinline,nonnull(1,3)));
static void rememberreq(serv_t *serv, uint bit, const char * required)
{
    char * token, * tmp = strdupa(required);
    list_t * ptr;
    uint old = bit;

    while ((token = strsep(&tmp, delimeter))) {
	boolean found = false;
	req_t * this;

	if (!*token)
	    continue;

	bit = old;

	switch(*token) {
	case '+':
	    /* This is an optional token */
	    token++;
	    bit = REQ_SHLD;
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
	}
    }

    /* Expand requested services for sorting */
    list_for_each(ptr, &(serv->sort.req)) {
	char * needed = getreq(ptr)->serv;
	if (needed)
	    requiresv(serv->name, needed);
    }
}

static void reversereq(const serv_t *__restrict serv, uint bit, const char *__restrict list) __attribute__((noinline,nonnull(1,3)));
static void reversereq(const serv_t * serv, uint bit, const char * list)
{
    const char * dep;
    char * rev = strdupa(list);
    uint old = bit;

    while ((dep = strsep(&rev, delimeter)) && *dep) {
	serv_t * tmp;
	list_t * ptr;

	if (!*dep)
	    continue;

	bit = old;

	switch (*dep) {
	case '+':
	    dep++;
	    bit = REQ_SHLD;
	default:
	    if (!(tmp = findserv(dep)))
		tmp = addserv(dep);
	    if (tmp) {
		const char * name;
		if ((name = getscript(serv->name)) == (char*)0)
		    name = serv->name;
		rememberreq(tmp, bit, name);
	    }
	    break;
	case '$':
	    list_for_each(ptr, sysfaci_start) {
		if (!strcmp(dep, getfaci(ptr)->name)) {
		    reversereq(serv, bit, getfaci(ptr)->repl);
		    break;
		}
	    }
	    break;
	}
    }
}

/*
 * Check required services for name
 */
static boolean chkrequired(const char *const __restrict name) __attribute__((nonnull(1)));
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
static boolean chkdependencies(const char *const __restrict name) __attribute__((nonnull(1)));
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
static serv_t * current_structure(const char *const __restrict this, const char order, const int runlvl, const char type) __attribute__((always_inline,nonnull(1)));
static serv_t * current_structure(const char *const this, const char order, const int runlvl, const char type)
{
    serv_t * serv = addserv(this);

    if (serv->order < order)
	serv->order = order;

    if ('S' == type)
	serv->lvls |= map_runlevel_to_lvl(runlvl);
#ifdef USE_STOP_TAGS
    else
	serv->lvlk |= map_runlevel_to_lvl(runlvl);
#endif /* USE_STOP_TAGS */

    return serv;
}

static void setlsb(const char *__restrict const name) __attribute__((unused));
static void setlsb(const char * const name)
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
static inline void nonlsb_script(void) __attribute__((always_inline));
static inline void nonlsb_script(void)
{
    list_t * pos;

    list_for_each(pos, serv_start) {
	if (getserv(pos)->opts & SERV_NOTLSB) {
	    list_t * tmp, * req = (list_t*)0;
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
static inline void active_script(void) __attribute__((always_inline));
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
		serv_t * chk = (serv_t*)0;
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
		if ((name = getscript(cur->name)) == (char*)0)
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
 * Last but not least the `$all' scripts will be set to the of
 * current the start order.
 */

static inline void all_script(void) __attribute__((always_inline));
static inline void all_script(void)
{
    list_t * pos;

    list_for_each(pos, serv_start) {
	serv_t * serv = getserv(pos);
	list_t * tmp;
	const char *name;
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
	/* Expand aliases to the real script name */
	if ((name = getscript(serv->name)) == (char*)0)
	    name = serv->name;
	setorder(name, neworder, false);
    }
}

/*
 * Remember reverse requests for required services
 */
static void reverse(char *__restrict stop, char *__restrict request) __attribute__((nonnull(1,2)));
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
static inline void makedep(void) __attribute__((always_inline));
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

    name = (char*)0;
    fprintf(boot, "TARGETS =");
    while (listscripts(&name, LVL_BOOT)) {
#if defined(MINIMAL_MAKE) && (MINIMAL_MAKE != 0)
	const serv_t *serv = findserv(getprovides(name));
	if (!serv || !(serv->opts & SERV_ENABLED))
	    continue;
#endif /* MINIMAL_MAKE */
	fprintf(boot, " %s", name);
    }
    putc('\n', boot);

    name = (char*)0;
    fprintf(start, "TARGETS =");
    while (listscripts(&name, LVL_ALL)) {	/* LVL_ALL: nearly all but not BOOT */
#if defined(MINIMAL_MAKE) && (MINIMAL_MAKE != 0)
	const serv_t *serv = findserv(getprovides(name));
	if (!serv || !(serv->opts & SERV_ENABLED))
	    continue;
#endif /* MINIMAL_MAKE */
	fprintf(start, " %s", name);
    }
    putc('\n', start);

    fprintf(boot,  "INTERACTIVE =");
    fprintf(start, "INTERACTIVE =");
    list_for_each(srv, serv_start) {
	serv_t * cur = getserv(srv);

#if defined(MINIMAL_MAKE) && (MINIMAL_MAKE != 0)
	if (!cur || !(cur->opts & SERV_ENABLED))
	    continue;
#else /* not MINIMAL_MAKE */
	if (!cur)
	    continue;
#endif /* not MINIMAL_MAKE */

	if (list_empty(&(cur->sort.req)))
	    continue;

	if (cur->lvls & LVL_BOOT)
	    out = boot;
	else
	    out = start;

	if ((name = getscript(cur->name)) == (char*)0)
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

	if ((name = getscript(cur->name)) == (char*)0)
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

		if ((name = getscript(dep->name)) == (char*)0)
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

		if ((name = getscript(req->serv)) == (char*)0)
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

    name = (char*)0;
    fprintf(stop, "TARGETS =");
    while (listscripts(&name, LVL_NORM)) {	/* LVL_NORM: nearly all but not BOOT and not SINGLE */
#if defined(MINIMAL_MAKE) && (MINIMAL_MAKE != 0)
	const serv_t *serv = findserv(getprovides(name));
	if (!serv || !(serv->opts & SERV_ENABLED))
	    continue;
#endif /* MINIMAL_MAKE */
	fprintf(stop, " %s", name);
    }
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

	if ((name = getscript(cur->name)) == (char*)0)
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

	    if ((name = getscript(rev->serv)) == (char*)0)
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
char *myname = (char*)0;
static void _logger (const char *const __restrict fmt, va_list ap);
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
 *  Check for script in list.
 */
static int curr_argc = -1;
static inline boolean chkfor(const char *const __restrict script, char ** const __restrict list, const int cnt) __attribute__((nonnull(1,2)));
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

/*
 * Open a runlevel directory, if it not
 * exists than create one.
 */
static DIR * openrcdir(const char *const __restrict rcpath) __attribute__((nonnull(1)));
static DIR * openrcdir(const char *const rcpath)
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

    if ((rcdir = opendir(rcpath)) == (DIR*)0) {
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
static inline void regcompiler(regex_t *__restrict preg, const char *__restrict regex, int cflags) __attribute__((always_inline,nonnull(1,2)));
static inline void regcompiler(regex_t *preg, const char *regex, int cflags)
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
static inline boolean regexecutor(regex_t *__restrict preg, const char *__restrict string, size_t nmatch, regmatch_t pmatch[], int eflags) __attribute__((nonnull(1,2)));
static inline boolean regexecutor(regex_t *preg, const char *string, size_t nmatch, regmatch_t pmatch[], int eflags)
{
    register int ret = regexec(preg, string, nmatch, pmatch, eflags);
    if (ret > REG_NOMATCH) {
	regerror(ret, preg, buf, sizeof (buf));
	regfree (preg);
	warn("%s\n", buf);
    }
    return (ret ? false : true);
}

/*
 * The script scanning engine.
 * We have to alloc the regular expressions first before
 * calling scan_script_defaults().  After the last call
 * of scan_script_defaults() we may free the expressions.
 */
static inline void scan_script_regalloc(void) __attribute__((always_inline));
static inline void scan_script_regalloc(void)
{
    regcompiler(&reg.prov,      PROVIDES,       REG_EXTENDED|REG_ICASE);
    regcompiler(&reg.req_start, REQUIRED_START, REG_EXTENDED|REG_ICASE|REG_NEWLINE);
    regcompiler(&reg.req_stop,  REQUIRED_STOP,  REG_EXTENDED|REG_ICASE|REG_NEWLINE);
    regcompiler(&reg.shl_start, SHOULD_START,   REG_EXTENDED|REG_ICASE|REG_NEWLINE);
    regcompiler(&reg.shl_stop,  SHOULD_STOP,    REG_EXTENDED|REG_ICASE|REG_NEWLINE);
    regcompiler(&reg.start_bf,  START_BEFORE,   REG_EXTENDED|REG_ICASE|REG_NEWLINE);
    regcompiler(&reg.stop_af,   STOP_AFTER,     REG_EXTENDED|REG_ICASE|REG_NEWLINE);
    regcompiler(&reg.def_start, DEFAULT_START,  REG_EXTENDED|REG_ICASE|REG_NEWLINE);
    regcompiler(&reg.def_stop,  DEFAULT_STOP,   REG_EXTENDED|REG_ICASE|REG_NEWLINE);
    regcompiler(&reg.desc,      DESCRIPTION,    REG_EXTENDED|REG_ICASE|REG_NEWLINE);
}

static inline void scan_script_reset(void) __attribute__((always_inline));
static inline void scan_script_reset(void)
{
    xreset(script_inf.provides);
    xreset(script_inf.required_start);
    xreset(script_inf.required_stop);
    xreset(script_inf.should_start);
    xreset(script_inf.should_stop);
    xreset(script_inf.start_before);
    xreset(script_inf.stop_after);
    xreset(script_inf.default_start);
    xreset(script_inf.default_stop);
    xreset(script_inf.description);
}

#define FOUND_LSB_HEADER   0x01
#define FOUND_LSB_DEFAULT  0x02
#define FOUND_LSB_OVERRIDE 0x04

static uchar scan_lsb_headers(const char *const __restrict path) __attribute__((nonnull(1)));
static uchar scan_lsb_headers(const char *const path)
{
    regmatch_t subloc[SUBNUM_SHD+1], *val = &subloc[SUBNUM-1], *shl = &subloc[SUBNUM_SHD-1];
    FILE *script;
    char *pbuf = buf;
    char *begin = (char*)0, *end = (char*)0;
    uchar ret = 0;

#define provides	script_inf.provides
#define required_start	script_inf.required_start
#define required_stop	script_inf.required_stop
#define should_start	script_inf.should_start
#define should_stop	script_inf.should_stop
#define start_before	script_inf.start_before
#define stop_after	script_inf.stop_after
#define default_start	script_inf.default_start
#define default_stop	script_inf.default_stop
#define description	script_inf.description

    info("Loading %s\n", path);
    script = fopen(path, "r");
    if (!script)
	error("fopen(%s): %s\n", path, strerror(errno));

#define COMMON_ARGS	buf, SUBNUM, subloc, 0
#define COMMON_SHD_ARGS	buf, SUBNUM_SHD, subloc, 0
    while (fgets(buf, sizeof(buf), script)) {

	/* Skip scanning above from LSB magic start */
	if (!begin) {
	    if ( (begin = strstr(buf, "### BEGIN INIT INFO")) ) {
	        /* Let the latest LSB header override the one found earlier */
	        scan_script_reset();
	    }
	    continue;
	}

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
#ifdef USE_STOP_TAGS
	if (!required_stop  && regexecutor(&reg.req_stop,  COMMON_ARGS) == true) {
	    if (val->rm_so < val->rm_eo) {
		*(pbuf+val->rm_eo) = '\0';
		required_stop = xstrdup(pbuf+val->rm_so);
	    } else
		required_stop = empty;
	}
#endif /* USE_STOP_TAGS */
	if (!should_start && regexecutor(&reg.shl_start,   COMMON_SHD_ARGS) == true) {
	    if (shl->rm_so < shl->rm_eo) {
		*(pbuf+shl->rm_eo) = '\0';
		should_start = xstrdup(pbuf+shl->rm_so);
	    } else
		should_start = empty;
	}
#ifdef USE_STOP_TAGS
	if (!should_stop  && regexecutor(&reg.shl_stop,    COMMON_SHD_ARGS) == true) {
	    if (shl->rm_so < shl->rm_eo) {
		*(pbuf+shl->rm_eo) = '\0';
		should_stop = xstrdup(pbuf+shl->rm_so);
	    } else
		should_stop = empty;
	}
#endif /* USE_STOP_TAGS */
	if (!start_before && regexecutor(&reg.start_bf,    COMMON_SHD_ARGS) == true) {
	    if (shl->rm_so < shl->rm_eo) {
		*(pbuf+shl->rm_eo) = '\0';
		start_before = xstrdup(pbuf+shl->rm_so);
	    } else
		start_before = empty;
	}
#ifdef USE_STOP_TAGS
	if (!stop_after  && regexecutor(&reg.stop_af,      COMMON_SHD_ARGS) == true) {
	    if (shl->rm_so < shl->rm_eo) {
		*(pbuf+shl->rm_eo) = '\0';
		stop_after = xstrdup(pbuf+shl->rm_so);
	    } else
		stop_after = empty;
	}
#endif /* USE_STOP_TAGS */
	if (!default_start  && regexecutor(&reg.def_start, COMMON_ARGS) == true) {
	    if (val->rm_so < val->rm_eo) {
		*(pbuf+val->rm_eo) = '\0';
		default_start = xstrdup(pbuf+val->rm_so);
	    } else
		default_start = empty;
	}
#ifdef USE_STOP_TAGS
	if (!default_stop   && regexecutor(&reg.def_stop,  COMMON_ARGS) == true) {
	    if (val->rm_so < val->rm_eo) {
		*(pbuf+val->rm_eo) = '\0';
		default_stop = xstrdup(pbuf+val->rm_so);
	    } else
		default_stop = empty;
	}
#endif /* USE_STOP_TAGS */
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
    if (begin && end)
	ret |= FOUND_LSB_HEADER;

    if (begin && !end) {
	char *name = basename(path);
	if (*name == 'S' || *name == 'K')
	    name += 3;
	warn("script %s is broken: missing end of LSB comment.\n", name);
	error("exiting now!\n");
    }

#ifndef USE_STOP_TAGS
    if (verbose && (begin && end && (!provides || !required_start)))
#else  /* USE_STOP_TAGS */
    if (verbose && (begin && end && (!provides || !required_start || !required_stop)))
#endif /* USE_STOP_TAGS */
    {
	char *name = basename(path);
	if (*name == 'S' || *name == 'K')
	    name += 3;
	warn("script %s could be broken: incomplete LSB comment.\n", name);
	if (!provides)
	    warn("Missing entry for Provides: please add even if empty.\n");
	if (!required_start)
	    warn("Missing entry for Required-Start: please add even if empty.\n");
#ifdef USE_STOP_TAGS
	if (!required_stop)
	    warn("Missing entry for Required-Stop: please add even if empty.\n");
#endif /* USE_STOP_TAGS */
    }

#undef provides
#undef required_start
#undef required_stop
#undef should_start
#undef should_stop
#undef start_before
#undef stop_after
#undef default_start
#undef default_stop
#undef description
    return ret;
}

/*
 * Follow symlinks, return the basename of the file pointed to by
 * symlinks or the basename of the current path if no symlink.
 */
static char *scriptname(const char *__restrict path) __attribute__((nonnull(1)));
static char *scriptname(const char * path)
{
    uint deep = 0;
    char linkbuf[PATH_MAX+1];
    char *script = xstrdup(path);

    strncpy(linkbuf, script, sizeof(linkbuf)-1);
    linkbuf[PATH_MAX] = '\0';

    do {
        struct stat st;
	int linklen;

	if (deep++ > MAXSYMLINKS) {
	    errno = ELOOP;
	    warn("Can not determine script name for %s: %s\n", path, strerror(errno));
	    break;
	}

	if (lstat(script, &st) < 0) {
	    warn("Can not stat %s: %s\n", script, strerror(errno));
	    break;
	}

	if (!S_ISLNK(st.st_mode))
	    break;

	if ((linklen = readlink(script, linkbuf, sizeof(linkbuf)-1)) < 0)
	    break;
	linkbuf[linklen] = '\0';

	if (linkbuf[0] != '/') {	/* restore relative links */
	    const char *lastslash;

	    if ((lastslash = strrchr(script, '/'))) {
		size_t dirname_len = lastslash - script + 1;

		if (dirname_len + linklen > PATH_MAX)
		    linklen = PATH_MAX - dirname_len;

		memmove(&linkbuf[dirname_len], &linkbuf[0], linklen + 1);
		memcpy(&linkbuf[0], script, dirname_len);
	    }
	}

	free(script);
	script = xstrdup(linkbuf);

    } while (1);

    free(script);
    script = xstrdup(basename(linkbuf));

    return script;
}

static uchar load_overrides(const char *const __restrict dir, const char *const __restrict name) __attribute__((nonnull(1,2)));
static uchar load_overrides(const char *const dir, const char *const name)
{
    uchar ret = 0;
    char fullpath[PATH_MAX+1];
    struct stat statbuf;
    int n;

    n = snprintf(&fullpath[0], sizeof(fullpath), "%s%s/%s", (root && !set_override) ? root : "", dir, name);
    if (n >= sizeof(fullpath) || n < 0)
	error("snprintf(): %s\n", strerror(errno));

    if (stat(fullpath, &statbuf) == 0 && S_ISREG(statbuf.st_mode))
        ret = scan_lsb_headers(fullpath);
    if (ret)
	ret |= FOUND_LSB_OVERRIDE;
    return ret;
}

static uchar scan_script_defaults(const char *const __restrict path, const char *const __restrict override_path) __attribute__((nonnull(1,2)));
static uchar scan_script_defaults(const char *const path, const char *const override_path)
{
    uchar ret = 0;
    char *name = scriptname(path);

    if (!name)
	return ret;

    /* Reset old results */
    scan_script_reset();

#ifdef SUSE
    /* Common script ... */
    if (!strcmp(name, "halt")) {
	ret |= (FOUND_LSB_HEADER|FOUND_LSB_DEFAULT);
	goto out;
    }

    /* ... and its link */
    if (!strcmp(name, "reboot")) {
	ret |= (FOUND_LSB_HEADER|FOUND_LSB_DEFAULT);
	goto out;
    }

    /* Common script for single mode */
    if (!strcmp(name, "single")) {
	ret |= (FOUND_LSB_HEADER|FOUND_LSB_DEFAULT);
	goto out;
    }
#endif /* SUSE */

    /* Replace with headers from the script itself */
    ret |= scan_lsb_headers(path);

    if (!ret)		/* Load values if the override file exist */
	ret |= load_overrides("/usr/share/insserv/overrides", name);
    else
	ret |= FOUND_LSB_DEFAULT;

    /*
     * Allow host-specific overrides to replace the content in the
     * init.d scripts
     */
    ret |= load_overrides(override_path, name);
#ifdef SUSE
out:
#endif /* SUSE */
    free(name);
    return ret;
}

static inline void scan_script_regfree() __attribute__((always_inline));
static inline void scan_script_regfree()
{
    regfree(&reg.prov);
    regfree(&reg.req_start);
    regfree(&reg.req_stop);
    regfree(&reg.shl_start);
    regfree(&reg.shl_stop);
    regfree(&reg.start_bf);
    regfree(&reg.stop_af);
    regfree(&reg.def_start);
    regfree(&reg.def_stop);
    regfree(&reg.desc);
}

static struct {
    char *location;
    const int lvl;
    const int seek;
    const char key;
} runlevel_locations[] = {
#ifdef SUSE	/* SuSE's SystemV link scheme */
    {"rc0.d/",    LVL_HALT,   LVL_NORM, '0'},
    {"rc1.d/",    LVL_ONE,    LVL_NORM, '1'}, /* runlevel 1 switch over to single user mode */
    {"rc2.d/",    LVL_TWO,    LVL_NORM, '2'},
    {"rc3.d/",    LVL_THREE,  LVL_NORM, '3'},
    {"rc4.d/",    LVL_FOUR,   LVL_NORM, '4'},
    {"rc5.d/",    LVL_FIVE,   LVL_NORM, '5'},
    {"rc6.d/",    LVL_REBOOT, LVL_NORM, '6'},
    {"rcS.d/",    LVL_SINGLE, LVL_NORM, 'S'}, /* runlevel S is for single user mode */
    {"boot.d/",   LVL_BOOT,   LVL_BOOT, 'B'}, /* runlevel B is for system initialization */
#else		/* not SUSE (actually, Debian) */
    {"../rc0.d/", LVL_HALT,   LVL_NORM, '0'},
    {"../rc1.d/", LVL_ONE,    LVL_NORM, '1'}, /* runlevel 1 switch over to single user mode */
    {"../rc2.d/", LVL_TWO,    LVL_NORM, '2'},
    {"../rc3.d/", LVL_THREE,  LVL_NORM, '3'},
    {"../rc4.d/", LVL_FOUR,   LVL_NORM, '4'},
    {"../rc5.d/", LVL_FIVE,   LVL_NORM, '5'},
    {"../rc6.d/", LVL_REBOOT, LVL_NORM, '6'},
    {"../rcS.d/", LVL_BOOT,   LVL_BOOT, 'S'}, /* runlevel S is for system initialization */
		/* On e.g. Debian there exist no boot.d */
#endif		/* not SUSE */
};

#define RUNLEVLES (sizeof(runlevel_locations)/sizeof(runlevel_locations[0]))

int map_has_runlevels(void)
{
    return RUNLEVLES;
}

char map_runlevel_to_key(const int runlevel)
{
    if (runlevel >= RUNLEVLES) {
	warn("Wrong runlevel %d\n", runlevel);
    }
    return runlevel_locations[runlevel].key;
}

int map_key_to_lvl(const char key)
{
    int runlevel;
    const char uckey = toupper(key);
    for (runlevel = 0; runlevel < RUNLEVLES; runlevel++) {
	if (uckey == runlevel_locations[runlevel].key)
	    return runlevel_locations[runlevel].lvl;
    }
    warn("Wrong runlevel key '%c'\n", uckey);
    return 0;
}

static const char *map_runlevel_to_location(const int runlevel)
{
    if (runlevel >= RUNLEVLES) {
	warn("Wrong runlevel %d\n", runlevel);
    }
    return runlevel_locations[runlevel].location;
}

int map_runlevel_to_lvl(const int runlevel)
{
    if (runlevel >= RUNLEVLES) {
	warn("Wrong runlevel %d\n", runlevel);
    }
    return runlevel_locations[runlevel].lvl;
}

#ifndef SUSE
static int map_runlevel_to_seek(const int runlevel)
{
    return runlevel_locations[runlevel].seek;
}
#endif /* not SUSE */

/*
 * Scan current service structure
 */
static void scan_script_locations(const char *const __restrict path,
	const char *const __restrict override_path, char ** const __restrict iargv, const int icnt) __attribute__((nonnull(1,2)));
static void scan_script_locations(const char *const path, const char *const override_path, char ** const iargv, const int icnt)
{
    int runlevel;

    pushd(path);
    for (runlevel = 0; runlevel < RUNLEVLES; runlevel++) {
	const char * rcd = (char*)0;
	DIR  * rcdir;
	struct dirent *d;
	char * token;
	struct stat st_script;

	rcd = map_runlevel_to_location(runlevel);
	rcdir = openrcdir(rcd); /* Creates runlevel directory if necessary */
	if (rcdir == (DIR*)0)
	    break;
	pushd(rcd);
	while ((d = readdir(rcdir)) != (struct dirent*)0) {
	    char * ptr = d->d_name;
	    char order = 0;
	    char type;
	    char* begin = (char*)0;	/* Remember address of ptr handled by strsep() */
	    uchar lsb = 0;

#ifndef USE_STOP_TAGS
	    if (*ptr != 'S')
#else  /* USE_STOP_TAGS */
	    if (*ptr != 'S' && *ptr != 'K')
#endif /* USE_STOP_TAGS */
		continue;
	    type = *ptr;
	    ptr++;

	    if (strspn(ptr, "0123456789") < 2)
		continue;
	    order = atoi(ptr);
	    ptr += 2;

	    if (stat(d->d_name, &st_script) < 0) {
		xremove(d->d_name);	/* dangling sym link */
		continue;
	    }
#ifdef SUSE
	    /*
	     * Ignore scripts if removed later to avoid not used depencies
	     * in the makefiles depend.boot, .depend.start and .depend.stop
	     */
	    if (iargv && chkfor(ptr, iargv, icnt))
		continue;
#endif /* SUSE */
	    lsb = scan_script_defaults(d->d_name, override_path);

	    if (!script_inf.provides || script_inf.provides == empty)
		script_inf.provides = xstrdup(ptr);
#ifndef SUSE
	    if (!lsb) {
	        script_inf.required_start = xstrdup(DEFAULT_DEPENDENCY);
		script_inf.required_stop  = xstrdup(DEFAULT_DEPENDENCY);
		script_inf.default_start  = xstrdup(DEFAULT_START_LVL);
		script_inf.default_stop   = xstrdup(DEFAULT_STOP_LVL);
	    }
#endif /* not SUSE */

	    begin = script_inf.provides;
	    while ((token = strsep(&begin, delimeter)) && *token) {
		serv_t * service = (serv_t*)0;
		if (*token == '$') {
		    warn("script %s provides system facility %s, skipped!\n", d->d_name, token);
		    continue;
		}
		service = current_structure(token, order, runlevel, type);

		if (service->opts & SERV_KNOWN)
		    continue;
		service->opts |= (SERV_KNOWN|SERV_ENABLED);

		if (!lsb)
		    service->opts |= SERV_NOTLSB;

		if ((lsb & FOUND_LSB_HEADER) == 0) {
		    if ((lsb & (FOUND_LSB_DEFAULT | FOUND_LSB_OVERRIDE)) == 0)
		      warn("warning: script '%s' missing LSB tags and overrides\n", d->d_name);
		    else
  		        warn("warning: script '%s' missing LSB tags\n", d->d_name);
		}

		if (script_inf.required_start && script_inf.required_start != empty) {
		    rememberreq(service, REQ_MUST, script_inf.required_start);
		}
		if (script_inf.should_start && script_inf.should_start != empty) {
		    rememberreq(service, REQ_SHLD, script_inf.should_start);
		}
		if (script_inf.start_before && script_inf.start_before != empty) {
		    reversereq(service, REQ_SHLD, script_inf.start_before);
		}
#ifdef USE_STOP_TAGS
		/*
		 * required_stop and should_stop arn't used in SuSE Linux.
		 * Note: Sorting is done symetrical in stop and start!
		 * The stop_order is given by max_order + 1 - start_order.
		 */
		if (script_inf.required_stop && script_inf.required_stop != empty) {
		    rememberreq(service, REQ_MUST, script_inf.required_stop);
		}
		if (script_inf.should_stop && script_inf.should_stop != empty) {
		    rememberreq(service, REQ_SHLD, script_inf.should_stop);
		}
		if (script_inf.stop_after && script_inf.stop_after != empty) {
		    reversereq(service, REQ_SHLD, script_inf.stop_after);
		}
#endif /* USE_STOP_TAGS */
	    }

	    scan_script_reset();
	}
	popd();
	closedir(rcdir);
    }
    popd();
    return;
}

#if defined(FACI_EXPANSION) && (FACI_EXPANSION > 0)
/*
 * Expand the system facilities after all insserv.conf files have been scanned.
 */
static char * facisep(char **__restrict repl, int *__restrict deep) __attribute__((noinline,nonnull(1,2)));
static char * facisep(char ** repl, int * deep)
{
    char * token = (char*)0, * exp = *repl;

    if (exp == (char*)0)
	goto out;

    if (*deep > 10) {
	warn("The nested level of the system facilities in the insserv.conf file(s) is to large\n");
	goto next;
    }

    if (*exp == '$') {
	static char * more, * start;
	if (more == (char*)0) {
	    const char * end;
	    list_t * ptr;
	    size_t len;

            if ((end = strpbrk(exp, delimeter)))
		len = end - exp;
	    else
		len = strlen(exp);

	    list_for_each(ptr, sysfaci_start) {
		if (!strncmp(getfaci(ptr)->name, exp, len)) {
		    more = xstrdup(getfaci(ptr)->repl);
		    break;
		}
	    }

	    if (more)
		start = more;
	    else {
		(void)strsep(repl, delimeter);
		goto next;
	    }
	}
	(*deep)++;
	token = facisep(&more, deep);
	(*deep)--;
	if (!more)
	    (void)strsep(repl, delimeter);
	if (token)
	    goto out;
	free(start);
	more = (char*)0;
    }
next:
    token = strsep(repl, delimeter);
out:
    return token;
}
#endif /* FACI_EXPANSION */

/*
 * The /etc/insserv.conf scanning engine.
 */
static void scan_conf_file(const char *__restrict file) __attribute__((nonnull(1)));;
static void scan_conf_file(const char * file)
{
    regmatch_t subloc[SUBCONFNUM], *val = (regmatch_t*)0;
    FILE *conf;

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
	char *pbuf = &buf[0];
	if (*pbuf == '#')
	    continue;
	if (*pbuf == '\n')
	    continue;
	if (regexecutor(&creg.isysfaci, buf, SUBCONFNUM, subloc, 0) == true) {
	    char * virt = (char*)0, * real = (char*)0;
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
			if(real) {
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
	if (regexecutor(&creg.isactive, buf, SUBCONFNUM, subloc, 0) == true) {
	    char * key = (char*)0, * servs = (char*)0;
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

    fclose(conf);
    return;
err:
    warn("fopen(%s): %s\n", file, strerror(errno));
}

static int cfgfile_filter(const struct dirent *__restrict d) __attribute__((nonnull(1)));
static int cfgfile_filter(const struct dirent * d)
{
    const char* name = d->d_name;
    const char* end;

    if (!name || (*name == '\0'))
	return 0;
    if ((*name == '.') && ((*(name+1) == '\0') || (*(name+1) == '.')))
	return 0;
    else {
	struct stat st;
	if ((stat(name,&st) < 0) || !S_ISREG(st.st_mode))
	    return 0;
    }
    if ((end = strrchr(name, '.'))) {
	end++;
	if (!strncmp(end, "rpm", 3)	|| /* .rpmorig, .rpmnew, .rmpsave, ... */
	    !strncmp(end, "ba", 2)	|| /* .bak, .backup, ... */
#ifdef SUSE
	    !strcmp(end,  "local")	|| /* .local are sourced by the basename */
#endif /* not SUSE */
	    !strcmp(end,  "old")	||
	    !strcmp(end,  "new")	||
	    !strcmp(end,  "org")	||
	    !strcmp(end,  "orig")	||
	    !strncmp(end, "dpkg", 3)	|| /* .dpkg-old, .dpkg-new ... */
	    !strcmp(end,  "save")	||
	    !strcmp(end,  "swp")	|| /* Used by vi like editors */
	    !strcmp(end,  "core"))	   /* modern core dump */
	{
	    return 0;
	}
    }
    if ((end = strrchr(name, ','))) {
	end++;
	if (!strcmp(end,  "v"))		  /* rcs-files */
	    return 0;
    }
    return 1;
}

static void scan_conf(const char *__restrict file) __attribute__((nonnull(1)));;
static void scan_conf(const char * file)
{
    struct dirent** namelist = (struct dirent**)0;
    char path[PATH_MAX+1];
#if defined(FACI_EXPANSION) && (FACI_EXPANSION > 0)
    list_t * ptr;
#endif /* FACI_EXPANSION */
    int n;

    regcompiler(&creg.isysfaci,  CONFLINE, REG_EXTENDED|REG_ICASE);
    regcompiler(&creg.isactive, CONFLINE2, REG_EXTENDED|REG_ICASE);

    n = snprintf(&path[0], sizeof(path), "%s%s",   (root && !set_insconf) ? root : "", file);
    if (n >= sizeof(path) || n < 0)
	error("snprintf(): %s\n", strerror(errno));

    scan_conf_file(path);

    n = snprintf(&path[0], sizeof(path), "%s%s.d", (root && !set_insconf) ? root : "", file);
    if (n >= sizeof(path) || n < 0)
	error("snprintf(): %s\n", strerror(errno));

    n = scandir(path, &namelist, cfgfile_filter, alphasort);
    if(n > 0) {
	while(n--) {
	    char buf[PATH_MAX+1];
	    int r;

	    r = snprintf(&buf[0], sizeof(buf), "%s/%s", path, namelist[n]->d_name);
	    if (r >= sizeof(buf) || r < 0)
		error("snprintf(): %s\n", strerror(errno));

	    scan_conf_file(buf);

	    free(namelist[n]);
	}
    }

    if (namelist)
	free(namelist);

    regfree(&creg.isysfaci);
    regfree(&creg.isactive);
#if defined(FACI_EXPANSION) && (FACI_EXPANSION > 0)
    list_for_each(ptr, sysfaci_start) {
	int deep = 0;
        char * repl = getfaci(ptr)->repl;
        char * real, *list = (char*)0;

        while ((real = facisep(&repl, &deep))) {
	    if (!list) {
		list = xstrdup(real);
	    } else {
		list = realloc(list, strlen(list)+2+strlen(real));
		strcat(list, " ");
		strcat(list, real);
	    }
        }

	if (list) {
	    free(getfaci(ptr)->repl);
	    getfaci(ptr)->repl = list;
	}
    }
#endif /* FACI_EXPANSION */
}

#if !defined(FACI_EXPANSION) || (FACI_EXPANSION == 0)
static inline void expand_conf(void)
{
    list_t * ptr;
    list_for_each(ptr, sysfaci_start)
	virtprov(getfaci(ptr)->name, getfaci(ptr)->repl);
}
#endif /* not FACI_EXPANSION */

/*
 * Scan for a Start or Kill script within a runlevel directory.
 * We start were we leave the directory, the upper level
 * has to call rewinddir(3) if necessary.
 */
static inline char * scan_for(DIR *const __restrict rcdir, const char *const __restrict script, char type) __attribute__((always_inline,nonnull(1,2)));;
static inline char * scan_for(DIR *const rcdir, const char *const script, char type)
{
    struct dirent *d;
    char * ret = (char*)0;

    while ((d = readdir(rcdir)) != (struct dirent*)0) {
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

static struct option long_options[] =
{
    {"verbose",	0, (int*)0, 'v'},
    {"config",	1, (int*)0, 'c'},
    {"dryrun",	0, (int*)0, 'n'},
    {"default",	0, (int*)0, 'd'},
    {"remove",	0, (int*)0, 'r'},
    {"force",	0, (int*)0, 'f'},
    {"path",	1, (int*)0, 'p'},
    {"override",1, (int*)0, 'o'},
    {"help",	0, (int*)0, 'h'},
    { 0,	0, (int*)0,  0 },
};

static void help(const char *const __restrict  name) __attribute__((nonnull(1)));
static void help(const char *const  name)
{
    printf("Usage: %s [<options>] [init_script|init_directory]\n", name);
    printf("Available options:\n");
    printf("  -h, --help       This help.\n");
    printf("  -r, --remove     Remove the listed scripts from all runlevels.\n");
    printf("  -f, --force      Ignore if a required service is missed.\n");
    printf("  -v, --verbose    Provide information on what is being done.\n");
    printf("  -p <path>, --path <path>  Path to replace " INITDIR ".\n");
    printf("  -o <path>, --override <path> Path to replace " OVERRIDEDIR ".\n");
    printf("  -c <config>, --config <config>  Path to config file.\n");
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
    char * override_path = OVERRIDEDIR;
    char * insconf = INSCONF;
    int runlevel, c;
    boolean del = false;
    boolean defaults = false;
    boolean ignore = false;

    myname = basename(*argv);

    for (c = 0; c < argc; c++)
	argr[c] = (char*)0;

    while ((c = getopt_long(argc, argv, "c:dfrhvno:p:", long_options, (int *)0)) != -1) {
	switch (c) {
	    case 'c':
		insconf = optarg;
		set_insconf = true;
		break;
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
	    case 'p':
		path = optarg;
		break;
	    case 'o':
		override_path = optarg;
		set_override = true;
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
	    if (stat(*argv, &st_script) < 0)
		error("%s: %s\n", *argv, strerror(errno));
	} else {
	    pushd(path);
	    if (stat(*argv, &st_script) < 0)
		error("%s: %s\n", *argv, strerror(errno));
	    popd();
	}

	if (S_ISDIR(st_script.st_mode)) {
	    const size_t l = strlen(*argv);

	    path = xstrdup(*argv);
	    if (path[l-1] == '/')
		path[l-1] = '\0';

	    if (del)
		error("usage: %s [[-r] init_script|init_directory]\n", myname);
	    argv++;
	    argc--;
	    if (argc)
		error("usage: %s [[-r] init_script|init_directory]\n", myname);
	} else {
	    char * base, * ptr = xstrdup(*argv);

	    if ((base = strrchr(ptr, '/'))) {
		*base = '\0';
		path  = ptr;
	    } else
		free(ptr);
	}
    }

    if (strcmp(path, INITDIR) != 0) {
	char * tmp;
	root = xstrdup(path);
	if ((tmp = strstr(root, INITDIR))) {
	    *tmp = '\0';
	} else {
	    free(root);
	    root = (char*)0;
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
#endif /* DEBUG */

    /*
     * Scan and set our configuration for virtual services.
     */
    scan_conf(insconf);

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
    scan_script_locations(path, override_path, (del ? argv : (char**)0), argc);

    if ((initdir = opendir(path)) == (DIR*)0)
	error("can not opendir(%s): %s\n", path, strerror(errno));
    /*
     * Now scan for the service scripts and their LSB comments.
     */
    pushd(path);
    while ((d = readdir(initdir)) != (struct dirent*)0) {
	serv_t * service = (serv_t*)0;
	char * token;
	char* begin = (char*)0;	/* Remember address of ptr handled by strsep() */
	uchar lsb = 0;
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
	lsb = scan_script_defaults(d->d_name, override_path);

	if ((lsb & FOUND_LSB_HEADER) == 0) {
	    if ((lsb & (FOUND_LSB_DEFAULT | FOUND_LSB_OVERRIDE)) == 0)
	        warn("warning: script '%s' missing LSB tags and overrides\n", d->d_name);
	    else
	        warn("warning: script '%s' missing LSB tags\n", d->d_name);
	}

#ifdef SUSE
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
	    serv->opts |= SERV_ALL;
	    rememberreq(serv, REQ_SHLD, "kbd");
	    continue;
	}
#endif /* SUSE */

#ifndef SUSE
	if (!lsb) {
	    script_inf.required_start = xstrdup(DEFAULT_DEPENDENCY);
	    script_inf.required_stop = xstrdup(DEFAULT_DEPENDENCY);
	    script_inf.default_start = xstrdup(DEFAULT_START_LVL);
	    script_inf.default_stop = xstrdup(DEFAULT_STOP_LVL);
	}
#endif /* not SUSE */

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
		    list_t * ptr = (list_t*)0;

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
			script_inf.default_start = lvl2str(guess->lvls);
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
				script_inf.default_start = lvl2str(getserv(ptr)->lvls);
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
	    while ((token = strsep(&begin, delimeter)) && *token) {

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

		    if ((!begin || !*begin) && (count > 1)) { /* Last token */ 
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

		    if (!known) {
			if (script_inf.required_start && script_inf.required_start != empty) {
			    rememberreq(service, REQ_MUST, script_inf.required_start);
			}
			if (script_inf.should_start && script_inf.should_start != empty) {
			    rememberreq(service, REQ_SHLD, script_inf.should_start);
			}
#ifdef USE_STOP_TAGS
			/*
			 * required_stop and should_stop arn't used in SuSE Linux.
			 * Note: Sorting is done symetrical in stop and start!
			 * The stop order is given by max order - start order.
			 */
			if (script_inf.required_stop && script_inf.required_stop != empty) {
			    rememberreq(service, REQ_MUST, script_inf.required_stop);
			}
			if (script_inf.should_stop && script_inf.should_stop != empty) {
			    rememberreq(service, REQ_SHLD, script_inf.should_stop);
			}
#endif /* USE_STOP_TAGS */
		    }

		    if (script_inf.start_before && script_inf.start_before != empty) {
			reversereq(service, REQ_SHLD, script_inf.start_before);
		    }
#ifdef USE_STOP_TAGS
		    if (script_inf.stop_after && script_inf.stop_after != empty) {
			reversereq(service, REQ_SHLD, script_inf.stop_after);
		    }
#endif /* USE_STOP_TAGS */
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
		 	uint deflvls = str2lvl(script_inf.default_start);

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
			    script_inf.default_start = xstrdup(DEFAULT_START_LVL);
		    }
#ifdef USE_STOP_TAGS
		    /*
		     * default_stop arn't used in SuSE Linux.
		     */
		    if (script_inf.default_stop && script_inf.default_stop != empty) {
		 	uint deflvlk = str2lvl(script_inf.default_stop);

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
#endif /* USE_STOP_TAGS */
		}
	    }
	    free(provides);
	}

	/* Ahh ... set default multiuser with network */
	if (!script_inf.default_start || script_inf.default_start == empty)
	    script_inf.default_start = xstrdup(DEFAULT_START_LVL);
#ifdef USE_STOP_TAGS
	if (!script_inf.default_stop  || script_inf.default_start == empty)
	    script_inf.default_stop  = xstrdup(DEFAULT_STOP_LVL);
#endif /* USE_STOP_TAGS */

	if (chkfor(d->d_name, argv, argc) && !defaults) {
	    if (argr[curr_argc]) {
		char * ptr = argr[curr_argc];
		struct _mark {
		    const char * wrd;
		    char * order;
		    char ** str;
		} mark[] = {
		    {"start=", (char*)0, &script_inf.default_start},
		    {"stop=",  (char*)0, &script_inf.default_stop },
		    {(char*)0, (char*)0, (char**)0}
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
#ifdef USE_STOP_TAGS
	    /*
	     * default_stop arn't used in SuSE Linux.
	     */
	    if (script_inf.default_stop && script_inf.default_stop != empty) {
		if (service && !del)
		  {
		    service->lvlk = str2lvl(script_inf.default_stop);
		    runlevels(token, script_inf.default_stop);
		  }
	    }
#endif /* USE_STOP_TAGS */
	}
	script_inf.provides = begin;

	/* Remember if not LSB conform script */
	if (!lsb && service)
	    service->opts |= SERV_NOTLSB;
    }
    /* Reset remaining pointers */
    scan_script_reset();

    /*
     * Free the regular scanner for the scripts.
     */
    scan_script_regfree();

    /* back */
    popd();
    closedir(initdir);

#if !defined(FACI_EXPANSION) || (FACI_EXPANSION == 0)
    expand_conf();
#endif /* not FACI_EXPANSION */

#ifdef SUSE
    /*
     *  Set initial order of some services
     */
    setorder("network",	 	5,  false); setlsb("network");
    setorder("inetd",		20, false); setlsb("inetd");
    setorder("halt",		20, false); setlsb("halt");
    setorder("reboot",		20, false); setlsb("reboot");
    setorder("single",		20, false); setlsb("single");
    setorder("serial",		10, false); setlsb("serial");
    setorder("gpm",		20, false); setlsb("gpm");
    setorder("boot.setup",	20, false);
#elif 0 /* not SUSE, but currently disabled */
    /*
     * Debian scripts with well known sequence numbers.  Not sure if
     * we want to fix all of these.
     */
    setorder("checkroot.sh",	10, false); setlsb("checkroot.sh");
    setorder("checkfs.sh",	30, false); setlsb("checkfs.sh");
    setorder("networking",	40, false); setlsb("networking.sh");
    setorder("mountnfs.sh",	45, false); setlsb("mountnfs.sh");
    setorder("single",		90, false); setlsb("single");
#endif /* not SUSE */

    /*
     * Set virtual dependencies for already enabled none LSB scripts.
     */
    nonlsb_script();

    /*
     * Now generate for all scripts the dependencies
     */
    follow_all();

    if (is_loop_detected() && !ignore)
	error("exiting now!\n");

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
    for (runlevel = 0; runlevel < RUNLEVLES; runlevel++) {
	int order;
	const char * script;
	char nlink[PATH_MAX+1], olink[PATH_MAX+1];
	const char * rcd = (char*)0;
	DIR  * rcdir;

	if ((rcd = map_runlevel_to_location(runlevel)) == (char*)0)
	    continue;

	script = (char*)0;
	rcdir = openrcdir(rcd); /* Creates runlevel directory if necessary */
	if (rcdir == (DIR*)0)
	    break;
	pushd(rcd);

	/*
	 * See if we found scripts which should not be
	 * included within this runlevel directory.
	 */
	while ((d = readdir(rcdir)) != (struct dirent*)0) {
	    const char * ptr = d->d_name;
	    serv_t * serv = (serv_t*)0;

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
	    serv_t *serv = findserv(getprovides(script));
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
		    if (del && this) {
			xremove(clink);		/* Found it, remove link */
			if (serv) serv->opts &= ~SERV_ENABLED;
		    }
		}
	    }

	    if (this) {
		/*
		 * If we haven't found it and we shouldn't delete it
		 * we try to add it.
		 */
		if (!del && !found) {
		    xsymlink(olink, nlink);
		    if (serv) serv->opts |= SERV_ENABLED;
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
# else  /* not SUSE but Debian SystemV link scheme */
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
	const char * rcd = (char*)0;
	DIR  * rcdir;

	if ((rcd = map_runlevel_to_location(runlevel)) == (char*)0)
	    continue;
	lvl  = map_runlevel_to_lvl(runlevel);
	seek = map_runlevel_to_seek(runlevel);

	script = (char*)0;
	rcdir = openrcdir(rcd); /* Creates runlevel directory if necessary */
	if (rcdir == (DIR*)0)
	    break;
	pushd(rcd);

	/*
	 * See if we found scripts which should not be
	 * included within this runlevel directory.
	 */
	while ((d = readdir(rcdir)) != (struct dirent*)0) {
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
	    serv_t *serv = findserv(getprovides(script));
	    const boolean stop = (notincluded(script, runlevel) || (serv->lvlk & lvl));
	    const boolean this = chkfor(script, argv, argc);
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
#  endif /* USE_KILL_IN_SINGLE */
		if ((serv->lvlk & lvl) == 0)		/* No default_stop provided */
			continue;
		order = (maxorder + 1) - order;
	    }

	    if ((serv->lvls & lvl) == 0 && (serv->lvlk & lvl) == 0)
		continue;		/* We aren't suppose to be on this runlevel */

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
		    if (del && this) {
			xremove(clink);		/* Found it, remove link */
			if (serv) serv->opts &= ~SERV_ENABLED;
		    }
		}
	    }

	    if (this) {
		/*
		 * If we haven't found it and we shouldn't delete it
		 * we try to add it.
		 */
		if (!del && !found) {
		    xsymlink(olink, nlink);
		    if (serv) serv->opts |= SERV_ENABLED;
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
