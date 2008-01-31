/*
 * listing.c
 *
 * Copyright 2000-2008 Werner Fink, 2000 SuSE GmbH Nuernberg, Germany,
 *				    2003 SuSE Linux AG, Germany.
 *			       2007-2008 SuSE Linux Products GmbH Nuernberg, Germany
 *
 * This source is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 */

#include <string.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdarg.h>
#include <errno.h>
#include <limits.h>
#include <sys/types.h>
#include <ctype.h>
#include "listing.h"

#define MAX_DEEP 99

int maxorder = 0;  		/* Maximum order of runlevels 0 upto 6 and S */

/* See listing.c for list_t and list_entry() macro */
#define getdir(list)		list_entry((list), struct dir_struct, d_list)
#define getlink(list)		list_entry((list), struct link_struct, l_list)
#define getnextlink(list)	(list_empty(list) ? (dir_t*)0 : getlink((list)->next)->target)

/*
 * We handle services (aka scripts) as directories because
 * dependencies can be handels as symbolic links therein.
 * A provided service will be linked into a required service.
 * For the general type of linked lists see listing.h.
 */

typedef struct link_struct {
    list_t		l_list;	/* The linked list of symbolic links */
    struct dir_struct * target;
} __align link_t;		/* This is a "symbolic link" */

typedef struct dir_struct {
    list_t	      d_list;	/* The peg into linked list to other directories */
    list_t	      s_link;   /* The linked list of symbolic start links in this directory */
    list_t	      k_link;   /* The linked list of symbolic stop links in this directory */
    ushort		 lvl;
    ushort	       flags;
    uchar	    minstart;	/* Default start deep if any */
    uchar	       start;	/* Current start deep */
    uchar	     minstop;	/* Default stop  deep if any */
    uchar		stop;	/* Current stop  deep */
    char	      * name;
    char	    * script;
} __align dir_t;		/* This is a "directory" */

/*
 * The linked list off all directories, note that the d_list
 * entry within the dir_struct is used as the peg pointer.
 */
static list_t dirs = { &(dirs), &(dirs) }, * d_start = &dirs;

#define DIR_SCAN	0x0001
#define DIR_LOOP	0x0002
#define DIR_ISACTIVE	0x0004
#define DIR_LOOPREPORT	0x0008
#define DIR_MAXDEEP	0x0010

/*
 * Provide or find a service dir, set initial states and
 * link it into the maintaining if a new one.
 */
static dir_t * providedir(const char *__restrict name) __attribute__((nonnull(1)));
static dir_t * providedir(const char * name)
{
    dir_t  * this;
    list_t * ptr;

    list_for_each(ptr, d_start) {
	if (!strcmp(getdir(ptr)->name,name))
	    goto out;
    }

    this = (dir_t *)malloc(sizeof(dir_t));
    if (this) {
	list_t * l_start = &(this->s_link);
	list_t * l_stop  = &(this->k_link);
	insert(&(this->d_list), d_start->prev);
	l_start->next = l_start;
	l_start->prev = l_start;
	l_stop->next = l_stop;
	l_stop->prev = l_stop;
	ptr = d_start->prev;
	this->name   = xstrdup(name);
	this->script = NULL;
	this->minstart = 1;
	this->minstop  = MAX_DEEP;
	this->start  = 0;
	this->stop   = 0;
	this->flags  = 0;
	this->lvl    = 0;
	goto out;
    }
    ptr = NULL;
    error("%s", strerror(errno));
out:
    return getdir(ptr);
}

/*
 * Find a service dir by its script name.
 */
static inline dir_t * findscript(const char *__restrict script) __attribute__((always_inline,nonnull(1)));
static inline dir_t * findscript(const char * script)
{
    dir_t  * this = NULL;
    list_t * ptr;
    register boolean found = false;

    list_for_each(ptr, d_start) {
	dir_t * tmp = getdir(ptr);

	if (!tmp->script)
	    continue;

	if (!strcmp(tmp->script,script)) {
	    found = true;
	    break;
	}
    }

    if (found)
	this = getdir(ptr);

    return this;
}

/*
 * Link the current service into the required service.
 * If the services do not exist, they will be created.
 */
static void ln_sf(const char *__restrict current, const char *__restrict required) __attribute__((nonnull(1,2)));
static void ln_sf(const char * current, const char * required)
{
    dir_t * cur = providedir(current);
    dir_t * req = providedir(required);
    list_t * l_list = &(req->s_link);
    list_t * dent;
    link_t * this;

    if (cur == req)
	goto out;

    list_for_each(dent, l_list) {
	dir_t * target = getlink(dent)->target;
	if (!strcmp(target->name, current))
	    goto out;
    }

    this = (link_t *)malloc(sizeof(link_t));
    if (this) {
	insert(&(this->l_list), l_list->prev);
	this->target = cur;
	goto out;
    }
    error("%s", strerror(errno));
out:
    return;
}

/*
 * Remember loops to warn only once
 */
static inline boolean remembernode (dir_t *__restrict dir) __attribute__((always_inline,nonnull(1)));
static inline boolean remembernode (dir_t * dir)
{
    register boolean ret = true;

    if (dir->flags & DIR_LOOP)
	goto out;

    ret = false;
    dir->flags |= DIR_LOOP;
out:
    return ret;
}

/*
 * Recursively called function to follow all
 * links within a service dir.
 * Just like a `find * -follow' within a directory tree
 * of depth one with cross linked dependencies.
 *
 * Be warned: the direction is naturally reversed.  That
 * means that the most requested services have the lowest
 * order.  In other word, an empty link list of a service
 * indicates that this service has a higher order number.
 */
#if defined(DEBUG) && (DEBUG > 0)
# define loop_warn_two(a,b)	\
	warn("There is a loop between service %s and %s (list:%d)\n", \
	(a)->name, (b)->name, __LINE__)
# define loop_warn_one(a)	\
	warn("There is a loop at service %s (list:%d)\n", \
	(a)->name, __LINE__);
#else
# define loop_warn_two(a,b)	\
	warn("There is a loop between service %s and %s\n", (a)->name, (b)->name)
# define loop_warn_one(a)	\
	warn("There is a loop at service %s\n", (a)->name);
#endif
#define loop_check(a)	\
	((a) && (a)->flags & DIR_LOOP)

static void __follow (dir_t *__restrict dir, dir_t *__restrict skip, const int, const int) __attribute__((noinline,nonnull(1)));
static void __follow (dir_t * dir, dir_t * skip, const int level, const int reportloop)
{
    list_t * l_list = &(dir->s_link);
    uchar * minorder = &(dir->minstart);
    dir_t * tmp;
    register int deep = level;	/* Link depth, maybe we're called recursively */
    register int loop = 0;	/* Count number of links in symbolic list */

    if (dir->flags & DIR_SCAN) {
	if (skip) {
	    if (!remembernode(skip) || !remembernode(dir))
		loop_warn_two(dir, skip);
	} else {
	    /* Does this happen? */
	    if (!remembernode(dir))
		loop_warn_one(dir);
	}
	goto out;
    }

    if (deep < *minorder)	/* Default deep of this tree is higher */
	deep = *minorder;

    if (deep > MAX_DEEP) {
	if ((dir->flags & DIR_MAXDEEP) == 0)
	    warn("Max recursions depth %d for %s reached\n",  MAX_DEEP, dir->name);
	dir->flags |= DIR_MAXDEEP;
	goto out;
    }

    for (tmp = dir; tmp; tmp = getnextlink(l_list)) {
	register boolean recursion = true;
	uchar * order = &(tmp->start);
	list_t * dent;

	if (loop++ > MAX_DEEP) {
	    if (skip) {
		if (!remembernode(skip) || !remembernode(tmp))
		    loop_warn_two(tmp, skip);
	    } else {
		if (!remembernode(tmp))
		    loop_warn_one(tmp);
	    }
	    break;			/* Loop detected, stop recursion */
	}
	l_list = &(tmp->s_link);	/* List of symbolic links for getnextlink() */

	if (!(dir->lvl & tmp->lvl))
	     continue;			/* Not same boot level */

	if (skip && skip == tmp) {
	    if (!remembernode(skip) || !remembernode(tmp))
		loop_warn_one(skip);
	    break;			/* Loop detected, stop recursion */
	}

	/*
	 * As higher the link depth, as higher the start order.
	 */
	if (*order > deep)
	    deep = *order;
	if (*order < deep)
	    *order = deep;

	if (list_empty(l_list))
	    break;			/* No further service requires this one */

	/*
	 * Do not count the dependcy deep of the system facilities
	 * but follow them to count the replacing provides.
	 */
	if ((*tmp->name != '$') && (++deep > MAX_DEEP)) {
	    if ((tmp->flags & DIR_MAXDEEP) == 0)
		warn("Max recursions depth %d reached\n",  MAX_DEEP);
	    tmp->flags |= DIR_MAXDEEP;
	    break;
	}

	tmp->flags |= DIR_SCAN; 	/* Mark this service for loop detection */

	/*
	 * If there are links in the links included, follow them
	 */
	list_for_each(dent, &(tmp->s_link)) {
	    dir_t * target = getlink(dent)->target;

	    if (!(dir->lvl & target->lvl))
		continue;			/* Not same boot level */

	    if (target == tmp)
		break;				/* Loop avoided */
	
	    if (target == dir)
		break;				/* Loop avoided */
	
	    if (skip && skip == target) {
		if (!remembernode(skip) || !remembernode(tmp))
		    loop_warn_two(skip, tmp);
		recursion = false;
		break;				/* Loop detected, stop recursion */
	    }

	    if (target->start >= deep)		/* Nothing new */
		continue;
						/* The inner recursion */
	    __follow(target, tmp, deep, reportloop);

	    /* Just for the case an inner recursion was stopped */
	    if (loop_check(target) || loop_check(tmp) || loop_check(skip)) {
		recursion = false;
		break;				/* Loop detected, stop recursion */
	    }
	}

	tmp->flags &= ~DIR_SCAN; 	/* Remove loop detection mark */

	if (!recursion) {
	    if (reportloop && !(tmp->flags & DIR_LOOPREPORT)) {
		warn(" loop involving service %s at depth %d\n", tmp->name, level);
		tmp->flags |= DIR_LOOPREPORT;
	    }
	    break;			/* Loop detected, stop recursion */
	}
    }
out:
    return;			/* Make compiler happy */
}

#undef loop_warn_two
#undef loop_warn_one
#undef loop_check

/*
 * Helper for follow_all: start with depth one.
 */
static inline void follow(dir_t *__restrict dir, const int reportloop) __attribute__((always_inline,nonnull(1)));
static inline void follow(dir_t * dir, const int reportloop)
{
    /* Link depth starts here with one */
    __follow(dir, NULL, dir->minstart, reportloop);
}

/*
 * Put not existing services into a guessed order.
 * The maximal order of not existing services can be
 * set if they are required by existing services.
 */
static void guess_order(dir_t *__restrict dir) __attribute__((nonnull(1)));
static void guess_order(dir_t * dir)
{
    list_t * l_list = &(dir->s_link);
    register int min = 99, lvl = 0;
    register int deep = 0;

    if (dir->script)		/* Skip it because we have read it */
	goto out;

    if (*dir->name == '$')	/* Don't touch our system facilities */
	goto out;

    /* No full loop required because we seek for the lowest order */
    if (!list_empty(l_list)) {
	dir_t * target = getnextlink(l_list);
	uchar * order = &(target->start);
	list_t * dent;

	if (min > *order)
	    min = *order;

	lvl |= target->lvl;

	list_for_each(dent, &(dir->s_link)) {
	    dir_t * target = getlink(dent)->target;
	    uchar * order = &(target->start);

	    if (++deep > MAX_DEEP)
		break;

	    if (target == dir)
		break;		/* Loop detected */

	    if (min > *order)
		min = *order;

	    lvl |= target->lvl;
	}
	if (min > 1) {		/* Set guessed order of this unknown script */
	    uchar * order = &(dir->start);
	    *order = min - 1;
	    dir->lvl |= lvl;	/* Set guessed runlevels of this unknown script */
	} else
	    dir->lvl  = LVL_BOOT;
    }
out:
    return;
}

/*
 * Follow all services and their dependencies recursivly.
 */
void follow_all()
{
    list_t *tmp;

    /*
     * Follow all scripts and calculate the main ordering.
     */
    list_for_each(tmp, d_start)
	follow(getdir(tmp), 1);

    /*
     * Guess order of not installed scripts in comparision
     * to the well known scripts.
     */
    list_for_each(tmp, d_start)
	guess_order(getdir(tmp));

    list_for_each(tmp, d_start) {
	if (!(getdir(tmp)->lvl & LVL_ALL))
	    continue;
	if (maxorder < getdir(tmp)->start)
	    maxorder = getdir(tmp)->start;
    }
}

boolean is_loop_detected(void)
{
    list_t *tmp;
    list_for_each(tmp, d_start) {
	dir_t * dir = getdir(tmp);
	if (dir->flags & DIR_LOOPREPORT)
	    return true;
    }
    return false;
}

/*
 * For debuging: show all services
 */
#if defined(DEBUG) && (DEBUG > 0)
void show_all()
{
    list_t *tmp;
    list_for_each(tmp, d_start) {
	dir_t * dir = getdir(tmp);
	if (dir->script)
	    fprintf(stderr, "%.2d %s 0x%.2x '%s' (%s)\n",
		   dir->start, dir->script, dir->lvl, lvl2str(dir->lvl), dir->name);
	else
	    fprintf(stderr, "%.2d %s 0x%.2x '%s' (%%%s)\n",
		   dir->start, dir->name, dir->lvl, lvl2str(dir->lvl), *dir->name == '$' ? "system" : "guessed");
    }
}
#endif

/*
 * Used within loops to get names not included in this runlevel.
 */
boolean notincluded(const char * script, const int runlevel)
{
    list_t *tmp;
    boolean ret = false;
    uint lvl = 0;

    lvl = map_runlevel_to_lvl (runlevel);

    list_for_each(tmp, d_start) {
	dir_t * dir = getdir(tmp);

	if (!dir->script)	/* No such file */
	    continue;

	if (dir->lvl & lvl)	/* Same runlevel */
	    continue;

	if (strcmp(script, dir->script))
	    continue;		/* Not this file */

	ret = true;		/* Not included */
	break;
    }

    return ret;
}

/*
 * Used within loops to get names and order out
 * of the service lists of a given runlevel.
 */
boolean foreach(const char ** script, int * order, const int runlevel)
{
    static list_t * tmp;
    dir_t * dir;
    boolean ret;
    uint lvl = 0;

    if (!*script)
	tmp  = d_start->next;

    lvl = map_runlevel_to_lvl (runlevel);

    do {
	ret = false;
	if (tmp == d_start)
	    break;
	dir = getdir(tmp);
	ret = true;
	*script = dir->script;
	*order = dir->start;

#if defined (IGNORE_LOOPS) && (IGNORE_LOOPS > 0)
	if (dir->flags & DIR_LOOP)
	    *script = NULL;
#endif

	tmp = tmp->next;

    } while (!*script || !(dir->lvl & lvl));

    return ret;
}

/*
 * The same as requiresv, but here we use
 * several arguments instead of one string.
 */
void requiresl(const char * this, ...)
{
    va_list ap;
    char * requires;
    int count = 0;

    va_start(ap, this);
    while ((requires = va_arg(ap, char *))) {
	ln_sf(this, requires);
	count++;
    }
    va_end(ap);
    if (!count)
	providedir(this);
}

/*
 * THIS services REQUIRES that service.
 */
void requiresv(const char * this, const char * requires)
{
    int count = 0;
    char * token, * tmp = strdupa(requires);

    if (!tmp)
	error("%s", strerror(errno));

    while ((token = strsep(&tmp, delimeter))) {
	if (*token)
	    ln_sf(this, token);
	count++;
    }
    if (!count)
	providedir(this);
}

/*
 * Set the runlevels of a service.
 */
void runlevels(const char * this, const char * lvl)
{
    dir_t * dir = providedir(this);

    dir->lvl |= str2lvl(lvl);
}

/*
 * Two helpers for runlevel bits and strings.
 */
uint str2lvl(const char * lvl)
{
    char * token, *tmp = strdupa(lvl);
    uint ret = 0;

    if (!tmp)
	error("%s", strerror(errno));

    while ((token = strsep(&tmp, delimeter))) {
	if (!*token || strlen(token) != 1)
	    continue;
	if (!strpbrk(token, "0123456sSbB"))
	    continue;

        ret |= map_key_to_lvl(*token);
    }

    return ret;
}

char * lvl2str(const uint lvl)
{
    char str[20], * ptr = str;
    int num;
    uint bit = 0x001;

    memset(ptr , '\0', sizeof(str));
    for (num = 0; num < 9; num++) {
	if (bit & lvl) {
	    if (LVL_NORM & bit)
		*(ptr++) = num + 48;
#ifdef SUSE
	    else if (LVL_SINGLE & bit)
		*(ptr++) = 'S';
	    else if (LVL_BOOT & bit)
		*(ptr++) = 'B';
#else  /* not SUSE */
	    else if (LVL_BOOT & bit)
		*(ptr++) = 'S';
#endif /* not SUSE */
	    else
		error("Wrong runlevel %d\n", num);
	    *(ptr++) = ' ';
	}
	bit <<= 1;
    }
    return xstrdup(str);
}

/*
 * Reorder all services starting with a service
 * being in same runlevels.
 */
void setorder(const char * script, const int order, boolean recursive)
{
    dir_t * dir = findscript(script);
    list_t * tmp;

    if (!dir)
	goto out;

    if (dir->minstart < order)
	dir->minstart = order;		/* Remember lowest default order deep */

    if (dir->start >= dir->minstart)	/* Nothing to do */
	goto out;

    if (!recursive) {
	dir->start = dir->minstart;
	goto out;
    }

    /*
     * Follow the script and re-calculate the ordering.
     */
    __follow(dir, NULL, dir->minstart, 0);

    /*
     * Guess order of not installed scripts in comparision
     * to the well known scripts.
     */
    list_for_each(tmp, d_start)
	guess_order(getdir(tmp));
 
    list_for_each(tmp, d_start) {
	if (!(getdir(tmp)->lvl & LVL_ALL))
	    continue;
	if (maxorder < getdir(tmp)->start)
	    maxorder = getdir(tmp)->start;
    }
out:
    return;
}

/*
 * Get the order of a service.
 */
int getorder(const char * script)
{
    dir_t * dir = findscript(script);
    int order = -1;

    if (dir)
	order = dir->start;

    return order;
}

/*
 * Provide a service if the corresponding script
 * was read and the scripts name was remembered.
 * A given script name marks a service as a readed one.
 * One script and several provided facilities leads
 * to the same order for those facilities.
 */
int makeprov(const char * name, const char * script)
{
    dir_t * alias = findscript(script);
    dir_t * dir   = providedir(name);
    int ret = 0;

    if (!dir->script) {
	if (!alias) {
	    dir->script = xstrdup(script);
	} else
	    dir->script = alias->script;
	goto out;
    }

    if (strcmp(dir->script, script))
	ret = -1;
out:
    return ret;
}

/*
 * The virtual facilities provides real services.
 */
void virtprov(const char * virt, const char * real)
{
    char * token, * ptr;
    dir_t * dir = providedir(virt);

    if (!real)
	goto out;

    ptr = strdupa(real);
    if (!ptr)
	error("%s", strerror(errno));

    while ((token = strsep(&ptr, delimeter))) {
	if (*token) {
	    dir_t * tmp;
	    /*
	     * optional real services are noted by a `+' sign
	     */
	    if (*token == '+')
		token++;
	    tmp = providedir(token);
	    ln_sf(virt, token);
	    dir->lvl |= tmp->lvl;
	}
    }

out: 
    if (!dir->lvl)		/* Unknown runlevel means before any runlevel */
	dir->lvl |= LVL_BOOT;
}

/*
 * Find the script name of a provided feature
 */
const char * getscript(const char * prov)
{
    char * script = NULL;
    list_t * ptr;

    list_for_each(ptr, d_start) {
	dir_t * tmp = getdir(ptr);

        if (!strcmp(tmp->name,prov)) {
	    if (tmp->script)
		script = tmp->script;
            break;
	}
    }
    return script;
}

/*
 * List all scripts for given runlevel bit
 */
boolean listscripts(const char ** script, const int lvl)
{
    static list_t * tmp;
    dir_t * dir;
    boolean ret;

    if (!*script)
	tmp  = d_start->next;

    do {
	ret = false;
	if (tmp == d_start)
	    break;
	dir = getdir(tmp);

	ret = true;
	*script = dir->script;

	if (dir->script) {
	    dir_t * chk = findscript(dir->script);
	    if (dir != chk)
		*script = NULL;		/* Duplet */
	}

#if defined (IGNORE_LOOPS) && (IGNORE_LOOPS > 0)
	if (dir->flags & DIR_LOOP)
	    *script = NULL;
#endif

	tmp = tmp->next;

    } while (!*script || !(dir->lvl & lvl));

    return ret;
}

/*
 * Return the provided service of a given script
 */
const char * getprovides(const char * script)
{
    char * prov = NULL;
    dir_t * dir = findscript(script);

    if (dir)
	prov = dir->name;
    return prov;
}
