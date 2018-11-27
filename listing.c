/*
 * listing.c
 *
 * Copyright 2000-2003 Werner Fink, 2000 SuSE GmbH Nuernberg, Germany,
 *				    2003 SuSE Linux AG, Germany.
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

int maxorder = 0;  /* Maximum order of runlevels 0 upto 6 and S */

/* See listing.c for list_t and list_entry() macro */
#define getdir(list)		list_entry((list), struct dir_struct, d_list)
#define getlink(list)		list_entry((list), struct link_struct, l_list)
#define getlinkdir(list)	(list_empty(list) ? NULL : getlink((list)->next)->target)

/*
 * We handle services (aka scripts) as directories because
 * dependencies can be handels as symbolic links therein.
 * A provided service will be linked into a required service.
 * For the general typ of linked list see listing.h.
 */

typedef struct link_struct {
    list_t		l_list;	/* The linked list to other symbolic links */
    struct dir_struct * target;
} link_t;			/* This is a "symbolic link" */

typedef struct dir_struct {
    list_t	      d_list;	/* The linked list to other directories */
    list_t	        link;   /* symbolic links in this directory */
    unsigned int       flags;
    char	      minord;	/* Default order deep if any */
    char	       order;	/* Current order deep */
    char	      * name;
    char	    * script;
    unsigned int	 lvl;
} dir_t;			/* This is a "directory" */

static list_t dirs = { &(dirs), &(dirs) }, * d_start = &dirs;

#define DIR_SCAN	0x00000001
#define DIR_LOOP	0x00000002
#define DIR_ISACTIVE	0x00000004

/*
 * Provide or find a service dir, set initial states and
 * link it into the maintaining if a new one.
 */
static dir_t * providedir(const char * name)
{
    dir_t  * this;
    list_t * ptr;

    list_for_each(ptr, d_start)
	if (!strcmp(getdir(ptr)->name,name))
	    goto out;

    this = (dir_t *)malloc(sizeof(dir_t));
    if (this) {
	list_t * l_start = &(this->link);
	l_start->next = l_start;
	l_start->prev = l_start;
	insert(&(this->d_list), d_start->prev);
	ptr = d_start->prev;
	this->name   = xstrdup(name);
	this->script = NULL;
	this->minord = 1;
	this->order  = 0;
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
static dir_t * findscript(const char * script)
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
static void ln_sf(const char * current, const char * required)
{
    dir_t * target = providedir(current);
    dir_t * dir    = providedir(required);
    list_t * l_start = &(dir->link);
    list_t * dent;
    link_t * this;

    if (target == dir)
	goto out;

    list_for_each(dent, l_start) {
	dir_t * target = getlink(dent)->target;
	if (!strcmp(target->name, current))
	    goto out;
    }

    this = (link_t *)malloc(sizeof(link_t));
    if (this) {
	insert(&(this->l_list), l_start->prev);
	this->target = target;
	goto out;
    }
    error("%s", strerror(errno));
out:
    return;
}

/*
 * Remember loops
 */
static inline boolean remembernode (dir_t * dir)
{
    boolean ret = true;

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

static void __follow (dir_t * dir, dir_t * skip, const int level)
{
    dir_t * tmp;
    register int deep = level;	/* Link depth, maybe we're called recursive */
    register int loop;
    static boolean warned = false;

    if (dir->flags & DIR_SCAN) {
	if (skip) {
	    if (!remembernode(skip) || !remembernode(dir))
		loop_warn_two(dir, skip);
	} else {
	    /* Does this happen? */
	    if (!remembernode(dir))
		loop_warn_one(dir);
	}
	return;
    }

    if (deep < dir->minord)	/* Default order deep of this tree is higher */
	deep = dir->minord;

    if (deep > MAX_DEEP) {
	if (!warned)
	    warn("Max recursions depth %d reached\n",  MAX_DEEP);
	warned = true;
	return;
    }

    for (loop = 0, tmp = dir; tmp; loop++, tmp = getlinkdir(&(tmp->link))) {
	list_t *dent;
	boolean recursion = true;

	if (loop > MAX_DEEP) {
	    if (skip) {
		if (!remembernode(skip) || !remembernode(tmp))
		    loop_warn_two(tmp, skip);
	    } else {
		if (!remembernode(tmp))
		    loop_warn_one(tmp);
	    }
	    break;		/* Loop detected, stop recursion */
	}

	if (!(dir->lvl & tmp->lvl))
	     continue;		/* Not same boot level */

	if (skip && skip == tmp) {
	    if (!remembernode(skip) || !remembernode(tmp))
		loop_warn_one(skip);
	    break;		/* Loop detected, stop recursion */
	}

	/*
	 * As higher the link depth, as higher the start order.
	 */
	if (tmp->order > deep)
	    deep = tmp->order;
	if (tmp->order < deep)
	    tmp->order = deep;

	if (list_empty(&(tmp->link)))
	    break;		/* No further service requires this one */

	/*
	 * Do not count the dependcy deep of the system facilities
	 * but follow them to count the replacing provides.
	 */
	if ((*tmp->name != '$') && (++deep > MAX_DEEP)) {
	    if (!warned)
		warn("Max recursions depth %d reached\n",  MAX_DEEP);
		warned = true;
	    break;
	}

	tmp->flags |= DIR_SCAN; /* Mark this service for loop detection */

	/*
	 * If there are links in the links included, follow them
	 */
	list_for_each(dent, &(tmp->link)) {
	    dir_t * target = getlink(dent)->target;

	    if (!(dir->lvl & target->lvl))
		continue;	/* Not same boot level */

	    if (target == tmp)
		break;		/* Loop avoided */
	
	    if (target == dir)
		break;		/* Loop avoided */
	
	    if (skip && skip == target) {
		if (!remembernode(skip) || !remembernode(tmp))
		    loop_warn_two(skip, tmp);
		recursion = false;
		break;		/* Loop detected, stop recursion */
	    }

	    __follow(target, tmp, deep);	/* The inner recursion */

	    /* Just for the case an inner recursion was stopped */
	    if (loop_check(target) || loop_check(tmp) || loop_check(skip)) {
		recursion = false;
		break;		/* Loop detected, stop recursion */
	    }
	}

	tmp->flags &= ~DIR_SCAN; /* Remove loop detection mark */

	if (!recursion)
	    break;		/* Loop detected, stop recursion */
    }
}

#undef loop_warn_two
#undef loop_warn_one
#undef loop_check

/*
 * Helper for follow_all: start with depth one.
 */
inline static void follow(dir_t * dir)
{
    /* Link depth starts here with one */
    __follow(dir, NULL, dir->minord);
}

/*
 * Put not existing services into a guessed order.
 * The maximal order of not existing services can be
 * set if they are required by existing services.
 */
static void guess_order(dir_t * dir)
{
    register int min = 99, lvl = 0;
    int deep = 0;

    if (dir->script)		/* Skip it because we have read it */
	goto out;

    if (*dir->name == '$')	/* Don't touch our system facilities */
	goto out;

    /* No full loop required because we seek for the lowest order */
    if (!list_empty(&(dir->link))) {
	dir_t * target = getlinkdir(&(dir->link));
	list_t * dent;

	if (min > target->order)
	    min = target->order;

	lvl |= target->lvl;

	list_for_each(dent, &(dir->link)) {
	    dir_t * target = getlink(dent)->target;

	    if (++deep > MAX_DEEP)
		break;

	    if (target == dir)
		break;		/* Loop detected */

	    if (min > target->order)
		min = target->order;

	    lvl |= target->lvl;
	}
	if (min > 1) {		/* Set guessed order of this unknown script */
	    dir->order = min - 1;
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
	follow(getdir(tmp));

    /*
     * Guess order of not installed scripts in comparision
     * to the well known scripts.
     */
    list_for_each(tmp, d_start)
	guess_order(getdir(tmp));

    list_for_each(tmp, d_start) {
	if (!(getdir(tmp)->lvl & LVL_ALL))
	    continue;
	if (maxorder < getdir(tmp)->order)
	    maxorder = getdir(tmp)->order;
    }
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
	    fprintf(stderr, "%.2d %s 0x%.2x (%s)\n",
		   dir->order, dir->script, dir->lvl, dir->name);
	else
	    fprintf(stderr, "%.2d %s 0x%.2x (%%%s)\n",
		   dir->order, dir->name, dir->lvl, *dir->name == '$' ? "system" : "guessed");
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
    unsigned int lvl = 0;

    switch (runlevel) {
	case 0: lvl = LVL_HALT;   break;
	case 1: lvl = LVL_ONE;    break;
	case 2: lvl = LVL_TWO;    break;
	case 3: lvl = LVL_THREE;  break;
	case 4: lvl = LVL_FOUR;   break;
	case 5: lvl = LVL_FIVE;   break;
	case 6: lvl = LVL_REBOOT; break;
#ifdef SUSE
	case 7: lvl = LVL_SINGLE; break;
	case 8: lvl = LVL_BOOT;   break;
#else
	case 7: lvl = LVL_BOOT;   break;
#endif /* not SUSE */

	default:
	    warn("Wrong runlevel %d\n", runlevel);
    }

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
    unsigned int lvl = 0;

    if (!*script)
	tmp  = d_start->next;

    switch (runlevel) {
	case 0: lvl = LVL_HALT;   break;
	case 1: lvl = LVL_ONE;    break;
	case 2: lvl = LVL_TWO;    break;
	case 3: lvl = LVL_THREE;  break;
	case 4: lvl = LVL_FOUR;   break;
	case 5: lvl = LVL_FIVE;   break;
	case 6: lvl = LVL_REBOOT; break;
#ifdef SUSE
	case 7: lvl = LVL_SINGLE; break;
	case 8: lvl = LVL_BOOT;	  break;
#else
	case 7: lvl = LVL_BOOT;	  break;
#endif /* not SUSE */
	default:
	    warn("Wrong runlevel %d\n", runlevel);
    }

    do {
	ret = false;
	if (tmp == d_start)
	    break;
	dir = getdir(tmp);
	ret = true;
	*script = dir->script;
	*order = dir->order;

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

    dir->lvl = str2lvl(lvl);
}

/*
 * Two helpers for runlevel bits and strings.
 */
unsigned int str2lvl(const char * lvl)
{
    char * token, *tmp = strdupa(lvl);
    int num;
    unsigned int ret = 0;

    if (!tmp)
	error("%s", strerror(errno));

    while ((token = strsep(&tmp, delimeter))) {
	if (!*token || strlen(token) != 1)
	    continue;
	if (!strpbrk(token, "0123456sSbB"))
	    continue;

	if (*token == 'S' || *token == 's')
	    num = 7;
	else if (*token == 'B' || *token == 'b')
	    num = 8;
	else
	    num = atoi(token);

	switch (num) {
	    case 0: ret |= LVL_HALT;   break;
	    case 1: ret |= LVL_ONE;    break;
	    case 2: ret |= LVL_TWO;    break;
	    case 3: ret |= LVL_THREE;  break;
	    case 4: ret |= LVL_FOUR;   break;
	    case 5: ret |= LVL_FIVE;   break;
	    case 6: ret |= LVL_REBOOT; break;
#ifdef SUSE
	    case 7: ret |= LVL_SINGLE; break;
	    case 8: ret |= LVL_BOOT;   break;
#else
	    case 7: ret |= LVL_BOOT;   break;
#endif /* not SUSE */
	    default:
		warn("Wrong runlevel %d\n", num);
	}
    }

    return ret;
}

char * lvl2str(const unsigned int lvl)
{
    char str[20], * ptr = str;
    int num;
    unsigned int bit = 0x001;

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
#else
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

    if (dir->minord < order)
	dir->minord = order;		/* Remember lowest default order deep */

    if (dir->order >= dir->minord)	/* Nothing to do */
	goto out;

    if (!recursive) {
	dir->order = dir->minord;
	goto out;
    }

    /*
     * Follow the script and re-calculate the ordering.
     */
    __follow(dir, NULL, dir->minord);

    /*
     * Guess order of not installed scripts in comparision
     * to the well known scripts.
     */
    list_for_each(tmp, d_start)
	guess_order(getdir(tmp));
 
    list_for_each(tmp, d_start) {
	if (!(getdir(tmp)->lvl & LVL_ALL))
	    continue;
	if (maxorder < getdir(tmp)->order)
	    maxorder = getdir(tmp)->order;
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
	order = dir->order;

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
