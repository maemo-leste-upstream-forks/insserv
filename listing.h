/*
 * listing.h
 *
 * Copyright 2000,2008 Werner Fink, 2000 SuSE GmbH Nuernberg, Germany.
 *				    2008 SuSE Linux Products GmbH Nuernberg, Germany
 *
 * This source is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 */

#include <stddef.h>

#if defined(DEBUG) && (DEBUG > 0)
# define __align __attribute__((packed))
#else
# define __align __attribute__((aligned(sizeof(struct list_struct*))))
#endif

typedef struct list_struct {
    struct list_struct * next, * prev;
} __align list_t;

/*
 * Insert new entry as next member.
 */
static inline void insert (list_t *__restrict new, list_t *__restrict here) __attribute__((always_inline,nonnull(1,2)));
static inline void insert (list_t * new, list_t * here)
{
    list_t * prev = here;
    list_t * next = here->next;

    next->prev = new;
    new->next = next;
    new->prev = prev;
    prev->next = new;
}

/*
 * Remove entries, note that the pointer its self remains.
 */
static inline void delete (list_t *__restrict entry) __attribute__((always_inline,nonnull(1)));
static inline void delete (list_t * entry)
{
    list_t * prev = entry->prev;
    list_t * next = entry->next;

    next->prev = prev;
    prev->next = next;
}

static inline void join(list_t *__restrict list, list_t *__restrict head) __attribute__((always_inline,nonnull(1,2)));
static inline void join(list_t * list, list_t * head)
{
    list_t * first = list->next;

    if (first != list) {
	list_t *last = list->prev;
       	list_t *at = head->next;

       	first->prev = head;
       	head->next = first;

       	last->next = at;
       	at->prev = last;
    }
}

static inline int list_empty(list_t *__restrict head) __attribute__((always_inline,nonnull(1)));
static inline int list_empty(list_t * head)
{
        return head->next == head;
}

#define list_entry(ptr, type, member)	({			\
	const typeof( ((type *)0)->member ) *__mptr = (ptr);	\
	((type *)( (char *)(__mptr) - offsetof(type,member) )); })
#define list_for_each(pos, head)	\
	for (pos = (head)->next; pos != (head); pos = pos->next)
#define list_for_each_prev(pos, head)	\
	for (pos = (head)->prev; pos != (head); pos = pos->prev)

typedef enum _boolean {false, true} boolean;
typedef unsigned char uchar;
typedef unsigned short ushort;
typedef unsigned int uint;

extern void follow_all(void);
extern void show_all(void);
extern void requiresl(const char *__restrict this, ...) __attribute__((nonnull(1)));
extern void requiresv(const char *__restrict this, const char *__restrict requires) __attribute__((nonnull(1,2)));
extern void runlevels(const char *__restrict this, const char *__restrict lvl) __attribute__((nonnull(1,2)));
extern uint str2lvl(const char *__restrict lvl) __attribute__((nonnull(1)));
extern char * lvl2str(const uint lvl);
extern int makeprov(const char *__restrict name, const char *__restrict script) __attribute__((nonnull(1,2)));
extern void setorder(const char *__restrict script, const int order, boolean recursive) __attribute__((nonnull(1)));
extern int getorder(const char *__restrict script) __attribute__((nonnull(1)));
extern boolean notincluded(const char *__restrict script, const int runlevel) __attribute__((nonnull(1)));
extern boolean foreach(const char **__restrict script, int *__restrict order, const int runlevel) __attribute__((nonnull(1,2)));
extern void virtprov(const char *__restrict virt, const char *__restrict real) __attribute__((nonnull(1,2)));
extern const char * getscript(const char *__restrict prov) __attribute__((nonnull(1)));
extern const char * getprovides(const char *__restrict script) __attribute__((nonnull(1)));
extern boolean listscripts(const char **__restrict script, const int lvl) __attribute__((nonnull(1)));
extern int maxorder;
extern boolean is_loop_detected(void);

/*
 * Common short cuts
 */
extern const char *const delimeter;
extern void error (const char *__restrict fmt, ...) __attribute__((format(printf,1,2)));
extern void warn (const char *__restrict fmt, ...) __attribute__((format(printf,1,2)));
extern void info (const char *__restrict fmt, ...) __attribute__((format(printf,1,2)));
extern int map_has_runlevels(void);
extern int map_runlevel_to_lvl (const int runlevel);
extern int map_key_to_lvl(const char key);

static inline char * xstrdup(const char *__restrict s) __attribute__((always_inline,nonnull(1)));
static inline char * xstrdup(const char * s)
{
    char * r;
    if (!s)
	error("%s", strerror(EINVAL));
    if (!(r = strdup(s)))
	error("%s", strerror(errno));
    return r;
} 

#define xreset(ptr)	\
	{char * tmp = (char *)ptr; if (ptr && *tmp) free(ptr);} ptr = NULL
#define xremove(x) ({ if ((dryrun ? 0 : (remove(x) < 0))) \
	warn ("can not remove(%s%s): %s\n", rcd, x, strerror(errno)); \
	else \
	info("remove service %s/%s%s\n", path, rcd, x); })
#define xsymlink(x,y) ({ if ((dryrun ? 0 : (symlink(x, y) < 0))) \
	warn ("can not symlink(%s, %s%s): %s\n", x, rcd, y, strerror(errno)); \
	else \
	info("enable service %s -> %s/%s%s\n", x, path, rcd, y); })

/*
 * Bits of the runlevels
 */
#define LVL_HALT	0x0001
#define LVL_ONE		0x0002
#define LVL_TWO		0x0004
#define LVL_THREE	0x0008
#define LVL_FOUR	0x0010
#define LVL_FIVE	0x0020
#define LVL_REBOOT	0x0040
#define LVL_SINGLE	0x0080
#define LVL_BOOT	0x0100

/*
 * LVL_BOOT is already done if one of the LVL_ALL will be entered.
 */
#define LVL_ALL		(LVL_HALT|LVL_ONE|LVL_TWO|LVL_THREE|LVL_FOUR|LVL_FIVE|LVL_REBOOT|LVL_SINGLE)

/*
 * Normal runlevels which are _direct_ available by shutdown/reboot/halt
 */
#define LVL_NORM	(LVL_HALT|LVL_ONE|LVL_TWO|LVL_THREE|LVL_FOUR|LVL_FIVE|LVL_REBOOT)
