/* * Copyright (c) 2013 Eric Radman <ericshane@eradman.com>
 *
 * Permission to use, copy, modify, and distribute this software for any
 * purpose with or without fee is hereby granted, provided that the above
 * copyright notice and this permission notice appear in all copies.
 *
 * THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
 * WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
 * MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR
 * ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
 * WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
 * ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF
 * OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
 */

#include <sys/inotify.h>
#include <sys/event.h>

#include <errno.h>
#include <limits.h>
#include <poll.h>
#include <stdio.h>
#include <string.h>
#include <time.h>
#include <unistd.h>

#include "compat.h"

#include "../data.h"

/* globals */

extern WatchFile **files;

/* forwards */

static WatchFile * file_by_descriptor(int fd);

/* utility functions */

static WatchFile *
file_by_descriptor(int wd) {
	int i;

	for (i=0; files[i] != NULL; i++) {
		if (files[i]->fd == wd)
			return files[i];
	}
	return NULL; /* lookup failed */
}

/* interface */

#define EVENT_SIZE (sizeof (struct inotify_event))
#define EVENT_BUF_LEN (32 * (EVENT_SIZE + 16))

/*
 * Conveniently inotify and kqueue ids both have the type `int`
 */
int
kqueue(void) {
	return inotify_init();
}

/*
 * Emulate kqueue(2). Only the flags used in entr.c are considered
 * Returns the number of eventlist structs filled by this call
 */
int
kevent(int kq, const struct kevent *changelist, int nchanges, struct
	kevent *eventlist, int nevents, const struct timespec *timeout) {
	int n;
	int wd;
	WatchFile *file;
	char buf[EVENT_BUF_LEN];
	ssize_t len;
	int pos;
	struct inotify_event *iev;
	u_int fflags;
	const struct kevent *kev;
	int ignored;
	struct pollfd pfd;

	if (nchanges > 0) {
		ignored = 0;
		for (n=0; n<nchanges; n++) {
			kev = changelist + (sizeof(struct kevent)*n);
			file = (WatchFile *)kev->udata;
			if (kev->flags & EV_DELETE) {
				inotify_rm_watch(kq /* ifd */, kev->ident);
				file->fd = -1; /* invalidate */
			}
			else if (kev->flags & EV_ADD) {
				wd = inotify_add_watch(kq /* ifd */, file->fn,
				    IN_CLOSE_WRITE|IN_DELETE_SELF|IN_MODIFY|IN_MOVE_SELF);
				if (wd < 0)
					return -1;
				close(file->fd);
				file->fd = wd; /* replace with watch descriptor */
			}
			else
				ignored++;
		}
		return nchanges - ignored;
	}

	pfd.fd = kq;
	pfd.events = POLLIN;
	if (timeout != 0 && (poll(&pfd, 1, timeout->tv_nsec/1000000) == 0))
		return 0;

	n = 0;
	do {
		pos = 0;
		len = read(kq /* ifd */, &buf, EVENT_BUF_LEN);
		if (len < 0) {
			/* SA_RESTART doesn't work for inotify fds */
			if (errno == EINTR)
				continue;
			else
				perror("read");
		}
		while ((pos < len) && (n < nevents)) {
			iev = (struct inotify_event *) &buf[pos];
			pos += EVENT_SIZE + iev->len;

			#ifdef DEBUG
			fprintf(stderr, "wd: %d mask: 0x%x\n", iev->wd, iev->mask);
			#endif

			/* convert iev->mask; to comparable kqueue flags */
			fflags = 0;
			if (iev->mask & IN_DELETE_SELF) fflags |= NOTE_DELETE;
			if (iev->mask & IN_CLOSE_WRITE) fflags |= NOTE_WRITE;
			if (iev->mask & IN_MOVE_SELF)   fflags |= NOTE_RENAME;
			if (fflags == 0) continue;

			/* merge events if we're not acting on a new file descriptor */
			if ((n > 0) && (eventlist[n-1].ident == iev->wd))
				fflags |= eventlist[--n].fflags;

			eventlist[n].ident = iev->wd;
			eventlist[n].filter = EVFILT_VNODE;
			eventlist[n].flags = 0; 
			eventlist[n].fflags = fflags;
			eventlist[n].data = 0;
			eventlist[n].udata = file_by_descriptor(iev->wd);
			if (eventlist[n].udata)
				n++;
		}
	}
	while ((poll(&pfd, 1, 50) > 0));

	return n;
}
