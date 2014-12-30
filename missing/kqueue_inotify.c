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
#include <sys/types.h>
#include <sys/wait.h>

#include <assert.h>
#include <errno.h>
#include <limits.h>
#include <poll.h>
#include <signal.h>
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

static void
handle_sigchld() {
	/* Interrupt ppoll */
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
	sigset_t sigmask;
	struct pollfd pfd;
	int pret;
	struct timespec polldelay = {
	    .tv_sec = 0, .tv_nsec = 50 /* ms */ * 1000000
	};

	if (sigprocmask(SIG_SETMASK, NULL, &sigmask) || sigdelset(&sigmask, SIGCHLD))
	    err(1, "failed to build sigmask");

	/* BSD kevent() allows changes to be applied and to wait for events in a
	 * single call, but entr doesn't need this, so do one or the other.
	 */
	if (nchanges > 0) {
		ignored = 0;
		for (n=0; n<nchanges; n++) {
			kev = changelist + (sizeof(struct kevent)*n);

			if (kev->filter == EVFILT_PROC) {
				struct sigaction act;
				sigset_t sset;
				assert(kev->flags == (EV_ADD|EV_ONESHOT));
				assert(kev->fflags == (NOTE_EXIT|NOTE_EXITSTATUS));
				if (sigprocmask(SIG_SETMASK, NULL, &sset) ||
					    sigaddset(&sset, SIGCHLD) ||
					    sigprocmask(SIG_SETMASK, &sset, NULL))
					err(1, "failed to mask SIGCHILD");
				act.sa_flags = 0;
				act.sa_handler = handle_sigchld;
				if (sigemptyset(&act.sa_mask) || sigaction(SIGCHLD, &act, NULL))
					err(1, "failed to set CHILD handler");
				continue;
			}

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
		return 0;
	}

	pfd.fd = kq;
	pfd.events = POLLIN;
	n = 0;
	do {
		if (((pret = ppoll(&pfd, 1, timeout, &sigmask)) == 0)) {
			fprintf(stderr,"ppoll timed out, return\n");
			return 0;
		}

		while (n < nevents) {
			int status;
			pid_t pid;
			if ((pid = waitpid(-1, &status, WNOHANG)) < 1)
				break;
			eventlist[n].ident = pid;
			eventlist[n].filter = EVFILT_PROC;
			eventlist[n].flags = 0;
			eventlist[n].fflags = NOTE_EXIT|NOTE_EXITSTATUS;
			eventlist[n].data = status;
			eventlist[n].udata = NULL;
			n++;
		}

		if (n > 0)
			return n;

	} while(pret < 0);

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
