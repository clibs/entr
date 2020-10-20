**WARNING:** This is a (possibly outdated and/or unmaintained) fork of https://github.com/eradman/entr . If you want to install entr, go to the [the original repository](https://github.com/eradman/entr) to get the latest release. Likewise, to file an issue or a pull request, head over to the [the original repository](https://github.com/eradman/entr).

Event Notify Test Runner
========================

A utility for running arbitrary commands when files change. Uses
[kqueue(2)][kqueue_2] or [inotify(7)][inotify_7] to avoid polling.  `entr` was
written to make rapid feedback and automated testing natural and completely
ordinary.

Installation - BSD, Mac OS, and Linux
-------------------------------------

    ./configure
    make test
    make install

To see available build options run `./configure -h`

Installation - Mac OS/Homebrew
------------------------------

    brew install entr

Installation - Ports
--------------------

Available in OpenBSD ports, FreeBSD ports, and pkgsrc under `sysutils/entr`.

Installation - Debian
---------------------

    apt-get install entr

Examples from `man entr`
------------------------

Rebuild a project if source files change, limiting output to the first 20 lines:

    $ find src/ | entr sh -c 'make | head -n 20'

Launch and auto-reload a node.js server:

    $ ls *.js | entr -r node app.js

Clear the screen and run a query after the SQL script is updated:

    $ echo my.sql | entr -p psql -f /_

Rebuild project if a source file is modified or added to the src/ directory:

    $ while sleep 1; do ls src/*.rb | entr -d rake; done

News
----

A release history as well as features in the upcoming release are covered in the
[NEWS][NEWS] file.

License
-------

Source is under and ISC-style license. See the [LICENSE][LICENSE] file for more
detailed information on the license used for compatibility libraries.

[kqueue_2]: http://www.openbsd.org/cgi-bin/man.cgi?query=kqueue&manpath=OpenBSD+Current&format=html
[inotify_7]: http://man.he.net/?section=all&topic=inotify
[NEWS]: http://www.bitbucket.org/eradman/entr/src/default/NEWS
[LICENSE]: http://www.bitbucket.org/eradman/entr/src/default/LICENSE
