#!/bin/sh
#
# Copyright (c) 2012 Eric Radman <ericshane@eradman.com>
#
# Permission to use, copy, modify, and distribute this software for any
# purpose with or without fee is hereby granted, provided that the above
# copyright notice and this permission notice appear in all copies.
#
# THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
# WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
# MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR
# ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
# WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
# ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF
# OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.

# test runner

typeset -i tests=0

function try { let tests+=1; this="$1"; }
trap 'printf "$0: exit code $? on line $LINENO\nFAIL: $this\n"; exit 1' ERR

function assert {
	[[ "$1" == "$2" ]] && { printf "."; return; }
	printf "\nFAIL: $this\n'$1' != '$2'\n"; exit 1
}
function skip { printf "s"; }

function zz { sleep 0.25; }
function setup { rm -f $tmp/*; touch $tmp/file{1,2}; zz; }
system_tmp=$(cd /tmp; pwd -P)
tmp=$(cd $(mktemp -d $system_tmp/entr_system_test.XXXXXXXXXX); pwd -P)

# rebuild

[ -f entr ] || {
	./configure
	make clean
	make
}

# required utilities

utils="hg vim"
for util in $utils; do
	p=$(which $util 2> /dev/null) || {
		echo "ERROR: could not locate the '$util' utility" >&2
		echo "System tests depend on the following: $utils" >&2
		exit 1
	}
done

# tests

try "no arguments"
	./entr 2> /dev/null || code=$?
	assert $code 1

try "reload and clear options with no utility to run"
	./entr -r -c 2> /dev/null || code=$?
	assert $code 1

try "empty input"
	echo "" | ./entr echo 2> /dev/null || code=$?
	assert $code 1

try "no regular files provided as input"
	mkdir $tmp/dir1
	ls $tmp | ./entr echo 2> /dev/null || code=$?
	rmdir $tmp/dir1
	assert $code 1

try "exec single shell utility and exit when a file is added to an implicit watch path"
	setup
	ls $tmp/file* | ./entr -d sh -c 'echo ping' >$tmp/exec.out 2>$tmp/exec.err \
	    || true &
	bgpid=$! ; zz
	touch $tmp/newfile
	wait $bgpid
	assert "$(cat $tmp/exec.out)" "ping"
	assert "$(cat $tmp/exec.err)" "entr: directory altered"

try "exec single shell utility and exit when a file is added to a specific path"
	setup
	ls -d $tmp | ./entr -d sh -c 'echo ping' >$tmp/exec.out 2>$tmp/exec.err \
	    || true &
	bgpid=$! ; zz
	touch $tmp/newfile
	wait $bgpid
	assert "$(cat $tmp/exec.out)" "ping"
	assert "$(cat $tmp/exec.err)" "entr: directory altered"

try "do nothing when a file not monitored is changed in directory watch mode"
	setup
	ls $tmp/file2 | ./entr -d echo "changed" >$tmp/exec.out 2>$tmp/exec.err &
	bgpid=$! ; zz
	echo "123" > file1
	kill -INT $bgpid
	wait $bgpid
	assert "$(cat $tmp/exec.out)" ""
	assert "$(cat $tmp/exec.err)" ""

try "exec utility when a file is written by Vim in directory watch mode"
	setup
	ls $tmp/file* | ./entr -d echo "changed" >$tmp/exec.out 2>$tmp/exec.err &
	bgpid=$! ; zz
	vim -e -s -u NONE -N \
	    -c ":r!date" \
	    -c ":wq" $tmp/file1 ; zz
	kill -INT $bgpid
	wait $bgpid
	assert "$(cat $tmp/exec.out)" "changed"
	assert "$(cat $tmp/exec.err)" ""

try "exec utility when a file is opened for write and then closed"
	setup
	echo "---" > $tmp/file1
	ls $tmp/file* | ./entr echo "changed" > $tmp/exec.out &
	bgpid=$! ; zz
	: > $tmp/file1 ; zz
	kill -INT $bgpid
	wait $bgpid
	if [ $(uname | egrep 'Darwin|FreeBSD|DragonFly') ]; then
		skip "NOTE_TRUNCATE not supported"
	else
		assert "$(cat $tmp/exec.out)" "changed"
	fi

try "exec single utility when an entire stash of files is reverted"
	setup
	cp /usr/include/*.h $tmp/
	cd $tmp
	hg init
	hg add *.h
	hg commit -u "regression" -m "initial checkin"
	for f in `ls *.h`; do
		chmod 644 $f
		echo "" >> $f
	done
	cd - > /dev/null ; zz
	ls $tmp/*.h | ./entr echo "changed" > $tmp/exec.out &
	bgpid=$! ; zz
	cd $tmp
	hg revert *.h
	cd - > /dev/null ; zz
	kill -INT $bgpid
	wait $bgpid
	assert "$(cat $tmp/exec.out)" "changed"

try "exec utility when a file is written by Vim"
	setup
	ls $tmp/file* | ./entr echo "changed" > $tmp/exec.out &
	bgpid=$! ; zz
	vim -e -s -u NONE -N \
	    -c ":r!date" \
	    -c ":wq" $tmp/file1 ; zz
	kill -INT $bgpid
	wait $bgpid
	assert "$(cat $tmp/exec.out)" "changed"

try "exec shell utility when a file is written by Vim with 'backup'"
	setup
	ls $tmp/file* | ./entr echo "changed" > $tmp/exec.out &
	bgpid=$! ; zz
	vim -e -s -u NONE -N \
	    -c ":set backup" \
	    -c ":r!date" \
	    -c ":wq" $tmp/file1 ; zz
	kill -INT $bgpid
	wait $bgpid
	assert "$(cat $tmp/exec.out)" "changed"

try "exec shell utility when a file is written by Vim with 'nowritebackup'"
	setup
	ls $tmp/file* | ./entr echo "changed" > $tmp/exec.out &
	bgpid=$! ; zz
	vim -e -s -u NONE -N \
	    -c ":set nowritebackup" \
	    -c ":r!date" \
	    -c ":wq" $tmp/file1 ; zz
	kill -INT $bgpid
	wait $bgpid
	assert "$(cat $tmp/exec.out)" "changed"

try "restart a server when a file is modified"
	setup
	echo "started." > $tmp/file1
	ls $tmp/file2 | ./entr -r tail -f $tmp/file1 2> /dev/null > $tmp/exec.out &
	bgpid=$! ; zz
	assert "$(cat $tmp/exec.out)" "started."
	echo 456 >> $tmp/file2 ; zz
	kill -INT $bgpid
	wait $bgpid
	assert "$(cat $tmp/exec.out)" "$(printf 'started.\nstarted.')"

try "exit with no action when restart and dirwatch flags are combined"
	setup
	echo "started." > $tmp/file1
	ls $tmp/file* | ./entr -rd tail -f $tmp/file1 2> /dev/null > $tmp/exec.out &
	bgpid=$! ; zz
	assert "$(cat $tmp/exec.out)" "started."
	touch $tmp/newfile
	kill -INT $bgpid
	wait $bgpid
	assert "$(cat $tmp/exec.out)" "$(printf 'started.')"

try "exec single shell utility when two files change simultaneously"
	setup
	ln $tmp/file1 $tmp/file3
	ls $tmp/file* | ./entr sh -c 'echo ping' > $tmp/exec.out &
	bgpid=$! ; zz
	echo 456 >> $tmp/file1 ; zz
	kill -INT $bgpid
	wait $bgpid
	assert "$(cat $tmp/exec.out)" "ping"

try "exec using subsituting changed file argument"
	setup
	ls $tmp/file* | ./entr cat /_ > $tmp/exec.out &
	bgpid=$! ; zz
	echo 123 >> $tmp/file1
	echo 456 >> $tmp/file2 ; zz
	kill -INT $bgpid
	wait $bgpid
	assert "$(cat $tmp/exec.out)" "123"

try "read each filename from a named pipe as they're modified"
	setup
	ls $tmp/file* | ./entr +$tmp/notify &
	bgpid=$! ; zz
	cat $tmp/notify > $tmp/namedpipe.out &
	echo 123 >> $tmp/file1 ; zz
	echo 789 >> $tmp/file2 ; zz
	kill -INT $bgpid
	wait $bgpid
	assert "$(cat $tmp/namedpipe.out | sed 's/.*\///')" "$(printf 'file1\nfile2')"

try "ensure that events are consolodated when writing to a named pipe"
	setup
	ls $tmp/file* | ./entr +$tmp/notify &
	bgpid=$! ; zz
	cat $tmp/notify > $tmp/namedpipe.out &
	mv $tmp/file1 $tmp/_file1 ; zz
	mv $tmp/_file1 $tmp/file1 ; zz
	kill -INT $bgpid
	wait $bgpid
	assert "$(cat $tmp/namedpipe.out | sed 's/.*\///')" "$(printf 'file1')"

try "read each filename from a named pipe until a file is removed"
	setup
	ls $tmp/file* | ./entr +$tmp/notify 2> /dev/null || code=$? &
	bgpid=$! ; zz
	cat $tmp/notify > $tmp/namedpipe.out &
	echo 123 >> $tmp/file1 ; zz
	rm $tmp/file2 ; zz
	kill -INT $bgpid
	wait $bgpid
	assert "$(cat $tmp/namedpipe.out | sed 's/.*\///')" "$(printf 'file1')"
	assert $code 1

try "exec single shell utility using utility substitution"
	setup
	ls $tmp/file1 $tmp/file2 | ./entr file /_ > $tmp/exec.out &
	bgpid=$! ; zz
	echo 456 >> $tmp/file2; zz
	kill -INT $bgpid
	wait $bgpid
	assert "$(cat $tmp/exec.out)" "$tmp/file2: ASCII text"

try "watch and exec a program that is overwritten"
	setup
	touch $tmp/script; chmod 755 $tmp/script
	echo $tmp/script | ./entr $tmp/script $tmp/file1 > $tmp/exec.out &
	bgpid=$! ; zz
	cat > $tmp/script <<-EOF
	#!/bin/sh
	echo vroom
	EOF
	zz ; kill -INT $bgpid
	wait $bgpid
	assert "$(cat $tmp/exec.out)" "vroom"

tty > /dev/null && {
try "exec an interactive utility when a file changes"
	setup
	ls $tmp/file* | ./entr sh -c 'tty | colrm 9; sleep 0.3' > $tmp/exec.out &
	bgpid=$! ; zz
	echo 456 >> $tmp/file2 ; zz
	kill -INT $bgpid
	wait $bgpid
	assert "$(cat $tmp/exec.out | tr '/pts' '/tty')" "/dev/tty"
}

# cleanup
rm -r $tmp

echo; echo "$tests tests PASSED"
exit 0
