#/bin/bash

globalFileName=/tmp/JsCert_run_tests.tmp

if [[ $1 == '-init' ]]
then
	printf '' > $globalFileName
	exit 0
fi

function end_message {
	sleep 0.1
	printf '\nFailed tests:\n'
	all_failed_tests=`cat $globalFileName`

	if [[ $all_failed_tests == '' ]]
	then
		printf '\tNone\n'
	else
		printf "$all_failed_tests\n"
	fi

	exit 0
}

if [[ $1 == '-makefile' ]]
then
	all_failed_tests=`cat $globalFileName`
	shift

	trap end_message SIGINT
fi

if [[ $1 == '' ]]
then
	printf 'Needs a JavaScript file as argument.\n'
	exit -1
fi

printf "\033[35m$1\033[00m"

# Running the interpreter.
interp/run_js -jsparser interp/parser/lib/js_parser.jar -test_prelude interp/test_prelude.js  -file $1

ret=$?

case $ret in
0) ret=0 ;;
1) ret=1 ;;
*) ret=2 ;;
esac

# 0:  OK
# 1:  Failed
# 2:  Unknown

if
	grep -q '@negative' $1
then
	case $ret in
	0) ret=1 ;;
	1) ret=0 ;;
	*) ;;
	esac
fi

case $ret in
0)
	printf ': \033[32mPassed!\033[00m\n'
	exit 0 ;;
1)
	printf ': \033[31mFailed\033[00m\n'
	printf "\t$1\n" >> $globalFileName
	exit 1 ;;
2)
	printf ': \033[33mAbandon\033[00m\n'
	exit 0 ;;
esac

