#/bin/bash

if [[ $1 == '' ]]
then
	printf 'Needs a JavaScript file as argument.\n'
	exit -1
fi

printf "\033[35m$1\033[00m"

if
	interp/run_js -jsparser interp/parser/lib/js_parser.jar -test_prelude interp/test_prelude.js  -file $1
then
	failed=true
else
	failed=false
fi

if
	grep -q '@negative' $1
then
	if [[ $failed == true ]]
	then
		failed=false
	else
		failed=true
	fi
fi

if [[ $failed == true ]]
then
	printf ': \033[32mPassed!\033[00m\n'
else
	printf ': \033[31mFailed\033[00m\n'
	exit -1
fi

