#/bin/bash

echo -n -e "\033[35m$1\033[00m"
if
	interp/run_js -jsparser interp/parser/lib/js_parser.jar -test_prelude interp/test_prelude.js  -file $1
then
	echo -e ': \033[32mPassed!\033[00m'
else
	echo -e '\033[31mFailed\033[00m'
fi

