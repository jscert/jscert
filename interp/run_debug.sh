#!/bin/bash

ocamldebug -I interp -I interp/src -I interp/src/extract interp/run_js.byte -jsparser interp/parser/lib/js_parser.jar -test_prelude interp/test_prelude.js -file $*

