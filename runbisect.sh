for file in `./test262tests`; do
  interp/run_jsbisect -jsparser interp/parser/lib/js_parser.jar -file $file
done


