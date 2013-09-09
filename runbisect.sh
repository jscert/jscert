nb=0
for file in `./test262tests`; do
  prefix=$(( $nb / 9999))
  nb=$(( $nb + 1 )) 
  export BISECT_FILE=bisect_$prefix
  interp/run_jsbisect -jsparser interp/parser/lib/js_parser.jar -file $file
done


