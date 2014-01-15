nb=0
for file in `./test262tests`; do
  prefix=$(( $nb / 9999))
  nb=$(( $nb + 1 )) 
  export BISECT_FILE=bisect_$prefix
  ./runtests.py --interp_path interp/run_jsbisect $file
done
