./runtests.py --webreport --title t262nightly --note "Nightly run of all test262" --dbsave `./test262tests`
cd test_data/query_scripts/
runhaskell update_known_passes.hs
runhaskell make_simple_report.hs --querytype=StdOutErrNotLikeAny --reportname=t2nightlynonknownaborts --reportcomment="Checking last night's run for aborts which are not syntax errors, parser errors or not implemented yet errors"
echo "Remember to move known passes file"
