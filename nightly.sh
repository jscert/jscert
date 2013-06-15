time ./runtests.py --webreport --title t262LS5nightly --note "Nightly run of all test262 and LambdaS5" --dbsave `./test262tests` tests/LambdaS5/unit-tests/*.js tests/JSRefTests/*.js
cd test_data/query_scripts/
runhaskell update_known_passes.hs
runhaskell make_simple_report.hs --querytype=OnlyInteresting --reportname=NightlyInterstingCases --reportcomment="Checking last night's run for aborts and fails which are not caused by known issues"
echo "Remember to move known passes file, and move reports to '-latest'"
