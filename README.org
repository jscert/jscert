#+INCLUDE: "common.org"

* README
  :PROPERTIES:
  :CUSTOM_ID: mainbody
  :END:

** Installation

*** The easy way

    You can download a VM pre-loaded with JSCert and all our
    dependencies [[http://jscert.org/jscertvm.ova][here]]. That VM is in [[http://en.wikipedia.org/wiki/Open_Virtualization_Format][Open Virtualization Format]], and
    should work with your favourite VM package.

*** The developer option

    You can get the latest source from [[https://github.com/jscert/jscert][here]].

    JSCert depends on:
    - Coq (version 8.4.6)
	- OCaml (version 4 or above minimum, 4.02 or above for all optional features to build)
    - Java (for the parser)

    In addition, in order to run the Test262 tests, and query the
    results you will need:
    - Python
    - Haskell
    - SqlLite
    
    Note: JSCert is not fully supported on 32-bit Linux platforms due to floating point extended precision problems.

**** Basic Install
      First, get java. On Ubuntu, this looks something like this:

#+begin_src sh
sudo apt-get install openjdk-6-jre
#+end_src

      Mac and windows users can get Java from [[http://www.java.com/en/download/index.jsp][here]].

      Now you need OCaml (>4.0) and Coq. The easiest way to get these
      is to use opam tool. You can get it with Ubuntu like this:

#+begin_src sh
add-apt-repository ppa:avsm/ocaml42+opam12
apt-get update
apt-get install opam
#+end_src

      Other platforms can download from [[http://opam.ocamlpro.com/][here]].

      Once you have opam, you can install OCaml and Coq:

#+begin_src sh
opam init
opam switch 4.02.3
make init
#+end_src

      Now you can build JSCert:
#+begin_src sh
make
#+end_src

      Note that the following error is normal and can
      be ignored:

#+begin quote
Warning: The following logical axioms were encountered:
 binds_equiv_read binds_rem binds_rem_inv indom_equiv_binds
not_indom_rem.
Having invalid logical axiom in the environment when extracting
may lead to incorrect or non-terminating ML terms.
#+end quote

   This is because, as reported in [[http://www.doc.ic.ac.uk/~gds/jscert_popl14.pdf][the paper]], we have not yet proved
   correctness for all the native libraries.

   You can now explore any of the Coq files in JSCert using [[http://proofgeneral.inf.ed.ac.uk/][Proof
   General]], or if you wish to use [[http://coq.inria.fr/cocorico/CoqIde][CoqIDE]] you can run:

#+begin_src sh
./open.sh &
#+end_src

   If you make changes, you should do the following to re-build:

#+begin_src sh
make clean
make
#+end_src

**** Testing Install

      In order to be able to run tests (for example the Test262 tests)
      using JSRef, you will also need python. Ubuntu users can do:

#+begin_src sh
sudo apt-get install python
#+end_src

      Everyone else can download from [[http://python.org/download/][here]].

      This is enough to simply run the tests, and see results printed
      to your console. If you would also like to generate a
      pretty-printed web page containing the results of a given test
      run, you will need the pystache library. You can install this
      using pip, which Ubuntu users can get with apt:
#+begin_src sh
sudo apt-get install python-pip
#+end_src

      And others can get from [[http://www.pip-installer.org/en/latest/installing.html][here]]. To install pystache:

#+begin_src sh
pip install --user pystache
#+end_src

      If you plan to develop the interpreter, you may wish to
      saving the results of your test runs (which can be quite
      lengthy) to query later. For this, you will need SQLLite, and
      haskell. Ubuntu users can do:
#+begin_src sh
sudo apt-get install cabal-install sqlite3
#+end_src

      And others can get SQLLite [[http://www.sqlite.org/download.html][here]], and Haskell [[http://www.haskell.org/platform/][here]].

      Everyone should do:

#+begin_src sh
cabal update
cabal install cabal-dev
#+end_src


** How to read JSCert

Our development is described in details [[http://jscert.org/dvpt.html][on this page]].

*** Why are some things marked "Admitted" ?

    JSCert is a large project, and can take some time to build.
    Fortunately, there are some simple tricks we regularly use to make
    best use of our developers time. For example: a consequence of the
    Coq compilation strategy is that a great many checks are only
    performed when the compiler or IDE encounters a =Qed= line. In a
    project with only a few definitions, the difference is negligible,
    but in JSCert, we find compilation is significantly faster during
    our regular developments if we replace most of the =Qed= lines of
    our proofs with =Admitted= lines. When working on a particular
    lemma, we will check that the =Qed= works with that lemma, and
    will assume the rest of the project. Every so often we run a
    script which replaces all these =Admitted= lines with =Qed=, and
    we check the integrity of the project as a whole.

    Since our github repository contains work-in-progress, there are
    often =Admitted= lines in there which would pass =Qed= checks, but
    which are as they are to speed up our regular working build
    process.

    It is possible to run a build with proofs enabled using the "proof"
    Makefile target. Beware that it will patch the coq sourcefiles as
    described above, so it is strongly recommended to only do this with
    a clean repository checkout.

#+begin_src sh
make proof
#+end_src

**** Can I trust the parser?

     We do not attempt to specify a JavaScript parser as a part of the
     JSCert project. In order to properly specify the =eval=
     construct, we appeal to a perfect parsing oracle:

#+begin_src coq
  | red_spec_call_global_eval_1_string_parse : forall s p S C bdirect o, (* Step 3 and 5 *)
      parse s (Some p) ->
      red_expr S C (spec_entering_eval_code bdirect (funcbody_intro p s) (spec_call_global_eval_2 p)) o ->
      red_expr S C (spec_call_global_eval_1 bdirect s) o
#+end_src

     This rule says that /if/ we can prove that parsing the string =s=
     can result in some parsed AST =p= then we may continue our
     computation using that AST in the =spec_entering_eval_code=
     intermediate form.

     Since we have not attempted to specify a JavaScript parser, we do
     not currently provide any rules which can be used to prove that
     any given string parses to any given AST. Instead, we require
     that users of JSCert explicitly assume whatever they need to
     assume about their parser.

     Of course, for the JSRef interpreter we cannot assume an oracle.
     Instead, we use an off-the-shelf parser. We chose to use the
     parser from [[https://code.google.com/p/closure-compiler/][Google Closure]], but any other parser would also work.

     This means that you can trust the JSRef interpreter only as much
     as you trust the Google Closure parser, and you can trust any
     proofs you build on JSCert only as much as you trust whatever
     parsing assumptions you explicitly make.

     Currently, none of the proofs in JSCert assume anything about the
     parser, other than that one exists.

** Testing

*** How to run tests

    For testing the JSRef interpreter, we provide a test script
    =runtests.py=. You can get help on the various options it provides
    in the usual way:

#+begin_src sh
./runtests.py --help
#+end_src

    The simplest way to run the Test262 suite is to build JSCert, and
    then type:

#+begin_src sh
./runtests.py `./test262tests`
#+end_src

    The command above will run all the tests in the Test262 suite, and
    print a pass/fail result for each test. If you would like to
    collate those results into a pretty HTML page in
    =./test_reports/=, you can do the following:

#+begin_src sh
./runtests.py --webreport `./test262tests`
#+end_src

    Whether you generate a pretty HTML page or not, both the above
    commands will run /all/ the Test262 tests, including the ones we
    fully expect to fail (for example, tests which rely on libraries
    we have not yet implemented). We provide a list of tests that we
    do not expect to fail in =test_data/interesting_tests.txt=. You
    can run just these tests like so:

#+begin_src sh
./runtests.py --webreport --title=FullRun `cat ./test_data/interesting_tests.txt`
#+end_src

    You don't have to trust our estimation of which tests are
    interesting however. You can save the results of your test run to
    a local database file, and run queries that make sense to you.
    This is described in the next section.

*** Queries: What tests mean

    In order to be able to run a batch of Test262 tests, and analyse the
    results later, there is a selection of scripts available in
    =test_data/query_scripts=. They should be built
    like so:

#+begin_src sh
cd test_data/query_scripts
cabal-dev install
#+end_src

    You can now create a test database, and save the results of a test
    run to it:

#+begin_src sh
cd ..
./createDB.sh
cd ..
./runtests.py --dbsave `./test262tests`
#+end_src

    The query binaries are created in the directory
    =test_data/query_scripts/cabal-dev/bin/=. The most useful of these
    is =make_simple_report= which can be used to produce a report (in
    =./test_reports/=) of all the test runs that meet our criteria of
    being "interesting".

#+begin_src sh
cabal-dev/bin/make_simple_report --querytype=OnlyInteresting --reportname=Interesting
#+end_src

    Our interpreter prints warnings when it detects a feature that we
    haven't yet implemented being accessed. This filter simply
    discounts all tests which trip these warnings.

    You can do more sophisticated things with these filters too. For
    example, you can filter using the test run output to StdErr or
    StdOut. And you can define arbitrary groups of tests using the
    =manage_test_group= and =make_group_by_content= scripts, and then
    explicitly include or exclude tests in those groups.

    At the time this document is being written, we pass all the tests
    we expect to. That is to say, all tests which do not trip warnings
    that unimplemented features are being exercised. Of course, just
    because we pass the tests, that does not necessarily imply we pass
    them for the right reasons! This is especially a problem with
    "negative" tests, which are expected to fail in a particular way,
    for a particular reason. For example, a test which checks that
    "with" statements are not permitted within strict mode functions
    may expect a =SyntaxError=. However, if the
    implementation were to incorrectly reject /all/ instances of
    "with", or even to spuriously reject some other perfectly legal
    syntax, the test would pass, even though the behaviour is clearly
    at fault.

    If you require a stronger guarantee
    about the correctness of JSRef, see the correctness proof against
    the JSCert semantics.

*** Bisect

    To test coverage of one program or a series of test, we also support
    the [[http://bisect.x9c.fr/][Bisect]] tool. Here is how to use it.

    First, install the bisect dependancy and build the bisect version of
    the interpreter.

#+BEGIN_SRC sh
opam install bisect
make interp/run_jsbisect
#+END_SRC

    Next, run the programs using the bisect-ready version of the
    interpreter:

#+BEGIN_SRC sh
for file in $FILE_LIST; do
  ./runtests.py --interp_path interp/run_jsbisect $file
done
#+END_SRC

    This will create as many ~bisectXXXX.out~ files as there are files
    that are run.

    Then to build a report using these run, you need to:

#+BEGIN_SRC sh
make report
#+END_SRC

    This will create a report in the ~report~ subdirectory (deleting any
    previous report that is there) and try to open it using a web
    browser. This will also delete the ~bisectXXXX.out~ files.

    If you need to run bisect with more than 10000 files, you will need
    to set the ~BISECT_FILE~ environment variable at some point (as by
    default the number of output files is limited at 10000). We provide
    a shell script to run every test262 test, called ~runbisect.sh~,
    which illustrates how to do so:

#+BEGIN_SRC sh
nb=0
for file in `./test262tests`; do
  prefix=$(( $nb / 9999))
  nb=$(( $nb + 1 ))
  export BISECT_FILE=bisect_$prefix
  ./runtests.py --interp_path interp/run_jsbisect $file
done
#+END_SRC

*** Under the hood: How tests work

    Since we are currently focused on the core language, JSRef does
    not implement any IO features. We can run any program to
    completion, and inspect the final state and return value of that
    program, but we cannot interact with the program while it is running.

    In order to run Test262 tests, we are required to provide a
    function =$ERROR(str)=, which should record that a test has failed
    for the reason given in the string =str=, and a function
    =runTestCase(f)=, which should run the function =f=, and interpret
    a =false= return value as failure. We implement these functions by
    storing the reason for a given test failure in the special
    distinguished global variable =__$ERROR__=. When any given test
    has been run to completion, we inspect the final state and look
    for the global variable =__$ERROR__=. If it has any value at all,
    we assume the test has failed, and we print that value to
    =stdout=. You can see how we implement the likes of =$ERROR(str)=
    in the file =src/core/trunk/interp/test_prelude.js=
