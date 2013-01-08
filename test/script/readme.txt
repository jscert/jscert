A litte shell script to find test cases we need...
It uses standard shell commands (find, grep, cp...)

--

SYNTAX
  getTests.sh 'dir' 'white_list' 'black_list' 'destination'

---

DESCRIPTION

The script search into 'dir' and subdirectories for *.js files containing
all words listed in text file 'white list' (separated by new line) and
not containing any of the words contained in 'black_list'. 
The files (if any) are then copied into 'destination'.

'dir' can be a 'master' folder containing different test suites, or a particular
subfolder inside a test suite (for example something like, myTestSuite/variables/scope/) 

--

EXAMPLE

Just go to test/script, look what's inside white.txt and black.txt and run this:

	$ ./getTests.sh ../sputnick white.txt black.txt selected_tests/

you should get the following output:

	Files must contains:
  		- 'function'

	Files must not contain:
  		- 'Object'
  		- 'eval'
  		- 'Math'
  		- 'sin'
  		- 'cos'
  		- 'for'
  		- 'switch'

	Found: 
      		76

If you now look inside selected_tests/ you should find a copy of all the files
contained in the sputnik directory (including subdirs) that satisfies the constraint.

Change the content of white.txt and black.txt to change the search criteria.

TIP: add the script to your $PATH so you don't have to write the full path every time!

---	

Feel free to modify or improve it! Or give me some suggestions!

--

Daniele
