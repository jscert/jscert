############################################################################
# You can define your own path to COQBIN by creating a file called
# "settings.sh" and placing the right definitions into it, e.g.
#    COQBIN=/var/tmp/charguer/v8.4/bin/
#
# The same applies for the path to tlc, e.g.: TLC=~/tlc/trunk
#
# Note that TLC should have no leading slash, whereas COQBIN should have one.
# Note that if you rebind COQBIN you need to do the same in the TLC folder.
# Note that if you add a settings.sh file, you need to do "make clean" first.

# Default paths for TLC and COQBIN, etc are as follows:

COQBIN=
TLC=lib/tlc
FLOCQ=lib/flocq
FLOCQ_INC=-R $(FLOCQ)/src Flocq

# Define FAST to be non empty for compiling Coq proofs faster
FAST=

LAMBDAS5=~/Documents/data/LambdaS5/tests/s5
SPIDERMONKEY=~/Mozilla/Central/Central/js/src/build_release/js
NODEJS=/usr/bin/nodejs

# Alternative definition for FLOCQ_INC:
# FLOCQ_FOLDERS=$(addprefix $(FLOCQ)/src/,Core Calc Appli Prop)
# FLOCQ_INC=$(addprefix -I ,$(FLOCQ_FOLDERS))

# Edit settings.sh to modify the default paths mentioned above
-include settings.sh


#######################################################

TLC_SRC=$(wildcard $(TLC)/*.v)
TLC_VO=$(TLC_SRC:.v=.vo)

FLOCQ_SRC=$(wildcard $(FLOCQ)/src/*/*.v)
FLOCQ_VO=$(FLOCQ_SRC:.v=.vo)


#######################################################

INCLUDES=-I coq -I $(TLC) $(FLOCQ_INC)
COQC=$(COQBIN)coqc $(INCLUDES)
COQDEP=$(COQBIN)coqdep $(INCLUDES)
OCAMLOPT=ocamlopt
OCAMLC=ocamlc

#######################################################
# MAIN SOURCE FILES

# TODO: rename coq into jscoq

JS_SRC=\
	coq/Shared.v \
	coq/JsNumber.v \
	coq/JsSyntax.v \
	coq/JsSyntaxAux.v \
	coq/JsSyntaxInfos.v \
	coq/JsCommon.v \
	coq/JsCommonAux.v \
	coq/JsPreliminary.v \
	coq/JsInit.v \
	coq/JsInterpreterMonads.v \
	coq/JsInterpreter.v \
        coq/JsInterpreterExtraction.v \
	coq/JsPrettyInterm.v \
	coq/JsPrettyIntermAux.v \
	coq/JsPrettyRules.v \
	coq/JsCorrectness.v


JS_VO=$(JS_SRC:.v=.vo)


# List for files that can be compiled without proofs in FAST=1 mode.

ifneq ($(FAST),)
	FAST_SRC=\
#		coq/Shared.v \
		coq/JsNumber.v \
		coq/JsSyntax.v \
		coq/JsSyntaxAux.v \
		coq/JsSyntaxInfos.v \
		coq/JsCommon.v \
		coq/JsCommonAux.v \
		coq/JsInit.v \
		coq/JsPrettyInterm.v \
		coq/JsPrettyIntermAux.v \
		coq/JsPrettyRules.v
endif

FAST_VO=$(FAST_SRC:.v=.vo)


#######################################################
# EXTENSIONS

.PHONY: all report depend clean
.SUFFIXES: .v .vo

#######################################################
# MAIN TARGETS

all: $(JS_VO) interpreter tags

debug:
	make -f Makefile.debug

report:
	bisect-report -html report bisect*.out
	firefox report/index.html || open report/index.html
	rm bisect*.out

tlc: $(TLC_VO)

flocq: $(FLOCQ_VO)

tags: $(JS_SRC)
	./gentags.sh


#######################################################
# EXTERNAL LIBRARIES: TLC and Flocq

init:
	bash -c "mkdir interp/src/extract" || true
	git submodule init; git submodule update
	svn checkout svn://scm.gforge.inria.fr/svn/tlc/trunk lib/tlc
	tar -xzf lib/flocq-2.1.0.tar.gz
	mv flocq-2.1.0 lib/flocq

# alternative: pull git from svn
#	git clone https://gforge.inria.fr/git/flocq/flocq.git flocq


#######################################################
# FAST COMPILATION TOOL: coqj


# Compile coqj : converts a .v file into a shallow .v file (without proofs)

#coqj: coqj.mll
#	ocamllex coqj.mll
#	ocamlopt -o coqj coqj.ml
#
# Fast compilation of files in $(FAST_SRC)

#define FAST_RULE

#$(1).vo: .depend coqj
#	@mkdir -p _shallow/$(dir $1)
#	./coqj $(1).v > _shallow/$(1).v
#	$(COQC) -dont-load-proofs -I coq -I $(TLC) _shallow/$(1).v
#	mv _shallow/$(1).vo $(1).vo

#endef

#$(foreach filebase,$(FAST_SRC:.v=),$(eval $(call FAST_RULE,$(filebase))))

# "make nofast" : Compilation mode to force the verification of all files

#nofast: $(FAST_VO:.vo=_full.vo)

#%_full.vo : %.v .depend
#	echo $*
#	cp $*.v $*_full.v
#	$(COQC) -dont-load-proofs -I coq -I $(TLC) $*_full.v
#	rm $*_full.v

#######
# Coq Compilation
#######
%.v.d: %.v
	$(COQDEP) $< > $@

include $(JS_SRC:.v=.v.d)

%.vo:
	$(COQC) -dont-load-proofs $<

#######################################################
#######################################################


#######################################################
# SED INSERTION

REFGETVALUE=$(shell cat interp/src/insert/ref_get_value)
REFGETVALUE2=$(shell cat interp/src/insert/ref_get_value2)
RUNOBJECTMETHOD=$(shell cat interp/src/insert/run_object_method)
RUNOBJECTHEAP=$(shell cat interp/src/insert/run_object_heap_set_extensible)
ENVGETIDENTIFIER=$(shell cat interp/src/insert/lexical_env_get_identifier_ref)

coq/JsInterpreterExtraction.vo: coq/JsInterpreterExtraction.v
	$(COQC) -I coq -I $(TLC) $< # The option [-dont-load-proof] would extract all instance to an axiom! -- Martin.
	mv *.ml interp/src/extract/
	mv *.mli interp/src/extract/
	cp interp/src/extract/JsInterpreter.mli interp/src/extract/JsInterpreterBisect.mli
	perl -pe 's|res_res \(run_error s Coq_native_error_ref\)|$(REFGETVALUE)|' interp/src/extract/JsInterpreter.ml > interp/src/extract/JsInterpreter.ml.bak
	perl -pe 's/\(\*\* val run_object_heap_set_extensible :/$(RUNOBJECTMETHOD)/' interp/src/extract/JsInterpreter.ml.bak > interp/src/extract/JsInterpreter.ml
	perl -pe 's/type runs_type =/$(RUNOBJECTHEAP)/' interp/src/extract/JsInterpreter.ml > interp/src/extract/JsInterpreter.ml.bak
	perl -pe 's/    result_val s \(ref_create_value \(Coq_value_prim Coq_prim_undef\) x0 str\)/$(ENVGETIDENTIFIER)/' interp/src/extract/JsInterpreter.ml.bak > interp/src/extract/JsInterpreter.ml
	perl -pe 's|\(\*\* val run_expr_get_value :|$(REFGETVALUE2)|' interp/src/extract/JsInterpreter.ml > interp/src/extract/JsInterpreter.ml.bak
	mv interp/src/extract/JsInterpreter.ml.bak interp/src/extract/JsInterpreter.ml
	perl -pe 's/ impossible/ (*BISECT-IGNORE*) impossible/g' interp/src/extract/JsInterpreter.ml > interp/src/extract/JsInterpreterBisect.ml
	# As there is a second generation f dependancies, you may need to re-call `make' another time to get full compilation working.
	ocamldep -I interp/src/extract/ interp/src/extract/*.ml{,i} >> .depend


#######################################################
# INTERPRETER

run_tests: interpreter
	./runtests.py --no_parasite

run_tests_spidermonkey:
	./runtests.py --spidermonkey --interp_path $(SPIDERMONKEY)

run_tests_lambdaS5:
	./runtests.py --lambdaS5 --interp_path $(LAMBDAS5)

run_tests_nodejs:
	./runtests.py --nodejs --interp_path $(NODEJS)

interpreter: interp/run_js

interp/src/extract/%.ml: coq/JsInterpreterExtraction.vo
	# The following line are here only temporary.  It just replaces all [Coq_result_stuck] generated by Coq by an [assert false], which is much easier to use for debuging purpose. -- Martin.
	perl -pe 's/\([^|][^ ]\)Coq_result_stuck/\1assert false/g' $@ > $@.bak
	mv $@.bak $@

interp/src/extract/%.mli: coq/JsInterpreterExtraction.vo

PARSER_INC=-I $(shell ocamlfind query xml-light) -I interp/src -I interp/src/extract

interp/src/parser_syntax.cmx: interp/parser/src/parser_syntax.ml
	$(OCAMLOPT) -c -o $@ $<

interp/src/parser_syntax.cmo: interp/parser/src/parser_syntax.ml
	$(OCAMLC) -c -o $@ $<

interp/src/pretty_print.cmx: interp/parser/src/pretty_print.ml interp/src/parser_syntax.cmx
	$(OCAMLOPT) $(PARSER_INC) -c -o $@ $<

interp/src/pretty_print.cmo: interp/parser/src/pretty_print.ml interp/src/parser_syntax.cmo
	$(OCAMLC) $(PARSER_INC) -c -o $@ $<

interp/src/parser.cmx: interp/parser/src/parser.ml interp/src/parser_syntax.cmx
	$(OCAMLOPT) $(PARSER_INC) -c -o $@ str.cmxa $<

interp/src/parser.cmo: interp/parser/src/parser.ml interp/src/parser_syntax.cmo
	$(OCAMLC) $(PARSER_INC) -c -o $@ str.cma $<

interp/src/parser_main.cmx: interp/parser/src/parser_main.ml interp/src/parser_main.cmi interp/src/parser.cmx interp/src/pretty_print.cmx
	$(OCAMLOPT) $(PARSER_INC) -c -o $@ $<

interp/src/parser_main.cmo: interp/parser/src/parser_main.ml interp/src/parser_main.cmi interp/src/parser.cmo interp/src/pretty_print.cmo
	$(OCAMLC) $(PARSER_INC) -c -o $@ $<

interp/src/parser_main.cmi: interp/src/parser_main.mli
	$(OCAMLOPT) $(PARSER_INC) -c -o $@ $<

interp/src/extract/JsInterpreterBisect.cmx:
	ocamlfind ocamlopt -package bisect -syntax camlp4o -c -w -20 -I interp/src -I interp/src/extract interp/src/extract/JsInterpreterBisect.mli
	ocamlfind ocamlopt -package bisect -syntax camlp4o -c -w -20 -I interp/src -I interp/src/extract interp/src/extract/JsInterpreterBisect.ml

interp/src/extract/%.cmi: interp/src/extract/%.mli
	$(OCAMLOPT) -c -I interp/src -I interp/src/extract -o $@ $<

interp/src/extract/%.cmx: interp/src/extract/%.ml interp/src/extract/%.cmi
	$(OCAMLOPT) -c -w -20 -I interp/src -I interp/src/extract -o $@ $<

interp/src/extract/%.cmo: interp/src/extract/%.ml interp/src/extract/%.cmi
	$(OCAMLC) -c -w -20 -I interp/src -I interp/src/extract -o $@ $<

interp/src/translate_syntax.cmi: interp/src/translate_syntax.mli interp/src/extract/JsSyntax.cmi
	$(OCAMLOPT) -c -I interp/src -I interp/src/extract -o $@ $<

interp/src/translate_syntax.cmx: interp/src/translate_syntax.ml interp/src/translate_syntax.cmi interp/src/extract/JsSyntax.cmx
	$(OCAMLOPT) -c -I interp/src -I interp/src/extract -o $@ $<

interp/src/translate_syntax.cmo: interp/src/translate_syntax.ml interp/src/translate_syntax.cmi interp/src/extract/JsSyntax.cmo
	$(OCAMLC) -c -I interp/src -I interp/src/extract -o $@ $<

interp/src/prheap.cmi: interp/src/prheap.mli interp/src/extract/JsSyntax.cmi
	$(OCAMLOPT) -c -I interp/src -I interp/src/extract -o $@ $<

interp/src/prheap.cmx: interp/src/prheap.ml interp/src/extract/JsSyntax.cmx interp/src/prheap.cmi
	$(OCAMLOPT) -c -I interp/src -I interp/src/extract -o $@ $<

interp/src/prheap.cmo: interp/src/prheap.ml interp/src/extract/JsSyntax.cmo interp/src/prheap.cmi
	$(OCAMLC) -c -I interp/src -I interp/src/extract -o $@ $<

interp/src/print_syntax.cmx: interp/src/print_syntax.ml interp/src/extract/JsSyntax.cmx
	$(OCAMLOPT) -c -I interp/src -I interp/src/extract -o $@ $<

interp/src/run_js.cmx: interp/src/run_js.ml interp/src/extract/JsInterpreter.cmx
	$(OCAMLOPT) -c -I interp/src -I interp/src/extract -I $(shell ocamlfind query xml-light) -o $@ $<

interp/src/run_js.cmo: interp/src/run_js.ml interp/src/extract/JsInterpreter.cmo
	$(OCAMLC) -c -I interp/src -I interp/src/extract -I $(shell ocamlfind query xml-light) -o $@ $<

interp/src/run_jsbisect.ml: interp/src/run_js.ml
	cp $< $@
	perl -pe 's/JsInterpreter\./JsInterpreterBisect\./' $@ > $@.bak
	mv $@.bak $@

interp/src/run_jsbisect.cmx: interp/src/run_jsbisect.ml interp/src/extract/JsInterpreterBisect.cmx
	$(OCAMLOPT) -c -I interp/src -I interp/src/extract -I $(shell ocamlfind query xml-light) -o $@ $<

interp/src/run_jsbisect.cmo: interp/src/run_jsbisect.ml interp/src/extract/JsInterpreterBisect.cmo
	$(OCAMLC) -c -I interp/src -I interp/src/extract -I $(shell ocamlfind query xml-light) -o $@ $<

mlfiles = ${shell ls interp/src/extract/*.ml interp/src/*.ml interp/parser/src/*.ml | perl -pe 's|interp/src/prtest.ml||'}
mlfilessorted = ${shell ocamldep -I interp/src/extract -sort ${mlfiles}}
mlfilessortedwithparsermoved = ${shell echo ${mlfilessorted} | perl -pe 's|parser/src|src|g'}
mlfilestransformed = ${mlfilessortedwithparsermoved:.ml=.cmx}
mlfilesbyte = ${mlfilessortedwithparsermoved:.ml=.cmo}
basicfiles=${shell echo ${mlfilestransformed} | perl -pe 's|interp/src/extract/JsInterpreterTrace.cmx||' | perl -pe 's|interp/src/run_jstrace.cmx||' | perl -pe 's|interp/src/extract/JsInterpreter.cmx||' | perl -pe 's|interp/src/run_js.cmx||' | perl -pe 's|interp/src/extract/JsInterpreterBisect.cmx||' | perl -pe 's|interp/src/run_jsbisect.cmx||'}
basicbytefiles=${shell echo ${mlfilesbyte} | perl -pe 's|interp/src/extract/JsInterpreterTrace.cmx||' | perl -pe 's|interp/src/run_jstrace.cmx||' | perl -pe 's|interp/src/extract/JsInterpreter.cmx||' | perl -pe 's|interp/src/run_js.cmx||' | perl -pe 's|interp/src/extract/JsInterpreterBisect.cmx||' | perl -pe 's|interp/src/run_jsbisect.cmx||'}

interp/run_js: ${basicfiles} interp/src/extract/JsInterpreter.cmx interp/src/run_js.cmx
	$(OCAMLOPT) $(PARSER_INC) -o interp/run_js xml-light.cmxa unix.cmxa str.cmxa $^

interp/run_js.byte: ${basicbytefiles} interp/src/extract/JsInterpreter.cmo interp/src/run_js.cmo
	$(OCAMLC) $(PARSER_INC) -o interp/run_js.byte xml-light.cma unix.cma str.cma $^

interp/run_jsbisect: ${basicfiles} interp/src/extract/JsInterpreterBisect.cmx interp/src/run_jsbisect.cmx
	ocamlfind $(OCAMLOPT) -package bisect $(PARSER_INC) -o interp/run_jsbisect xml-light.cmxa unix.cmxa str.cmxa bisect.cmxa $^


#######################################################
# Tracing version of the interpreter

tracer/annotml/ppx_lines.native: tracer/annotml/ppx_lines.ml
	cd tracer/annotml; ocamlfind ocamlopt -c -package compiler-libs.common -o ppx_lines.cmx ppx_lines.ml
	cd tracer/annotml; ocamlfind ocamlopt -linkpkg -package compiler-libs.common ppx_lines.cmx -o ppx_lines.native

interp/src/extract/JsInterpreterTrace.cmx: ${basicfiles} interp/src/extract/JsInterpreter.ml tracer/annotml/ppx_lines.native
	cp interp/src/extract/JsInterpreter.ml interp/src/extract/JsInterpreterTrace.ml
	$(OCAMLOPT) -ppx tracer/annotml/ppx_lines.native -c -I interp/src -I interp/src/extract -I tracer/annotml -o $@ interp/src/extract/JsInterpreterTrace.ml

interp/src/run_jstrace.ml: interp/src/run_js.ml
	cp $< $@
	perl -pe 's/JsInterpreter\./JsInterpreterTrace\./' $@ > $@.bak
	mv $@.bak $@

interp/src/run_jstrace.cmx: interp/src/run_jstrace.ml interp/src/extract/JsInterpreterTrace.cmx
	$(OCAMLOPT) -c -I interp/src -I interp/src/extract -I $(shell ocamlfind query xml-light) -o $@ $<

tracer/annotml/myPrint.cmx: tracer/annotml/myPrint.ml
	$(OCAMLOPT) -c -o $@ $<

interp/run_jstrace: ${basicfiles} tracer/annotml/myPrint.cmx interp/src/extract/JsInterpreterTrace.cmx interp/src/run_jstrace.cmx
	ocamlfind $(OCAMLOPT) $(PARSER_INC) -o interp/run_jstrace xml-light.cmxa unix.cmxa str.cmxa $^


#######################################################
# DEPENDENCIES

# TODO: split the dependencies between the coq files and the caml files

DEPS=$(JS_SRC) $(TLC_SRC) $(FLOCQ_SRC)

depend: .depend

ifeq ($(KEEP_DEPENDS),1)
else
.depend : $(DEPS) Makefile
	$(COQDEP) $(DEPS) > .depend
	ocamldep -I interp/src/extract/ interp/src/extract/*.ml{,i} >> .depend
endif

ifeq ($(findstring $(MAKECMDGOALS),init depend clean clean_all),)
include .depend
endif


#######################################################
# CLEAN

clean_cm:
	bash -c "rm -f interp/src/*.{cmi,cmx,cmo}" || echo ok
	bash -c "rm -f interp/src/extract/*.{cmi,cmx,cmo}" || echo ok
	bash -c "rm -f tracer/annotml/*.{cmi,cmx,cmo}" || echo ok

clean: clean_cm
	bash -c "rm -f coq/*.{vo,deps,dot,glob,ml,mli,cmi,cmx}" || echo ok
	bash -c "rm -f .depend" || echo ok
	bash -c "rm -f interp/src/extract/*.{ml,mli}" || echo ok
	bash -c "rm -f interp/run_js interp/run_jsbisect interp/run_jsbisect.ml" || echo ok

clean_all: clean
	find . -iname "*.vo" -exec rm {} \;
	find . -iname "*.glob" -exec rm {} \;


#######################################################
# LOCAL: copy all flocq and tlc .vo files to the head folder

local:
	@$(foreach file, $(FLOCQ_VO), cp $(file) $(notdir $(file));)
	@$(foreach file, $(TLC_VO), cp $(file) $(notdir $(file));)
