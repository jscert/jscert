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

# Use bash as the default shell
SHELL=/bin/bash

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

OCAMLBUILD=ocamlbuild

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
# MAIN TARGETS

default: coq interpreter tags

all: default interp/run_jsbisect interp/run_jstrace

debug:
	make -f Makefile.debug

report:
	bisect-report -html report bisect*.out
	firefox report/index.html || open report/index.html
	rm bisect*.out

tags: $(JS_SRC)
	./gentags.sh

.PHONY: all default debug report init tlc flocq lib \
        coq extract_interpreter interpreter \
        local nofast

#######################################################
# EXTERNAL OCAML DEPENDENCIES
.PHONY: install_depend install_optional_depend
install_depend:
	# Install coq if required
	if ! which $(COQBIN)coqc; then opam install -y coq; fi
	opam install -y xml-light ocamlfind yojson

install_optional_depend: install_depend
	opam install -y js_of_ocaml bisect

#######################################################
# EXTERNAL LIBRARIES: TLC and Flocq

init:
	git submodule init; git submodule update
	svn checkout svn://scm.gforge.inria.fr/svn/tlc/trunk lib/tlc
	tar -xzf lib/flocq-2.1.0.tar.gz
	mv flocq-2.1.0 lib/flocq
# alternative: pull git from svn
#	git clone https://gforge.inria.fr/git/flocq/flocq.git flocq

lib: tlc flocq

tlc: $(TLC_VO)

flocq: $(FLOCQ_VO)

#######################################################
# Coq Compilation Implicit Rules
%.v.d: %.v
	$(COQDEP) $< > $@

# If this rule fails for some reason, try `make clean_all && make`
%.vo: %.v
	$(COQC) -dont-load-proofs $<

#######################################################
# FAST COMPILATION TOOL: coqj

# Compile coqj : converts a .v file into a shallow .v file (without proofs)
tools/coqj/coqj:
	$(MAKE) -C tools/coqj coqj

# Fast compilation of files in $(FAST_SRC)
define FAST_RULE
$(1).vo: tools/coqj/coqj
	@mkdir -p _shallow/$(dir $1)
	tools/coqj/coqj $(1).v > _shallow/$(1).v
	$(COQC) -dont-load-proofs -I coq -I $(TLC) _shallow/$(1).v
	mv _shallow/$(1).vo $(1).vo
endef

$(foreach filebase,$(FAST_SRC:.v=),$(eval $(call FAST_RULE,$(filebase))))

# "make nofast" : Compilation mode to force the verification of all files
nofast: $(FAST_VO:.vo=_full.vo)

%_full.vo : %.v
	echo $*
	cp $*.v $*_full.v
	$(COQC) -dont-load-proofs -I coq -I $(TLC) $*_full.v
	rm $*_full.v

#######################################################
# JSCert Specific Rules

coq: $(JS_VO)

# Interpreter extraction spits out lots of *.ml,mli files
# The option [-dont-load-proof] would extract all instance to an axiom! -- Martin.
coq/JsInterpreterExtraction.vo: coq/JsInterpreterExtraction.v
	$(COQC) $<
	-mkdir -p interp/src/extract
	-rm -f interp/src/extract/.patched
	mv *.ml interp/src/extract
	mv *.mli interp/src/extract

#######################################################
# JsRef Interpreter Rules

# ; forces rule to be run, generates everything under extract dir
interp/src/extract/%: coq/JsInterpreterExtraction.vo ;

# Insert more useful error messages into Interpreter
REFGETVALUE=$(shell cat interp/src/insert/ref_get_value)
REFGETVALUE2=$(shell cat interp/src/insert/ref_get_value2)
RUNOBJECTMETHOD=$(shell cat interp/src/insert/run_object_method)
RUNOBJECTHEAP=$(shell cat interp/src/insert/run_object_heap_set_extensible)
ENVGETIDENTIFIER=$(shell cat interp/src/insert/lexical_env_get_identifier_ref)

interp/src/extract/JsInterpreter.ml.patched: interp/src/extract/JsInterpreter.ml
	@echo \# Inserting useful error messages into $<
	@perl -i -pe 's|res_res \(run_error s Coq_native_error_ref\)|$(REFGETVALUE)|' $<
	@perl -i -pe 's/\(\*\* val run_object_heap_set_extensible :/$(RUNOBJECTMETHOD)/' $<
	@perl -i -pe 's/type runs_type =/$(RUNOBJECTHEAP)/' $<
	@perl -i -pe 's/    result_val s \(ref_create_value \(Coq_value_prim Coq_prim_undef\) x0 str\)/$(ENVGETIDENTIFIER)/' $<
	@perl -i -pe 's|\(\*\* val run_expr_get_value :|$(REFGETVALUE2)|' $<
	touch $@

# Sentinel file to check all interpreter source files have been patched
# Should depend on each individual file patched sentinel
# (Can also add rules to patch all files)
interp/src/extract/.patched: interp/src/extract/JsInterpreter.ml.patched
	touch $@

extract_interpreter: interp/src/extract/.patched

# interp/_tags contains OCaml-specific build rules for all interpreter variants
interp/%.native interp/%.byte: extract_interpreter interp/src/%.ml
	cd interp && $(OCAMLBUILD) -use-ocamlfind -cflags "-w -20" $(@F)

.PRECIOUS: interp/%.native
interp/%: interp/%.native
	ln -fs $(<F) $@

interpreter: interp/run_js

#######################################################
# JSRef Bisect Mode

interp/src/extract/JsInterpreterBisect.ml: interp/src/extract/JsInterpreter.ml extract_interpreter
	perl -pe 's/ impossible/ (*BISECT-IGNORE*) impossible/g' $< > $@

interp/src/run_jsbisect.ml: interp/src/run_js.ml
	perl -pe 's/JsInterpreter\./JsInterpreterBisect\./' $< > $@

interp/run_jsbisect.native: interp/src/run_jsbisect.ml \
                            interp/src/extract/JsInterpreterBisect.ml

# interp/run_jsbisect is an implicit rule

#######################################################
# Tracing version of the interpreter

interp/tracer/annotml/ppx_lines.native:
	$(MAKE) -C interp/tracer/annotml ppx_lines.native

interp/src/extract/JsInterpreterTrace.ml: interp/src/extract/JsInterpreter.ml extract_interpreter
	cp $< $@

interp/src/run_jstrace.ml: interp/src/run_js.ml
	perl -pe 's/JsInterpreter\./JsInterpreterTrace\./' $< > $@

interp/run_jstrace.native: interp/src/run_jstrace.ml interp/src/extract/JsInterpreterTrace.ml interp/tracer/annotml/ppx_lines.native

# interp/run_jstrace is an implicit rule

#######################################################
# Interpreter run helpers
.PHONY: run_tests run_tests_spidermonkey run_tests_lambdaS5 run_tests_nodejs

run_tests: interpreter
	./runtests.py --no_parasite

run_tests_spidermonkey:
	./runtests.py --spidermonkey --interp_path $(SPIDERMONKEY)

run_tests_lambdaS5:
	./runtests.py --lambdaS5 --interp_path $(LAMBDAS5)

run_tests_nodejs:
	./runtests.py --nodejs --interp_path $(NODEJS)

#######################################################
# CLEAN
.PHONY: clean clean_interp clean_all

clean_interp:
	-rm -f coq/JsInterpreterExtraction.vo
	-rm -rf interp/src/extract
	-rm -f interp/run_js interp/run_jsbisect interp/src/run_jsbisect.ml
	cd interp && $(OCAMLBUILD) -quiet -clean
	-rm -f interp/run_jstrace interp/src/run_jstrace.ml
	$(MAKE) -C interp/tracer/annotml clean

clean: clean_interp
	-rm -f coq/*.{vo,glob,d}

clean_all: clean
	find . -iname "*.vo" -exec rm {} \;
	find . -iname "*.glob" -exec rm {} \;
	find . -iname "*.d" -exec rm {} \;


#######################################################
# LOCAL: copy all flocq and tlc .vo files to the head folder

local:
	@$(foreach file, $(FLOCQ_VO), cp $(file) $(notdir $(file));)
	@$(foreach file, $(TLC_VO), cp $(file) $(notdir $(file));)

#######################################################
#######################################################


ifeq ($(filter init clean% install% all,$(MAKECMDGOALS)),)
-include $(JS_SRC:.v=.v.d)
-include $(TLC_SRC:.v=.v.d)
-include $(FLOCQ_SRC:.v=.v.d)
endif
