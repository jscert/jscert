JS_PARSER_JAR=./src/parser/lib/js_parser.jar

BUILD_FLAGS=-I,$(shell ocamlfind query camomile),-I,$(shell ocamlfind query batteries),-I,$(shell ocamlfind query oUnit),-I,$(shell ocamlfind query xml-light)

BUILD_FLAGS=-I,$(shell ocamlfind query camomile),-I,$(shell ocamlfind query batteries),-I,$(shell ocamlfind query oUnit),-I,$(shell ocamlfind query xml-light)

LIBS=xml-light,unix,oUnit,nums,str,bigarray,camomile,batteries

copyfiles:
	cp ../../coq/core/v0.2/interpreter.ml src
	cp ../../coq/core/v0.2/interpreter.mli src 

clean:
	ocamlbuild -clean

build_test: copyfiles
	ocamlbuild -libs ${LIBS} \
	-cflags ${BUILD_FLAGS} \
	-lflags ${BUILD_FLAGS} \
	-Is src,src/parser/src,test \
	test/test_parser.byte

run_test: build_test
	./test_parser.byte -jsparser ${JS_PARSER_JAR}

build_run: copyfiles
	ocamlbuild -libs ${LIBS} \
	-cflags ${BUILD_FLAGS} \
	-lflags ${BUILD_FLAGS} \
	-Is src,src/parser/src \
	run.byte

