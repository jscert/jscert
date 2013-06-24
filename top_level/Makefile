mlfiles = ${shell ls ../interp/src/extract/*.ml ../interp/src/*.ml ../interp/parser/src/*.ml}
mlfilessorted = ${shell ocamldep -I ../interp/src/extract/ -sort ${mlfiles}}
mlfilestransformed = ${shell echo ${mlfilessorted} | sed 's|parser/src|src|g' | sed 's|.ml|.cmx|g' |  sed 's|../interp/src/extract/JsInterpreterBisect.cmx||' | sed 's|../interp/src/run_jsbisect.cmx||' | sed 's|../interp/src/run_js.cmx||'}

INCLUDE = -I ../interp/src -I ../interp/src/extract

PACKAGE = -package lwt.syntax -package lwt.simple-top -package lwt -package unix -package str -package xml-light -linkpkg

all:
	ocamlfind ocamlopt -syntax camlp4o $(PACKAGE) $(INCLUDE) -o top $(mlfilestransformed) top.ml
	rm top.cm* *~

clean: 
	rm *.o top
