ppx_lines.native: ppx_lines.ml
	ocamlfind ocamlopt -c -package compiler-libs.common -o ppx_lines.cmx ppx_lines.ml
	ocamlfind ocamlopt -linkpkg -package compiler-libs.common ppx_lines.cmx -o ppx_lines.native

myPrint.cmo: myPrint.ml
	ocamlfind ocamlc -c -o myPrint.cmo myPrint.ml

testFoo: ppx_lines.native myPrint.cmo test/foo.ml test/bar.ml
	ocamlc -dsource -ppx ./ppx_lines.native -c test/bar.ml
	ocamlc -dsource -ppx ./ppx_lines.native -I test -c test/foo.ml
	ocamlc myPrint.cmo test/bar.cmo test/foo.cmo -o testFoo

tests: testFoo
	./testFoo

.PHONY: tests
