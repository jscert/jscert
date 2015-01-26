OCAMLBUILD=ocamlbuild -use-ocamlfind

ppx_lines.native: ppx_lines.ml
	$(OCAMLBUILD) $@

foo.native: ppx_lines.native myPrint.ml test/foo.ml test/bar.ml
	$(OCAMLBUILD) test/$@

tests: foo.native
	./foo.native

clean:
	$(OCAMLBUILD) -clean -quiet

.PHONY: tests clean
