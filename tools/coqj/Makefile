coqj.native: coqj.mll
	ocamlbuild -verbose 1 $@

coqj: coqj.native
	ln -s $@.native $@

clean:
	ocamlbuild -clean -quiet
	rm -f coqj

.PHONY: clean
