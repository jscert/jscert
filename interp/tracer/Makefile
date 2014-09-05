generate.out: generate.ml
	ocamlc str.cma generate.ml -o $@

trace.js: annotml/trace.log generate.out
	./generate.out $< $@ annotml/test/bar.ml annotml/test/foo.ml

view: navig.html trace.js 
	chromium-browser $<		
