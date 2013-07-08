all:
#	ocamlopt -i environment.ml
	ocamlopt -o environment.cmx -c environment.ml
#	ocamlopt -i reference.ml
	ocamlopt -o reference.cmx -c reference.ml
#	ocamlopt -i lexical.ml
	ocamlopt -o lexical.cmx -c lexical.ml
#	ocamlopt -i context.ml
	ocamlopt -o context.cmx -c context.ml
#	ocamlopt -i conversion.ml
	ocamlopt -o conversion.cmx -c conversion.ml
#	ocamlopt -i expression.ml
	ocamlopt -o expression.cmx -c expression.ml
#	ocamlopt -i statement.ml
	ocamlopt -o statement.cmx -c statement.ml
	ocamlopt -o jvs.cmx -c jvs.ml
	ocamlopt -o print.cmx -c print.ml
	ocamlopt -o main environment.cmx reference.cmx lexical.cmx context.cmx conversion.cmx expression.cmx statement.cmx print.cmx jvs.cmx main.ml
	rm *.cm* *.o*

clean:
	rm main result *.js *.xml *~ 
