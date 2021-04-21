all:
	-ocamllex src/lexer.mll
	ocamlyacc src/parser.mly
	dune build

clean:
	dune clean
	-rm src/parser.ml
	-rm src/parser.mli
	-rm src/lexer.ml
	-rm paper/*.aux
	-rm paper/*.log
	-rm paper/proofs/*.aux
	-rm paper/proofs/*.log
	-rm paper/*.pdf
	-rm paper/*.gz
	-rm -rf paper/_minted*


lexer:
	ocamllex src/lexer.mll

parser:
	ocamlyacc src/parser.mly
	
paper:
	pdflatex -shell-escape paper/notes.tex
