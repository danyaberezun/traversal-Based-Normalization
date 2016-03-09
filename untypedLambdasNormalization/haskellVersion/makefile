all: cleanExceptPdf
	make program
	make normalize
	make generate_traversals
	make cleanExceptPdf

program: cleanExceptPdf
	ghc Main.hs
	./Main

normalize:
	xelatex --shell-escape examplesNormalForms.tex
	xelatex --shell-escape examplesNormalForms.tex

generate_traversals:
	xelatex --shell-escape examples.tex
	xelatex --shell-escape examples.tex

cleanExceptPdf:
	rm -rf *.log *.aux *.toc *.pyg *.pytxcode examples.tex examplesNormalForms.tex Main *.o *.hi

clean: cleanExceptPdf
	rm -f examples.pdf examplesNormalForms.pdf