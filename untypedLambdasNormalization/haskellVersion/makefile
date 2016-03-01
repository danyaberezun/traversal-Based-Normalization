all: cleanExceptPdf
	ghc Main.hs
	./Main

normalize: all
	xelatex --shell-escape examplesNormalForms.tex
	xelatex --shell-escape examplesNormalForms.tex
	make cleanExceptPdf

generate_traversals: all
	xelatex --shell-escape examples.tex
	xelatex --shell-escape examples.tex
	make cleanExceptPdf

cleanExceptPdf:
	rm -rf *.log *.aux *.toc *.pyg *.pytxcode examples.tex examplesNormalForms.tex Main *.o *.hi

clean: cleanExceptPdf
	rm -f examples.pdf examplesNormalForms.pdf