all: cleanExceptPdf program show normalize generate_traversals cleanExceptPdf

show: cleanExceptPdf
	xelatex --shell-escape show_traversal.tex

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
	rm -rf *.log *.aux *.toc *.pyg *.pytxcode show_traversal.tex examples.tex examplesNormalForms.tex Main *.o *.hi

clean: cleanExceptPdf
	rm -f show_traversal.pdf examples.pdf examplesNormalForms.pdf
