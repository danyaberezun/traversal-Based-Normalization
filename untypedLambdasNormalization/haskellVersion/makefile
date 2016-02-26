all: cleanExceptPdf
	ghc Main.hs
	./Main
	xelatex --shell-escape examples.tex
	xelatex --shell-escape examples.tex
	make cleanExceptPdf

cleanExceptPdf:
	rm -rf *.log *.aux *.toc *.pyg *.pytxcode examples.tex TwoBackPointersVersion *.o *.hi

clean: cleanExceptPdf
	rm -f examples.pdf