cc = xelatex
option = --shell-escape

all: main main2 headLinearReduction

headLinearReduction:
	$(cc) $(option) headLinearReductionLTS.tex
	$(cc) $(option) headLinearReductionLTS.tex
	make clean

main:
	$(cc) $(option) main.tex
	$(cc) $(option) main.tex
	make clean

main2:
	$(cc) $(option) main2.tex
	$(cc) $(option) main2.tex
	make clean

clean:
	rm -rf *.log *.aux *.toc *.pyg *.pytxcode _minted-*

cleanPdf: clean
	rm -rf *.pdf