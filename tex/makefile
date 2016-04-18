all: transition_system main main2 headLinearReduction

transition_system:
	xelatex --shell-escape labelledTransitionSystem.tex
	xelatex --shell-escape labelledTransitionSystem.tex
	make clean

headLinearReduction:
	xelatex --shell-escape headLinearReductionLTS.tex
	make clean

main:
	xelatex --shell-escape main.tex
	xelatex --shell-escape main.tex
	make clean

main2:
	xelatex --shell-escape main2.tex
	xelatex --shell-escape main2.tex
	make clean

clean:
	rm -rf *.log *.aux *.toc *.pyg *.pytxcode _minted-*

cleanPdf: clean
	rm -rf *.pdf