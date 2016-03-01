all:
	xelatex --shell-escape labelledTransitionSystem.tex
	xelatex --shell-escape labelledTransitionSystem.tex
	make clean

main:
	xelatex --shell-escape main.tex
	xelatex --shell-escape main.tex

main2:
	xelatex --shell-escape main2.tex
	xelatex --shell-escape main2.tex

clean:
	rm -rf *.log *.aux *.toc *.pyg *.pytxcode _minted-*

cleanPdf: clean
	rm -rf *.pdf