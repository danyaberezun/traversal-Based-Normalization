all:
	xelatex --shell-escape main.tex
	xelatex --shell-escape main.tex

main2:
	xelatex --shell-escape main2.tex
	xelatex --shell-escape main2.tex

clean:
	rm -rf *.log *.aux *.toc *.pyg *.pytxcode _minted-main*
cleanPdf: clean
	rm -rf *.pdf