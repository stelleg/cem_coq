all: view

paper.pdf: *.tex *.bib *.sty
	xelatex paper.tex
	bibtex paper
	xelatex paper.tex
	xelatex paper.tex

clean:
	rm paper.pdf
	rm paper.aux
	rm paper.log
	rm paper.bbl
	rm paper.blg

view: paper.pdf
	mupdf paper.pdf
