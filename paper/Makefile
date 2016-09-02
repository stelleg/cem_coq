
all: paper.pdf
	mupdf paper.pdf

paper.pdf: *.tex *.bib
	pdflatex paper.tex
	bibtex paper
	pdflatex paper.tex
	pdflatex paper.tex

clean:
	rm paper.pdf
	rm paper.aux
	rm paper.log
	rm paper.bbl
	rm paper.blg

view: paper.pdf
	mupdf paper.pdf
