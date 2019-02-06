all: thesis.pdf anon_thesis.pdf

thesis.pdf:
	pdflatex thesis; bibtex thesis;\
  pdflatex thesis; pdflatex thesis


anon_thesis.pdf:
	pdflatex anon_thesis; bibtex anon_thesis;\
  pdflatex anon_thesis; pdflatex anon_thesis

clean:
	rm thesis.{aux,bbl,blg,log,out,pdf}
	rm anon_thesis.{aux,bbl,blg,log,out,pdf}
