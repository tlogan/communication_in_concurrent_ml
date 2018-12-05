all: thesis.pdf 

thesis.pdf:
	pdflatex thesis; bibtex thesis;\
  pdflatex thesis; pdflatex thesis

clean:
	rm thesis.{aux,bbl,blg,log,out,pdf}
