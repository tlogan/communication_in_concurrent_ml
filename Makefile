all: thesis.pdf anon_thesis.pdf presentation.pdf


thesis.pdf:
	pdflatex thesis; bibtex thesis;\
  pdflatex thesis; pdflatex thesis


presentation.pdf:
	pdflatex presentation; bibtex presentation;\
  pdflatex presentation; pdflatex presentation


anon_thesis.pdf:
	pdflatex anon_thesis; bibtex anon_thesis;\
  pdflatex anon_thesis; pdflatex anon_thesis


cleanPres:
	rm presentation.{aux,bbl,blg,log,out,pdf}

clean:
	rm thesis.{aux,bbl,blg,log,out,pdf}
	rm presentation.{aux,bbl,blg,log,out,pdf}
	rm anon_thesis.{aux,bbl,blg,log,out,pdf}
