
default: userguide.ps.gz userguide.pdf userguide.html

clean:
	rm -f userguide.ps.gz userguide.pdf userguide.html

%.pdf: %.tex
	pdflatex $<
%.dvi: %.tex
	latex $<
	bibtex $(<:.tex=)
	latex $<
%.ps: %.dvi
	dvips $< -o $@
%.gz: %
	gzip -f $<
%.html: %.tex
	hevea -noiso $<

html: userguide.html

bib:
	bibtex userguide

show: userguide.pdf
	kpdf userguide.pdf&

# Currently, the aux file mentions a bib file in Dale's LIX directory.  
# Only he will be able to do the following command to create the 
# userguide.bib file.

userguide.bib: userguide.tex
	aux2bib userguide.aux > userguide.bib
