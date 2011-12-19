default:

PS   = userguide.ps.gz
PDF  = userguide.pdf
HTML = userguide.html

#default: $(PS) $(PDF) $(HTML)

clean:
	rm -f $(PS) $(PDF) $(HTML)

%.pdf: %.tex
	pdflatex $<
%.dvi: %.tex
	latex $<
	bibtex $*
	latex $<
%.ps: %.dvi
	dvips $< -o $@
%.gz: %
	gzip -f $<
%.html: %.tex
	hevea -noiso $<

bib:
	bibtex userguide

show: userguide.pdf
	kpdf userguide.pdf&

# Currently, the aux file mentions a bib file in Dale's LIX directory.
# Only he will be able to do the following command to create the
# userguide.bib file.

userguide.bib: userguide.tex
	aux2bib userguide.aux > userguide.bib
