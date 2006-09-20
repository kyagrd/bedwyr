
default: userguide.ps.gz userguide.pdf

clean:
	rm -f userguide.ps.gz userguide.pdf

%.pdf: %.tex
	pdflatex $<
%.dvi: %.tex
	latex $<
%.ps: %.dvi
	dvips $< -o $@
%.gz: %
	gzip -f $<

# Currently, the aux file mentions a bib file in Dale's LIX directory.  
# Only he will be able to do the following command to create the 
# userguide.bib file.

userguide.bib: userguide.tex
	aux2bib userguide.aux > userguide.bib
