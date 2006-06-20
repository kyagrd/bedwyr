
default: userguide.ps.gz userguide.pdf
%.pdf: %.tex
	pdflatex $<
%.dvi: %.tex
	latex $<
%.ps: %.dvi
	dvips $< -o $@
%.gz: %
	gzip $<
