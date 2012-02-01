GUIDE	= userguide-1.3
TEX	= $(GUIDE).tex
PS	= $(GUIDE).ps.gz
PDF	= $(GUIDE).pdf
HTML	= $(GUIDE).html
BIB	= userguide.bib

LATEX	 = latex
PDFLATEX = pdflatex
HEVEA	 = hevea -noiso

all: $(PS) $(PDF) $(HTML)

clean:
	rm -f $(PS) $(PDF) $(HTML)
	rm -f *.aux *.log *.toc *.blg *.bbl *.dvi *.haux *.htoc

htclean:
	rm -f *.haux *.htoc *.html

.SUFFIXES: .tex .aux .bbl .dvi .ps .pdf .haux .htoc .html

.tex.aux:
	latex $*

.aux.bbl:
	bibtex $*

# This cancels the predefined .tex.dvi rule,
# which uses tex instead of latex,
# and which I don't want to redefine since
# depending on the bbl makes more sence dependency-wise.
# For some reason, ".tex.dvi:" doesn't cancel the rule.
%.dvi: %.tex

.bbl.dvi:
	$(LATEX) $*
	! grep -q "Rerun to get cross-references right" $*.log || $(LATEX) $*
.dvi.ps:
	dvips $< -o $@
%.gz: %
	gzip -f $<

.bbl.pdf:
	$(PDFLATEX) $*
	! grep -q "Rerun to get cross-references right" $*.log || $(PDFLATEX) $*

# Finding whether hevea really needs to be re-run is complicated
# since it doesn't procuce a log file, so instead of playing with tee and
# file descriptors I will always re-run it.
%.html: %.aux %.bbl
	$(HEVEA) $*
	$(HEVEA) $*

show: $(PDF)
	kpdf $< &


# For this target, the aux file need to mention a bib file
# in Dale's LIX directory.
# Only he will be able to do the following command to create the
# userguide.bib file.
bib: $(BIB)

BIBREF	= ../../../../../pap/references/master
ifneq ($(strip $(wildcard $(BIBREF))),)
$(BIB): $(TEX)
	sed -e 's|^\\bibliography{userguide}$$|\\bibliography{$(BIBREF)}|' $< | latex --jobname=$(<:.tex=) --
	aux2bib $(<:.tex=.aux) > $@
	rm -f $(<:.tex=.aux)
endif
