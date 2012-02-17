GUIDE	= userguide-1.3
TEX	= $(GUIDE).tex
PS	= $(GUIDE).ps.gz
PDF	= $(GUIDE).pdf
HTML	= $(GUIDE).html
BIB	= userguide.bib

LATEX	 = latex
PDFLATEX = pdflatex
HEVEA	 = hevea -noiso
GZIP	 = gzip -9

all: $(PS) $(PDF) $(HTML)

clean:
	rm -f $(PS) $(PDF) $(HTML)
	rm -f *.aux *.log *.toc *.blg *.bbl *.dvi *.haux *.htoc
	rm -f html/ndcore/* html/bedwyr/*

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
# depending on the bbl makes more sense dependency-wise.
# For some reason, ".tex.dvi:" doesn't cancel the rule.
%.dvi: %.tex

.bbl.dvi:
	$(LATEX) $*
	@while ( grep -q "Rerun to get cross-references right" $*.log ) ; do \
	  echo 'Reruning latex to get cross-references right' ; \
	  $(LATEX) $* ; \
	  done
.dvi.ps:
	dvips $< -o $@
%.gz: %
	$(GZIP) -f $<

.bbl.pdf:
	$(PDFLATEX) $*
	@while ( grep -q "Rerun to get cross-references right" $*.log ) ; do \
	  echo 'Reruning pdflatex to get cross-references right' ; \
	  $(PDFLATEX) $* ; \
	  done

# Finding whether hevea really needs to be re-run is complicated
# since it doesn't always warn, so I first make sure that latex was
# run enough times.
.dvi.html:
	@echo $(HEVEA) $*
	@bash -c 'while ( ($(HEVEA) $* 2>&1 | tee >(cat >&3) | grep -q "Rerun me to get cross-references right") 3>&1 ) ; do \
	  echo "Reruning hevea to get cross-references right" ; \
	  done'

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
