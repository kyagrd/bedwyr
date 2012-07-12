##############################################################################
#  Bedwyr prover                                                             #
#  Copyright (C) 2012 Quentin Heath                                          #
#                                                                            #
#  This program is free software; you can redistribute it and/or modify      #
#  it under the terms of the GNU General Public License as published by      #
#  the Free Software Foundation; either version 2 of the License, or         #
#  (at your option) any later version.                                       #
#                                                                            #
#  This program is distributed in the hope that it will be useful,           #
#  but WITHOUT ANY WARRANTY; without even the implied warranty of            #
#  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the             #
#  GNU General Public License for more details.                              #
#                                                                            #
#  You should have received a copy of the GNU General Public License         #
#  along with this code; if not, write to the Free Software Foundation,      #
#  Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307 USA              #
##############################################################################

# $(make TARGET=$TARGET) compiles
# $(make TARGET=$TARGET install) installs
# $(make TARGET=$TARGET dist) builds packages
#
# $TARGET can be one of those:
# - "ndcore" for this library only
# - "bedwyr" for the program only
# - ""

-include Makefile.include

### FILES

TEST_EXAMPLES	= list.def internal/scoping.def internal/checks.def \
		  3bits.def lambda.def progs.def \
		  graph-alt.def minmax.def multisim.def \
		  tictactoe.def \
		  pi/pi_trace.def pi/corr-assert.def pi/pi_modal.def \
		  pi/pi_asserts.def

## ?? ##

ndcore_dir	= src/ndcore
bedwyr_prefix	= src/bedwyr
src_docdir	= src.docdir

# Archived files

ARCH_FILES	= $(OCAML_FILES) \
		  $(NDCORE_FILES) $(BEDWYR_FILES) \
		  $(MAN_FILES) $(CONTRIB_FILES) $(EXAMPLES_FILES) \
		  configure.ac Makefile Makefile.include.in \
		  myocamlbuild.ml _tags install-sh

BEDWYR_ARCH	= $(addprefix $(DIST_NAME).,$(ARCH_SUFFIXES))

# Released files

NDCORE_LIBS	= $(addprefix $(ndcore_dir)/ndcore.,$(LIB_SUFFIXES))
NDCORE_MLS	= $(filter-out $(ndcore_dir)/test.ml,$(wildcard $(ndcore_dir)/*.ml))
NDCORE_MODULES	= $(basename $(NDCORE_MLS))
ifneq ($(BEST_SUFFIX),)
  NDCORE_CMIS	= $(addsuffix .cmi,$(NDCORE_MODULES))
endif
NDCORE_LIB_FLS	= $(NDCORE_LIBS) $(ndcore_dir)/META $(NDCORE_CMIS)
BEDWYR_BINS	= $(addprefix $(bedwyr_prefix).,$(BIN_SUFFIXES))
ifeq ($(TARGET),ndcore)
  BUILT_FILES	= $(NDCORE_LIB_FLS)
else
  ifeq ($(TARGET),bedwyr)
  BUILT_FILES	= $(BEDWYR_BINS)
  else
    ifeq ($(TARGET),)
  BUILT_FILES	= $(NDCORE_LIB_FLS) $(BEDWYR_BINS)
    endif
  endif
endif
MANPAGES	= $(MAN_FILES:.in=.gz)


DIST_FILES	= $(BUILT_FILES) \
		  $(NDCORE_FILES) $(BEDWYR_FILES) \
		  $(MANPAGES) $(CONTRIB_FILES) $(EXAMPLES_FILES) \
		  $(NDCORE_ODOCS) $(BEDWYR_ODOCS_DIR)/index.html

# Other files

DEBIAN_FILES	= $(DEBIAN_FILES_IN:.in=)

### BUILDING

build: $(BUILT_FILES) bedwyr

$(BEDWYR_BINS): src/config.ml

%.byte:
	@$(OCAMLBUILD) $@

%.native:
	@$(OCAMLBUILD) $@

%.cmi:
	@$(OCAMLBUILD) $@

%.cma:
	@$(OCAMLBUILD) $@

%.cmxa %.a:
	@$(OCAMLBUILD) $@

%.docdir/index.html: %.odocl
	@$(OCAMLBUILD) $@

%.odoc:
	@$(OCAMLBUILD) $@

%.exe:
	@$(OCAMLBUILD) -just-plugin
	@$(OCAMLBUILD) -ocamlopt $(MINGW32_OCAMLOPT) $*.native
	@mv -vi _build/$*.native _build/$*.exe

%:: config.status %.in
	@./$< $@

config.status: configure Makefile
	./$< --no-create $(CONFIGURE_OPTS)

configure: configure.ac
	autoconf

### TESTING

bedwyr: $(bedwyr_prefix).$(BEST_SUFFIX)
	@ln -svf bedwyr.$(BEST_SUFFIX) $@

.PHONY: run test test_ndcore test_batyping test_input test_prover test_bedwyr

ifeq ($(TARGET),)
test:
	@$(MAKE) test_ndcore
	@echo
	@$(MAKE) test_batyping
	@echo
	@$(MAKE) test_input
	@echo
	@$(MAKE) test_prover
	@echo
	@$(MAKE) test_bedwyr
else
test:
	@$(MAKE) test_$(TARGET)
endif

test_ndcore: $(ndcore_dir)/test.$(BEST_SUFFIX)
	@echo '** Testing the core LLambda library **'
	@_build/$<
	@echo " ***"

test_batyping: src/batyping/test.$(BEST_SUFFIX)
	@echo '** Testing the Bedwyr-Abella typing library **'
	@_build/$<
	@echo " ***"

test_input: src/input/test.$(BEST_SUFFIX)
	@echo '** Testing the *.def and REPL input library **'
	@_build/$<
	@echo " ***"

test_prover: src/prover/test.$(BEST_SUFFIX)
	@echo '** Testing the theorem prover library **'
	@_build/$<
	@echo " ***"

test_bedwyr: bedwyr
	@echo '** Testing bedwyr on examples **'
	@time for i in $(TEST_EXAMPLES) ; do \
	  echo "==== Running tests in $$i ====" ; \
	  if ./$< -t -I examples/$$i ; then echo "All done." ; \
	  else echo "Error." ; exit 1 ; fi ; \
	  done

ifeq ($(OCAMLDEBUG),)
  debug:
	@echo 'Debug information generation disabled,'
	@echo 'add "--enable-debug" to your ./configure options.'
else
  ifeq ($(OCAMLC),)
  debug:
	@echo 'Bytecode generation disabled,'
	@echo 'add "--enable-bytecode" to your ./configure options.'
  else
  debug: $(bedwyr_prefix).d.byte
	$(OCAMLDEBUG) _build/$<
  endif
endif

### DOC

.PHONY: doc ndcore_doc bedwyr_doc bedwyr_src_doc bedwyr_ref bedwyr_man

ifeq ($(OCAMLDOC),)
  doc:
	@echo 'Documentation generation disabled,'
	@echo 'add "--enable-doc" to your ./configure options.'
else
  NDCORE_ODOCS		= $(addsuffix .odoc,$(NDCORE_MODULES))
  BEDWYR_ODOCS_DIR	= $(src_docdir)
  ifeq ($(TARGET),)
  doc: ndcore_doc bedwyr_doc
  else
  doc: $(TARGET)_doc
  endif
endif

ndcore_doc: ndcore_src_doc

ndcore_src_doc: $(NDCORE_ODOCS)

bedwyr_doc: bedwyr_man bedwyr_src_doc bedwyr_refman

bedwyr_man: $(MANPAGES)

bedwyr_src_doc: $(BEDWYR_ODOCS_DIR)/index.html

src.odocl:
	@echo src/Bedwyr > $@
	@for i in ndcore batyping input prover ; do \
	  sed -e "s|^|src/$$i/|" src/$$i/$$i.mllib ; \
	  done >> $@

bedwyr_refman: doc/Makefile
	@make -C doc

### INSTALL

ifeq ($(TARGET),)
  install: install_ndcore install_bedwyr
else
  install: install_$(TARGET)
endif

ifneq ($(OCAMLDOC),)
  install_ndcore: install_ndcore_doc
  install_bedwyr: install_bedwyr_doc
endif

install_ndcore: install_ndcore_lib install_ndcore_files

install_ndcore_lib: $(NDCORE_LIB_FLS)
	@$(INSTALL_DIR) $(LIBDIR)
	@for i in $^ ; do $(INSTALL_DATA) _build/$$i $(LIBDIR) ; done

install_ndcore_files: $(NDCORE_FILES:=.gz)
	@$(INSTALL_DIR) $(DOCDIR)
	@for i in $^ ; do $(INSTALL_DATA) $$i $(DOCDIR) ; done

install_ndcore_doc: $(NDCORE_ODOCS)
	@$(INSTALL_DIR) $(DOCDIR)
	@for i in $^ ; do $(GZIP) _build/$$i ; \
	  $(INSTALL_DATA) _build/$$i.gz $(DOCDIR) ; \
	  done

install_bedwyr: install_bedwyr_bin install_bedwyr_files \
  install_bedwyr_man install_bedwyr_contrib install_bedwyr_examples

install_bedwyr_bin: $(BEDWYR_BINS)
	@$(INSTALL_DIR) $(BINDIR)
	@for i in $^ ; do $(INSTALL_BIN) _build/$$i $(BINDIR) ; done
	@ln -svf bedwyr.$(BEST_SUFFIX) $(BINDIR)/bedwyr

install_bedwyr_files: $(BEDWYR_FILES:=.gz)
	@$(INSTALL_DIR) $(DOCDIR)
	@for i in $^ ; do $(INSTALL_DATA) $$i $(DOCDIR) ; done

install_bedwyr_man: $(MANPAGES)
	@$(INSTALL_DIR) $(MANDIR)/man1
	@for i in $^ ; do $(INSTALL_DATA) $$i $(MANDIR)/man1 ; done
	@for i in $(addsuffix .1.gz,$(addprefix bedwyr.,$(BIN_SUFFIXES))) ; \
	  do ln -svf bedwyr.1.gz $(MANDIR)/man1/$$i ; done

install_bedwyr_contrib:
	@$(INSTALL_DIR) $(DATADIR)
	@for i in $(CONTRIB_FILES) ; do \
	  $(INSTALL_DATA) -D $$i $(DATADIR)/$$i ; done
	@$(INSTALL_DIR) $(VIMFILES)
	@for i in $(VIM_CONTRIB) ; do \
	  $(INSTALL_DATA) -D contrib/vim/$$i $(VIMFILES)/$$i ; done

install_bedwyr_examples:
	@$(INSTALL_DIR) $(DATADIR)
	@for i in $(EXAMPLES_FILES) ; do \
	  $(INSTALL_DATA) -D $$i $(DATADIR)/$$i ; done

install_bedwyr_doc: install_bedwyr_odocs install_bedwyr_refman

install_bedwyr_odocs: $(BEDWYR_ODOCS_DIR)/index.html
	@$(INSTALL_DIR) $(DOCDIR)/libref
	@$(INSTALL_DATA) _build/$(BEDWYR_ODOCS_DIR)/*.html \
	  _build/$(BEDWYR_ODOCS_DIR)/style.css $(DOCDIR)/libref

install_bedwyr_refman: doc/Makefile
	@make -C doc install

### ARCHIVES

.PHONY: dist archive
.SUFFIXES: .tar .tbz .tgz
#.PHONY: dist $(ndcore_dir)/ndcore.tar src/bedwyr.tar doc/manual.tar dist.tar

dist: archive deb

archive: $(BEDWYR_ARCH)

archive.tar: $(ARCH_FILES)
	@$(TAR) -cf $@ --xform 's|^|$(DIST_NAME)/|' $^

doc/archive.tar: doc/Makefile
	@$(MAKE) -C doc archive

$(DIST_NAME).tar: archive.tar doc/archive.tar
	@$(TAR) -cf $@ -T /dev/null
	@for i in $^ ; do $(TAR) -Af $@ $$i ; done

%.bz2: %
	@$(BZIP2) -k $<
.tar.tbz:
	@$(BZIP2) -k -c $< > $@
%.gz: %
	@$(GZIP) -c $< > $@
.tar.tgz:
	@$(GZIP) -c $< > $@

deb: orig_files debian_files
	@CONFIGURE_OPTS="--enable-deb" $(MAKE) -C $(DEB_DIST_NAME) deb_pkg

orig_files: $(DIST_NAME).tgz
	@$(TAR) -xf $< --xform 's|^$(DIST_NAME)/|$(DEB_DIST_NAME)/|'
	@cp -pvf $< $(DEB_NAME).orig.tar.gz

debian_files: $(addprefix debian-files/,$(DEBIAN_FILES))
	@$(TAR) -cvf - $^ --xform 's|^debian-files/|$(DEB_DIST_NAME)/debian/|' \
	  | $(TAR) -xpvf -

ifeq (0,$(MAKELEVEL))
  deb_pkg:
	@echo 'Use the "deb" target to ensure the necessary files exist.'
else
  deb_pkg:
	@DEBEMAIL="$(DEBEMAIL)" DEBFULLNAME="$(DEBFULLNAME)" $(DCH)
	@$(DEBUILD)
endif


### OTHER TARGETS

.PHONY: help mostlyclean clean distclean

help:
	@echo ' help           this message'
	@echo
	@echo '   check out "./configure --help" for more reading'
	@echo
	@echo ' build          default: build "bedwyr.($(BIN_SUFFIXES))"'
	@echo ' test           run all sorts of tests'
	@echo ' doc            build all sorts of doc'
	@echo ' install        install files wrt to $$DESTDIR and'
	@echo '                the parameters given to ./configure'
	@echo
	@echo ' dist           build archives and packages'
	@echo ' archive        build archives "$(DIST_NAME).($(ARCH_SUFFIXES))'
	@echo
	@echo ' help           display this message'
	@echo ' mostlyclean    remove compiled files'
	@echo ' clean          also remove Make-generated and backup files'
	@echo ' distclean      also remove configure-generated files'

mostlyclean:
	@$(OCAMLBUILD) -clean
	@rm -vf bedwyr

clean: mostlyclean doc/Makefile
	@$(MAKE) -C doc clean
	@$(FIND) . -name '*~' -exec rm -vf \{\} \;
	@rm -vf *.bz2 *.gz *.tar *.tbz *.tgz *.odocl
	@rm -vf *.build *.changes *.dsc *.deb
	@rm -rvf $(DEB_DIST_NAME)

distclean: clean doc/Makefile
	@rm -vf $(ac_config_files)
	@rm -vf config.status config.log configure
	@rm -rvf autom4te.cache
