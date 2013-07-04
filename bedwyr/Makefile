##############################################################################
#  Bedwyr prover                                                             #
#  Copyright (C) 2012-2013 Quentin Heath                                     #
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
#  You should have received a copy of the GNU General Public License along   #
#  with this program; if not, write to the Free Software Foundation, Inc.,   #
#  51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA.               #
##############################################################################

# $(make TARGET=$TARGET) compiles
# $(make TARGET=$TARGET install) installs
# $(make TARGET=$TARGET dist) builds packages
#
# $TARGET can be one of those:
# - "ndcore" for this library only
# - "bedwyr" for the program only
# - ""

#
# DEFINITIONS
#
##############################################################################

-include Makefile.include

#
# FILES
#
##############################################################################

TEST_EXAMPLES	= list.def internal/scoping.def internal/checks.def \
		  3bits.def lambda.def progs.def \
		  graph-alt.def minmax.def multisim.def \
		  tictactoe.def \
		  pi/pi_trace.def pi/corr-assert.def pi/pi_modal.def \
		  pi/pi_asserts.def

ndcore_dir	= src/ndcore
bedwyr_prefix	= src/bedwyr
src_docdir	= src.docdir
l_cclib		= -lflags -cclib,

# Archived files

ARCH_FILES	= $(OCAML_FILES) \
		  $(NDCORE_FILES) $(BEDWYR_FILES) COPYING $(MAN_FILES) \
		  $(CONTRIB_FILES) $(DESKTOP_FILES) $(ICONS) $(EXAMPLES_FILES) \
		  configure.ac Makefile Makefile.include.in \
		  myocamlbuild.ml.in _tags.in install-sh

BEDWYR_ARCH	= $(addprefix $(DIST_NAME).,$(ARCH_SUFFIXES))

# Released files

NDCORE_LIBS	= $(addprefix $(ndcore_dir)/ndcore.,$(LIB_SUFFIXES))
NDCORE_MLS	= $(filter-out $(ndcore_dir)/test.ml,$(wildcard $(ndcore_dir)/*.ml))
NDCORE_MLIS	= $(wildcard $(ndcore_dir)/*.mli)
NDCORE_MODULES	= $(basename $(NDCORE_MLS))
ifneq ($(BEST_SUFFIX),)
  NDCORE_CMIS	= $(addsuffix .cmi,$(NDCORE_MODULES))
endif
SLIMMER_META	= src/META
BEDWYR_BINS	= $(addprefix $(bedwyr_prefix).,$(BIN_SUFFIXES))
ifeq ($(TARGET),ndcore)
  BUILT_FILES	= $(NDCORE_LIBS) $(NDCORE_CMIS) $(SLIMMER_META)
else
  ifeq ($(TARGET),bedwyr)
  BUILT_FILES	= $(BEDWYR_BINS) $(MANPAGES) $(DESKTOP_FILES:.in=)
  else
    ifeq ($(TARGET),)
  BUILT_FILES	= $(NDCORE_LIBS) $(NDCORE_CMIS) $(SLIMMER_META) \
		  $(BEDWYR_BINS) $(MANPAGES) $(DESKTOP_FILES:.in=)
    endif
  endif
endif
MANPAGES	= $(MAN_FILES:.in=.gz)

# Other files

NSIS_RC_FILES	= $(addprefix nsis-files/,$(filter %.rc,$(NSIS_FILES)))
COFF_FILES	= $(NSIS_RC_FILES:.rc=.o)

#
# BUILDING
#
##############################################################################

.PHONY: build

build: $(BUILT_FILES) bedwyr

%.byte: $(OCAML_IN_FILES:.in=)
	@$(OCAMLBUILD) $@

%.native: $(OCAML_IN_FILES:.in=)
	@$(OCAMLBUILD) $@

%.cmi: $(OCAML_IN_FILES:.in=)
	@$(OCAMLBUILD) $@

%.cma: $(OCAML_IN_FILES:.in=)
	@$(OCAMLBUILD) $@

%.cmxa %.a: $(OCAML_IN_FILES:.in=)
	@$(OCAMLBUILD) $@

%.docdir/index.html: $(OCAML_IN_FILES:.in=) %.odocl
	@$(OCAMLBUILD) $@

%.odoc: $(OCAML_IN_FILES:.in=)
	@$(OCAMLBUILD) $@

%.exe: $(OCAML_IN_FILES:.in=) $(COFF_FILES)
	@$(OCAMLBUILD) -just-plugin
	@$(OCAMLBUILDWIN32) $(addprefix $(l_cclib)../,$(COFF_FILES)) $*.native
	@mv -vi _build/$*.native _build/$@

%.o: %.rc
	@$(MINGW32_WINDRES) $< $@

$(SLIMMER_META): $(SLIMMER_META).part $(BEDWYR_MODULES:%=src/%/META.part)
	@cat $< > $@
	@for i in $(BEDWYR_MODULES) ; do \
	  echo -e "\n# Specifications for the \"slimmer.$$i\" library" ; \
	  echo "package \"$$i\" (" ; \
	  sed -e 's|^|  |' src/$$i/META.part ; \
	  echo ')' ; \
	  done >> $@

%:: config.status %.in Makefile
	@./$< $@
	@sed -i \
	  -e 's|+pkgdatadir+|$(pkgdatadir)|' \
	  -e 's|+bindir+|$(bindir)|' \
	  $@

config.status: configure Makefile
	@[ -x $@ ] && ./$@ --recheck || ./$< --no-create $(CONFIGURE_OPTS)

configure: configure.ac
	autoconf

#
# TESTING
#
##############################################################################

bedwyr: $(bedwyr_prefix).$(BEST_SUFFIX)
	@ln -svf _build/$< $@

.PHONY: test test_ndcore test_batyping test_input test_prover test_bedwyr debug

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

#
# DOC
#
##############################################################################

.PHONY: doc ndcore_doc ndcore_src_doc bedwyr_doc bedwyr_src_doc bedwyr_refman

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

bedwyr_doc: bedwyr_src_doc bedwyr_refman

bedwyr_src_doc: $(BEDWYR_ODOCS_DIR)/index.html

src.odocl: $(foreach m,$(BEDWYR_MODULES),src/$m/$m.mllib)
	@echo src/Bedwyr > $@
	@for i in $(BEDWYR_MODULES) ; do \
	  sed -e "s|^|src/$$i/|" src/$$i/$$i.mllib ; \
	  done >> $@

bedwyr_refman: doc/Makefile
	@make -C doc

#
# INSTALL
#
##############################################################################

.PHONY: install \
  install_ndcore install_ndcore_doc install_ndcore_lib \
  install_ndcore_files \
  install_bedwyr install_bedwyr_doc install_bedwyr_bin install_bedwyr_files \
  install_bedwyr_man install_bedwyr_contrib install_bedwyr_link \
  install_bedwyr_icons install_bedwyr_examples install_bedwyr_odocs \
  install_bedwyr_refman

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

install_ndcore_lib: $(SLIMMER_META) $(NDCORE_LIBS) \
  $(NDCORE_CMIS) $(NDCORE_MLIS)
	@$(INSTALL_DIR) $(OCAMLLIBDIR)
	@$(FINDLIB_INSTALL) $< $(wildcard $(^:%=_build/%))

install_ndcore_files: $(NDCORE_FILES:=.gz)
	@$(INSTALL_DIR) $(DOCDIR)
	@for i in $^ ; do $(INSTALL_DATA) $$i $(DOCDIR) ; done

install_ndcore_doc: $(NDCORE_ODOCS)
	@$(INSTALL_DIR) $(DOCDIR)
	@for i in $^ ; do $(GZIP) _build/$$i ; \
	  $(INSTALL_DATA) _build/$$i.gz $(DOCDIR) ; \
	  done

install_bedwyr: install_bedwyr_bin install_bedwyr_files \
  install_bedwyr_man install_bedwyr_contrib install_bedwyr_link \
  install_bedwyr_icons install_bedwyr_examples

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
	@for i in $(CONTRIB_FILES) ; do \
	  $(INSTALL_DATA) -D $$i $(PKGDATADIR)/$$i ; done
ifneq ($(VIMFILES),$(DESTDIR))
	@for i in $(VIM_CONTRIB) ; do \
	  $(INSTALL_DIR) $$(dirname $(VIMFILES)/$$i) ; \
	  ln -svf $(pkgdatadir)/contrib/vim/$$i $(VIMFILES)/$$i ; done
endif

install_bedwyr_link: $(DESKTOP_FILES:.in=)
	@$(INSTALL_DIR) $(DESKTOP_DIR)
	@$(INSTALL_DATA) $^ $(DESKTOP_DIR)

install_bedwyr_icons:
	@$(INSTALL_DIR) $(PIXMAPS_DIR)
	@$(INSTALL_DATA) contrib/icons/bedwyr_32x32.xpm $(PIXMAPS_DIR)
	@for i in $(HICOLOR_ICONS) ; do \
	  $(INSTALL_DATA) -D contrib/icons/$$i  $(ICONS_DIR)/$$i ; done

install_bedwyr_examples:
	@for i in $(EXAMPLES_FILES) ; do \
	  $(INSTALL_DATA) -D $$i $(PKGDATADIR)/$$i ; done

install_bedwyr_doc: install_bedwyr_odocs install_bedwyr_refman

install_bedwyr_odocs: $(BEDWYR_ODOCS_DIR)/index.html
	@$(INSTALL_DIR) $(DOCDIR)/libref
	@$(INSTALL_DATA) _build/$(BEDWYR_ODOCS_DIR)/*.html \
	  _build/$(BEDWYR_ODOCS_DIR)/style.css $(DOCDIR)/libref

install_bedwyr_refman: doc/Makefile
	@make -C doc install

#
# ARCHIVES
#
##############################################################################

.PHONY: dist archive deb deb_orig deb_debian deb_pkg
.SUFFIXES: .tar .tbz .tgz

dist: archive deb nsis

archive: $(BEDWYR_ARCH)

archive.tar: $(ARCH_FILES)
	@$(TAR) -cpf $@ --xform 's|^|$(DIST_NAME)/|' $^

doc/archive.tar: doc/Makefile
	@$(MAKE) -C doc archive

$(DIST_NAME).tar: archive.tar doc/archive.tar
	@$(TAR) -cpf $@ -T /dev/null
	@for i in $^ ; do $(TAR) -Af $@ $$i ; done

%.bz2: %
	@$(BZIP2) -k $<
.tar.tbz:
	@$(BZIP2) -k -c $< > $@
%.gz: %
	@$(GZIP) -c $< > $@
.tar.tgz:
	@$(GZIP) -c $< > $@

deb: deb_orig deb_debian
	@CONFIGURE_OPTS="$(CONFIGURE_OPTS) --enable-deb" \
	  $(MAKE) -C $(DEB_DIST_NAME) deb_pkg

deb_orig: $(DEB_NAME).orig.tar.gz

$(DEB_NAME).orig.tar.gz: $(DIST_NAME).tgz
	@mkdir -p $(DEB_DIST_NAME)
	@find $(DEB_DIST_NAME) -maxdepth 1 -mindepth 1 \
	  -path $(DEB_DIST_NAME)/debian -prune -o -exec rm -rf {} +
	@$(TAR) -xpf $< --xform 's|^$(DIST_NAME)/|$(DEB_DIST_NAME)/|'
	@$(TAR) -cpzf $@ $(DEB_DIST_NAME)

deb_debian: $(addprefix debian-files/,$(DEBIAN_FILES))
	@rm -rf $(DEB_DIST_NAME)/debian
	@$(TAR) -cpf - $^ --xform 's|^debian-files/|$(DEB_DIST_NAME)/debian/|' \
	  | $(TAR) -xpf -

ifeq (0,$(MAKELEVEL))
  deb_pkg:
	@echo 'Use the "deb" target to ensure the necessary files exist.'
else
  deb_pkg:
	@DEBEMAIL="$(DEBEMAIL)" DEBFULLNAME="$(DEBFULLNAME)" $(DCH)
	@$(DEBUILD)
endif

nsis: nsis_orig_files nsis_files
	@CONFIGURE_OPTS="$(CONFIGURE_OPTS) --enable-nsis \
	  --enable-bytecode --enable-win32 --enable-doc --without-xmlm" \
	  $(MAKE) -C nsis-build nsis_pkg
	@cp -pvf nsis-build/$(DIST_NAME)-installer.exe .

nsis_orig_files: $(DIST_NAME).tgz
	@mkdir -p nsis-build
	@find nsis-build -maxdepth 1 -mindepth 1 \
	  -path nsis-build/nsis-files -prune -o -exec rm -rf {} +
	@$(TAR) -xpf $< --xform 's|^$(DIST_NAME)/|nsis-build/|'

nsis_files: $(addprefix nsis-files/,$(NSIS_FILES))
	@rm -rf nsis-build/nsis-files
	@$(TAR) -cpf - $^ --xform 's|^|nsis-build/|' | $(TAR) -xpf -
	@sed -e 's|$$|\r|' COPYING > nsis-build/nsis-files/COPYING.txt

ifeq (0,$(MAKELEVEL))
  nsis_pkg:
	@echo 'Use the "nsis" target to ensure the necessary files exist.'
else
  nsis_pkg: build doc
	@mv _build/$(src_docdir)/index.html _build/$(src_docdir)/index.htm
	@find _build/$(src_docdir)/ -type f \
	  -exec sed -i -e 's|\<index.html\>|index.htm|' {} \;
	@$(MAKENSIS) nsis-files/bedwyr.nsi
endif


#
# OTHER TARGETS
#
##############################################################################

.PHONY: help mostlyclean clean distclean

help:
	@echo ' help           this message'
	@echo
	@echo '   check out "./configure --help" for more reading'
	@echo
	@echo ' build          default: build binaries (bedwyr.($(BIN_SUFFIXES)))'
	@echo ' test           run all sorts of tests'
	@echo ' doc            build all sorts of doc'
	@echo ' install        install files wrt to $$DESTDIR and'
	@echo '                the parameters given to ./configure'
	@echo
	@echo ' dist           build archives and packages'
	@echo ' archive        build archives ($(DIST_NAME).($(ARCH_SUFFIXES)))'
	@echo ' deb            build debian package ($(DEB_NAME)-1_*.deb)'
	@echo ' nsis           build windows installer ($(DIST_NAME)-installer.exe)'
	@echo
	@echo ' help           display this message'
	@echo ' mostlyclean    remove compiled files'
	@echo ' clean          also remove make-generated and backup files'
	@echo ' distclean      also remove configure-generated files'

mostlyclean:
	@[[ -x _build/sanitize.sh ]] && _build/sanitize.sh || true
	@$(OCAMLBUILD) -clean
	@rm -vf nsis-files/*.o bedwyr

clean: mostlyclean doc/Makefile
	@$(MAKE) -C doc clean
	@$(MAKE) -C examples/ccs_vp/timing clean
	@$(FIND) . -name '*~' -exec rm -vf \{\} \;
	@rm -vf $(SLIMMER_META)
	@rm -vf *.bz2 *.gz *.tar *.tbz *.tgz *.odocl $(MANPAGES)
	@rm -vf *.build *.changes *.dsc *.deb *-installer.exe
	@rm -rvf $(DEB_DIST_NAME) nsis-build

distclean: clean doc/Makefile
	@$(MAKE) -C doc distclean
	@rm -vf $(ac_config_files)
	@rm -vf config.status config.log configure
	@rm -rvf autom4te.cache
