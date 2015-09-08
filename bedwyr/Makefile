##############################################################################
#  Bedwyr prover                                                             #
#  Copyright (C) 2012-2015 Quentin Heath                                     #
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

# $(make) compiles
# $(make install) installs
# $(make dist) builds packages

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
		  graph-alt.def minmax.def peterson.def multisim.def \
		  tictactoe.def \
		  pi/pi_trace.def pi/corr-assert.def pi/pi_modal.def \
		  pi/pi_asserts.def

BUILD		= _build
bedwyr_prefix	= $(BUILD)/src/bedwyr
OPAM_PACKAGES	= opam-repo/packages

# Archived files

ARCH_FILES	= $(OCAML_FILES) $(BEDWYR_WRAPPER) \
		  $(SLIMMER_FILES) $(BEDWYR_FILES) COPYING $(MAN_FILES) \
		  $(CONTRIB_FILES) $(DESKTOP_FILES) $(ICONS_FILES) $(EXAMPLES_FILES) \
		  configure.ac Makefile Makefile.include.in \
		  myocamlbuild.ml install-sh

BEDWYR_ARCH	= $(addprefix $(DIST_NAME).,$(ARCH_SUFFIXES))

# Released files

BEDWYR_BINS	= $(addprefix $(bedwyr_prefix).,$(BIN_SUFFIXES)) $(BEDWYR_WRAPPER:.in=)
MANPAGES	= $(MAN_FILES:.in=) $(foreach m,$(BIN_SUFFIXES),$(MAN_FILES:.1.in=.$m.1))

SLIMMER_META	= src/META
SLIMMER_LIBS	= $(foreach l,$(BEDWYR_LIBS),\
		  $(addprefix $(BUILD)/src/$l/$l.,$(LIB_SUFFIXES)))
SLIMMER_PLUGINS	= $(foreach p,$(BEDWYR_PLUGINS),\
		  $(addprefix $(BUILD)/src/plugins/$p.,$(PLUGIN_SUFFIXES)))
SLIMMER_CMIS	= $(foreach l,$(BEDWYR_LIBS),$(BUILD)/src/$l/$l.cmi) \
		  $(foreach p,$(BEDWYR_PLUGINS),$(BUILD)/src/plugins/$p.cmi)
SLIMMER_MLIS	= $(foreach l,$(BEDWYR_LIBS),\
		  $(wildcard src/$l/$l/*.mli))
SLIMMER_FINDLIB	= $(SLIMMER_META) $(SLIMMER_LIBS) $(SLIMMER_PLUGINS) \
		  $(SLIMMER_CMIS)

BUILT_FILES	= $(BEDWYR_BINS) $(MANPAGES) $(SLIMMER_FINDLIB) \
		  $(CONTRIB_FILES:.in=) $(DESKTOP_FILES:.in=)

SRC_DOCDIR	= $(BUILD)/src.docdir

OPAM_FILES	= opam descr findlib url files/bedwyr.install

# Other files

NSIS_RC_FILES	= $(addprefix nsis-files/,$(filter %.rc,$(NSIS_FILES)))
COFF_FILES	= $(NSIS_RC_FILES:.rc=.o)
ifeq (,)
  OPAM_URL_SCHEME	= http
  OPAM_URL_FULL_PATH	= slimmer.gforge.inria.fr/releases/debian/pool/main/b/bedwyr/$(DEB_NAME).orig.tar.gz
else
  OPAM_URL_SCHEME	= file
  OPAM_URL_FULL_PATH	= $(HOME)/$(DEBIAN_VERSION)/$(DEB_NAME).orig.tar.gz
endif
OPAM_URL	= $(OPAM_URL_SCHEME)://$(OPAM_URL_FULL_PATH)

#
# BUILDING
#
##############################################################################

.SECONDEXPANSION:
.PHONY: build slimmer_lib

build: $(BUILT_FILES) bedwyr

slimmer_lib: $(SLIMMER_FINDLIB)

$(BUILD)/%.byte: $(OCAML_FILES:.in=)
	@$(OCAMLBUILD) $(patsubst $(BUILD)/%,%,$@)

$(BUILD)/%.native: $(OCAML_FILES:.in=)
	@$(OCAMLBUILD) $(patsubst $(BUILD)/%,%,$@)

$(BUILD)/%.cmi: $(OCAML_FILES:.in=)
	@$(OCAMLBUILD) $(patsubst $(BUILD)/%,%,$@)

$(BUILD)/%.cmo: $(OCAML_FILES:.in=)
	@$(OCAMLBUILD) $(patsubst $(BUILD)/%,%,$@)

$(BUILD)/%.cma: $(OCAML_FILES:.in=)
	@$(OCAMLBUILD) $(patsubst $(BUILD)/%,%,$@)

$(BUILD)/%.cmxa $(BUILD)/%.a: $(OCAML_FILES:.in=)
	@$(OCAMLBUILD) $(patsubst $(BUILD)/%,%,$@)

$(BUILD)/%.cmxs: %.mldylib $(OCAML_FILES:.in=)
	@$(OCAMLBUILD) $(patsubst $(BUILD)/%,%,$@)

$(BUILD)/%.docdir/index.html: $(OCAML_FILES:.in=) %.odocl
	@$(OCAMLBUILD) $(patsubst $(BUILD)/%,%,$@)

$(BUILD)/%.exe: nsis-files/$$(*F).o $(BUILD)/%.native
	$(MINGW32_LD) $^ -o $@

%.mldylib: %.mllib
	@ln -svf $(<F) $@

%.o: %.rc
	@$(MINGW32_WINDRES) $< $@

$(SLIMMER_META): $(SLIMMER_META).part $(BEDWYR_LIBS:%=src/%/META.part)
	@cat $< > $@
	@for i in $(BEDWYR_LIBS) ; do \
	  echo -e "\n# Specifications for the \"slimmer.$$i\" library" ; \
	  echo "package \"$$i\" (" ; \
	  sed -e 's|^|  |' src/$$i/META.part ; \
	  echo ')' ; \
	  done >> $@

contrib/rlwrap/$(RLWRAP_CONTRIB:.in=): $(BUILD)/src/interface/interface/rlwrap.$(BEST_SUFFIX) contrib/rlwrap/$(RLWRAP_CONTRIB)
	@cat $@.in > $@
	@$< >> $@

%:: config.status %.in Makefile
	@./$< $@
	@sed -i.bkp \
	  -e 's|+pkgdatadir+|$(pkgdatadir)|' \
	  -e 's|+bindir+|$(bindir)|' \
	  $@
	@rm -f $@.bkp

config.status: configure Makefile
	@[ -x $@ ] && ./$@ --recheck || ./$< --no-create $(CONFIGURE_OPTS)

configure: configure.ac
	autoconf

#
# TESTING
#
##############################################################################

.PHONY: bedwyr test test_libs \
  test_pack_ndcore test_pack_parsetree test_pack_prover test_pack_interface \
  test_bedwyr debug

bedwyr: $(bedwyr_prefix).$(BEST_SUFFIX)
	@ln -svf $< $@

test:
	@echo '** Testing bedwyr libraries **'
	@$(MAKE) test_libs
	@echo '** Testing bedwyr on examples **'
	@$(MAKE) test_bedwyr

ifeq ($(OCAMLFIND_OUNIT),)
  test_libs:
	@echo 'Unit testing disabled, install oUnit to enable.'
else
  test_libs: test_pack_ndcore test_pack_parsetree test_pack_prover test_pack_interface
endif

test_pack_%: $(BUILD)/src/$$*/$$*/test.$(BEST_SUFFIX)
	@echo -n 'Testing the $* module'
	@$< $(OUNIT_FLAGS)

test_bedwyr: bedwyr
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
	$(OCAMLDEBUG) $<
  endif
endif

#
# DOC
#
##############################################################################

.PHONY: doc bedwyr_doc slimmer_doc bedwyr_refman src_libref

ifeq ($(OCAMLDOC),)
  doc:
	@echo 'Documentation generation disabled,'
	@echo 'add "--enable-doc" to your ./configure options.'
else
  doc: bedwyr_doc slimmer_doc
endif

bedwyr_doc: bedwyr_refman

bedwyr_refman: doc/Makefile
	@$(MAKE) -C $(<D)

slimmer_doc: src_libref

src_libref: $(SRC_DOCDIR)/index.html

src.odocl: $(foreach m,$(BEDWYR_LIBS),src/$m/$m.mlpack)
	@rm -f $@
	@for i in $^ ; do \
	  sed -e "s|^|$$(dirname $$i)/|" -e '/Parser/d' $$i ; \
	  done >> $@

man/%.byte.1: man/%.1
	@echo ".so man1/$*.1" > $@

man/%.native.1: man/%.1
	@echo ".so man1/$*.1" > $@

man/%.exe.1: man/%.1
	@echo ".so man1/$*.1" > $@

man/%.html: man/%
	@groff -Thtml -mandoc $< > $@

%.html: %.md
	@markdown $< > $@

#
# INSTALL
#
##############################################################################

.PHONY: install \
  install_bedwyr install_bedwyr_bin install_bedwyr_files \
  install_bedwyr_man install_bedwyr_contrib install_bedwyr_link \
  install_bedwyr_icons install_bedwyr_hicolor install_bedwyr_pixmaps \
  install_bedwyr_examples \
  install_slimmer install_slimmer_lib install_slimmer_files \
  install_doc \
  install_bedwyr_doc install_bedwyr_refman \
  install_slimmer_doc install_src_libref

install: install_bedwyr install_slimmer

ifeq ($(OCAMLDOC),)
  install_doc:
	@echo 'Documentation generation disabled,'
	@echo 'add "--enable-doc" to your ./configure options.'
else
  install: install_doc
  install_doc: install_bedwyr_doc install_slimmer_doc
endif

install_bedwyr: install_bedwyr_bin install_bedwyr_files \
  install_bedwyr_man install_bedwyr_contrib install_bedwyr_link \
  install_bedwyr_icons install_bedwyr_examples

install_bedwyr_bin: $(BEDWYR_BINS)
	@$(INSTALL_DIR) $(BINDIR)
	@for i in $^ ; do $(INSTALL_BIN) $$i $(BINDIR) ; done

install_bedwyr_files: $(BEDWYR_FILES:=.gz)
	@$(INSTALL_DIR) $(DOCDIR)
	@for i in $^ ; do $(INSTALL_DATA) $$i $(DOCDIR) ; done

install_bedwyr_man: $(MANPAGES)
	@$(INSTALL_DIR) $(MANDIR)/man1
	@for i in $^ ; do $(INSTALL_DATA) $$i $(MANDIR)/man1 ; done

install_bedwyr_contrib: $(CONTRIB_FILES:.in=)
	@for i in $^ ; do \
	  $(INSTALL_DATA) -D $$i $(PKGDATADIR)/$$i ; done
ifneq ($(BASHCOMP_D),$(DESTDIR))
	@for i in $(BASH_CONTRIB) ; do \
	  $(INSTALL_DIR) $$(dirname $(BASHCOMP_D)/$$i) ; \
	  ln -svf $(pkgdatadir)/contrib/bash_completion.d/$$i $(BASHCOMP_D)/$$i ; done
endif
ifneq ($(VIMFILES),$(DESTDIR))
	@for i in $(VIM_CONTRIB) ; do \
	  $(INSTALL_DIR) $$(dirname $(VIMFILES)/$$i) ; \
	  ln -svf $(pkgdatadir)/contrib/vim/$$i $(VIMFILES)/$$i ; done
endif

install_bedwyr_link: $(DESKTOP_FILES:.in=)
	@$(INSTALL_DIR) $(DESKTOP_DIR)
	@$(INSTALL_DATA) $^ $(DESKTOP_DIR)

install_bedwyr_icons: install_bedwyr_hicolor install_bedwyr_pixmaps

install_bedwyr_hicolor: $(addprefix contrib/icons/,$(HICOLOR_ICONS))
	@for i in $(HICOLOR_ICONS) ; do \
	  $(INSTALL_DATA) -D contrib/icons/$$i  $(ICONS_DIR)/$$i ; done

install_bedwyr_pixmaps: $(addprefix contrib/icons/,$(PIXMAP_ICONS))
	@$(INSTALL_DIR) $(PIXMAPS_DIR)
	@$(INSTALL_DATA) $^ $(PIXMAPS_DIR)

install_bedwyr_examples:
	@for i in $(EXAMPLES_FILES) ; do \
	  $(INSTALL_DATA) -D $$i $(PKGDATADIR)/$$i ; done

install_slimmer: install_slimmer_lib install_slimmer_files

install_slimmer_lib: $(SLIMMER_FINDLIB) $(SLIMMER_MLIS)
	@$(INSTALL_DIR) $(OCAMLLIBDIR)
	@$(FINDLIB_INSTALL) $^

install_slimmer_files: $(SLIMMER_FILES:=.gz)
	@$(INSTALL_DIR) $(DOCDIR)
	@for i in $^ ; do $(INSTALL_DATA) $$i $(DOCDIR) ; done

install_bedwyr_doc: install_bedwyr_refman

install_bedwyr_refman: doc/Makefile
	@$(MAKE) -C $(<D) install

install_slimmer_doc: install_src_libref

install_src_libref: $(SRC_DOCDIR)/index.html
	@$(INSTALL_DIR) $(DOCDIR)/libref
	@$(INSTALL_DATA) $(SRC_DOCDIR)/*.html \
	  $(SRC_DOCDIR)/style.css $(DOCDIR)/libref

#
# ARCHIVES
#
##############################################################################

.PHONY: dist archive \
  deb deb_orig deb_debian deb_pkg \
  nsis nsis_orig_files nsis_files nsis_pkg \
  opam opam_publish $(OPAM_PACKAGES)/$(PACKAGE_TARNAME)/$(OPAM_NAME) \
  opam-files/findlib opam-files/url opam-files/files/bedwyr.install
.SUFFIXES: .tar .tbz .tgz

dist: archive opam deb nsis

archive: $(BEDWYR_ARCH)

archive.tar: $(ARCH_FILES)
	@$(TAR) -cpf $@ --xform 's|^|$(DIST_NAME)/|S' $^

doc/archive.tar: doc/Makefile
	@$(MAKE) -C $(<D) archive

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

opam: $(OPAM_PACKAGES)/$(PACKAGE_TARNAME)/$(OPAM_NAME)
	@opam update bedwyr

$(OPAM_PACKAGES)/$(PACKAGE_TARNAME)/$(OPAM_NAME): $(addprefix opam-files/,$(OPAM_FILES))
	@rm -rf $@
	@$(TAR) -cpf - $^ --xform 's|^opam-files/|$@/|S' | $(TAR) -xpf -

opam-files/findlib:
	@echo "slimmer" > $@
	@for i in $(BEDWYR_LIBS) ; do echo "slimmer.$$i" ; done >> $@

opam-files/url:
	@echo "archive: \"$(OPAM_URL)\"" > $@
	@echo -n "checksum: \"" >> $@
	@curl -L $(OPAM_URL) | md5sum | tr -d ' \n-' >> $@
	@echo "\"" >> $@

opam-files/files/bedwyr.install:
	@mkdir -p opam-files/files
	@echo "bin: [" > $@
	@for i in "_build/src/bedwyr.native" "contrib/bedwyr" ; do \
	  echo "  \"$$i\"" ; \
	  done >> $@
	@echo "]" >> $@
	@echo "man: [" >> $@
	@for i in ".native" "" ; do \
	  echo "  \"man/bedwyr$$i.1\" {\"man1/bedwyr$$i.1\"}" ; \
	  done >> $@
	@echo "]" >> $@
	@echo "lib: [" >> $@
	@for i in $(SLIMMER_FINDLIB) ; do \
	  echo "#  \"$$i\"" ; \
	  done >> $@
	@echo "]" >> $@
	@echo "share: [" >> $@
	@for i in $(RLWRAP_CONTRIB:.in=) ; do \
	  echo "  \"contrib/rlwrap/$$i\" {\"contrib/rlwrap/$$i\"}" ; \
	  done >> $@
	@for i in $(EXAMPLES_FILES) ; do \
	  echo "  \"$$i\" {\"$$i\"}" ; \
	  done >> $@
	@echo "]" >> $@

ifeq ($(OPAM_URL_SCHEME),file)
opam_publish: $(OPAM_URL_FULL_PATH)

$(OPAM_URL_FULL_PATH): $(notdir $(OPAM_URL_FULL_PATH))
	@mkdir -pv $(@D)
	@mv -vf $< $(@D)
endif

opam_publish:
	@make opam
	@opam upgrade bedwyr


deb: deb_orig deb_debian
	@CONFIGURE_OPTS="$(CONFIGURE_OPTS) --enable-deb" \
	  $(MAKE) -C $(DEB_DIST_NAME) deb_pkg

deb_orig: $(DEB_NAME).orig.tar.gz

$(DEB_NAME).orig.tar.gz: $(DIST_NAME).tgz
	@mkdir -p $(DEB_DIST_NAME)
	@find $(DEB_DIST_NAME) -maxdepth 1 -mindepth 1 \
	  -path $(DEB_DIST_NAME)/debian -prune -o -exec rm -rf {} +
	@$(TAR) -xvpf $< --xform 's|^$(DIST_NAME)/|$(DEB_DIST_NAME)/|S'
	@$(TAR) -cpzf $@ $(DEB_DIST_NAME)

deb_debian: $(addprefix debian-files/,$(DEBIAN_FILES))
	@rm -rf $(DEB_DIST_NAME)/debian
	@$(TAR) -cpf - $^ --xform 's|^debian-files/|$(DEB_DIST_NAME)/debian/|S' \
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
	@CONFIGURE_OPTS="$(CONFIGURE_OPTS) --enable-nsis --host=win32 \
	  --disable-bytecode --enable-nativecode --enable-doc" \
	  $(MAKE) -C nsis-build nsis_pkg
	@cp -pvf nsis-build/$(DIST_NAME)-installer.exe .

nsis_orig_files: $(DIST_NAME).tgz
	@mkdir -p nsis-build
	@find nsis-build -maxdepth 1 -mindepth 1 \
	  -path nsis-build/nsis-files -prune -o -exec rm -rf {} +
	@$(TAR) -xpf $< --xform 's|^$(DIST_NAME)/|nsis-build/|S'

nsis_files: $(addprefix nsis-files/,$(NSIS_FILES))
	@rm -rf nsis-build/nsis-files
	@$(TAR) -cpf - $^ --xform 's|^|nsis-build/|S' | $(TAR) -xpf -
	@sed -e 's|$$|\r|' COPYING > nsis-build/nsis-files/COPYING.txt

ifeq (0,$(MAKELEVEL))
  nsis_pkg:
	@echo 'Use the "nsis" target to ensure the necessary files exist.'
else
  nsis_pkg: $(filter %.exe contrib/emacs/% contrib/vim/%,$(BUILT_FILES)) bedwyr_doc
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
	@echo ' build          default: build binaries ($(PACKAGE_TARNAME).($(BIN_SUFFIXES)))'
	@echo ' test           run all sorts of tests'
	@echo ' doc            build all sorts of doc'
	@echo ' install        install files wrt to $$DESTDIR and'
	@echo '                the parameters given to ./configure'
	@echo
	@echo ' dist           build archives and packages'
	@echo ' archive        build archives ($(DIST_NAME).($(ARCH_SUFFIXES)))'
	@echo ' opam           build opam package ($(DEB_NAME)???)'
	@echo ' deb            build debian package ($(DEB_NAME)-1_*.deb)'
	@echo ' nsis           build windows installer ($(DIST_NAME)-installer.exe)'
	@echo
	@echo ' help           display this message'
	@echo ' mostlyclean    remove compiled files'
	@echo ' clean          also remove other make-generated files'
	@echo ' distclean      also remove configure-generated and backup files'

mostlyclean:
	@[[ -x $(BUILD)/sanitize.sh ]] && $(BUILD)/sanitize.sh || true
	@$(OCAMLBUILD) -clean
	@rm -vf nsis-files/*.o bedwyr

clean: doc/Makefile mostlyclean
	@$(MAKE) -C $(<D) clean
	@$(MAKE) -C examples/ccs_vp/timing clean
	@rm -vf $(addprefix opam-files/,$(OPAM_FILES))
	@rm -vf src/*/*.mldylib
	@rm -vf $(BEDWYR_BINS) $(MANPAGES) $(SLIMMER_FINDLIB)
	@rm -vf *.bz2 *.gz *.tar *.tbz *.tgz *.odocl $(MANPAGES:=.html) README.html
	@rm -vf *.debian.tar.xz *.build *.changes *.dsc *.deb *-installer.exe
	@rm -rvf $(DEB_DIST_NAME) nsis-build

distclean: doc/Makefile clean
	@$(MAKE) -C $(<D) distclean
	@$(FIND) . -name '*~' -exec rm -vf \{\} \;
	@rm -vf $(ac_config_files)
	@rm -vf config.status config.log configure
	@rm -rvf autom4te.cache
