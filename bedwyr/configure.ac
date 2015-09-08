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

m4_define([M4_VERSION_MAJOR],1)
m4_define([M4_VERSION_MINOR],4)
m4_define([M4_VERSION_PATCH],0)
m4_define([M4_VERSION_BUILD],0)
m4_define([M4_VERSION_DEV],beta12)
m4_define([M4_VERSION1],[M4_VERSION_MAJOR.M4_VERSION_MINOR])
m4_define([M4_VERSION2],m4_if(M4_VERSION_PATCH,0,
          [M4_VERSION1],[M4_VERSION1.M4_VERSION_PATCH]))
m4_define([M4_VERSION3],m4_if(M4_VERSION_BUILD,0,
          [M4_VERSION2],[M4_VERSION2.M4_VERSION_BUILD]))
m4_define([M4_VERSION],m4_if(M4_VERSION_DEV,,
          [M4_VERSION3],[M4_VERSION3-M4_VERSION_DEV]))
AC_INIT([Bedwyr],[M4_VERSION],
        [https://gforge.inria.fr/tracker/?atid=1543&group_id=367],
        [bedwyr],[http://slimmer.gforge.inria.fr/bedwyr/])
VERSION_MAJOR=M4_VERSION_MAJOR
VERSION_MINOR=M4_VERSION_MINOR
VERSION_PATCH=M4_VERSION_PATCH
VERSION_BUILD=M4_VERSION_BUILD
VERSION_DEV=M4_VERSION_DEV
AC_PREREQ(2.60)
AC_CONFIG_SRCDIR([src/bedwyr.ml])

#
# Common build stuff
#
##############################################################################

AC_PATH_PROG(BASH,bash,no)
AS_IF([test "X$BASH" = Xno],
      [AC_MSG_ERROR(Cannot find bash.)])

AC_PATH_PROG(TAR,tar,no)
AS_IF([test "X$TAR" = Xno],
      [AC_MSG_ERROR(Cannot find tar.)])

AC_PATH_PROG(FIND,find,no)
AS_IF([test "X$FIND" = Xno],
      [AC_MSG_ERROR(Cannot find find.)])

AC_PATH_PROG(GZIP,gzip,no)
AS_IF([test "X$GZIP" = Xno],
      [AC_MSG_WARN(Cannot find gzip.)],
      [ARCH_SUFFIXES="$ARCH_SUFFIXES tgz"])

AC_PATH_PROG(BZIP2,bzip2,no)
AS_IF([test "X$BZIP2" = Xno],
      [AC_MSG_WARN(Cannot find bzip2.)],
      [ARCH_SUFFIXES="$ARCH_SUFFIXES tbz"])

#
# OCaml stuff (only $OCAML[C|DEBUG|BUILD] and $MINGW32_* are actually used)
#
##############################################################################

AC_PATH_PROGS(OCAMLFIND,ocamlfind.opt ocamlfind,no)
AS_IF([test "X$OCAMLFIND" = Xno],
      [AC_MSG_ERROR(Cannot find ocamlfind. Install findlib.)])

AC_MSG_CHECKING(if debugging information should be added)
AC_ARG_ENABLE([debug],
              AC_HELP_STRING([--enable-debug],
                             [add debugging/profiling information (no)]),
              [AC_MSG_RESULT($enable_debug)],
              [AC_MSG_RESULT(no)])
if test "X$enable_debug" = Xyes ; then
	BYTE_BIN_SUFFIX="d.byte"
	NATIVE_BIN_SUFFIX="p.native"
	BYTE_LIBS_SUFFIX="d.cma"
	NATIVE_LIBS_SUFFIX="p.a p.cmxa"
	NATIVE_SHARED_LIBS_SUFFIX="p.cmxs"
else
	BYTE_BIN_SUFFIX="byte"
	NATIVE_BIN_SUFFIX="native"
	BYTE_LIBS_SUFFIX="cma"
	NATIVE_LIBS_SUFFIX="a cmxa"
	NATIVE_SHARED_LIBS_SUFFIX="cmxs"
fi

WIN32_BIN_SUFFIX="exe"
AC_MSG_CHECKING(if native win32 code should be generated)
AC_ARG_ENABLE([win32],
              AC_HELP_STRING([--enable-win32],[output native win32 code (no)]),
              [AC_MSG_RESULT($enable_win32)],
              [AC_MSG_RESULT(no)])
if test "X$enable_win32" = Xyes ; then
	MINGW32_OCAMLFIND_CONF=/etc/i686-w64-mingw32-ocamlfind.conf
	AC_CHECK_FILE($MINGW32_OCAMLFIND_CONF,,
	              MINGW32_OCAMLFIND_CONF=no)
	AS_IF([test "X$MINGW32_OCAMLFIND_CONF" = Xno],
              [AC_MSG_ERROR(Cannot find findlib support for native win32 code generation. Install mingw32-ocaml.)])
	BIN_SUFFIXES="$BIN_SUFFIXES $WIN32_BIN_SUFFIX"
	BEST_SUFFIX="$WIN32_BIN_SUFFIX"
	OCAML_VERSION=$(OCAMLFIND_CONF="$MINGW32_OCAMLFIND_CONF" "$OCAMLFIND" ocamlopt -version)

	AC_PATH_PROGS(MINGW32_WINDRES,
	              i686-w64-mingw32-windres.opt i686-w64-mingw32-windres \
	                i586-mingw32msvc-windres.opt i586-mingw32msvc-windres,
	              no)
	AS_IF([test "X$MINGW32_WINDRES" = Xno],
	      [AC_MSG_ERROR(Cannot find windres. Install mingw32-binutils.)])
fi

AC_MSG_CHECKING(if bytecode should be generated)
AC_ARG_ENABLE([bytecode],
              AC_HELP_STRING([--enable-bytecode],[output bytecode (yes)]),
              [AC_MSG_RESULT($enable_bytecode)],
              [AC_MSG_RESULT(yes)])
if test "X$enable_bytecode" != Xno ; then
	AC_PATH_PROGS(OCAMLC,ocamlc.opt ocamlc,no)
	AS_IF([test "X$OCAMLC" = Xno],
	      [AC_MSG_ERROR(Cannot find a bytecode compiler.)])
	LIB_SUFFIXES="$LIB_SUFFIXES $BYTE_LIBS_SUFFIX"
	PLUGIN_SUFFIXES="$PLUGIN_SUFFIXES $BYTE_LIBS_SUFFIX"
	BIN_SUFFIXES="$BIN_SUFFIXES $BYTE_BIN_SUFFIX"
	BEST_SUFFIX="$BYTE_BIN_SUFFIX"
	OCAML_VERSION=$("$OCAMLC" -version)
fi

AC_MSG_CHECKING(if native code should be generated)
AC_ARG_ENABLE([nativecode],
              AC_HELP_STRING([--enable-nativecode],[output native code (no)]),
              [AC_MSG_RESULT($enable_nativecode)],
              [AC_MSG_RESULT(no)])
if test "X$enable_nativecode" = Xyes ; then
	AC_PATH_PROGS(OCAMLOPT,ocamlopt.opt ocamlopt,no)
	AS_IF([test "X$OCAMLOPT" = Xno],
	      [AC_MSG_ERROR(Cannot find a native code compiler.)])
	LIB_SUFFIXES="$LIB_SUFFIXES $NATIVE_LIBS_SUFFIX"
	PLUGIN_SUFFIXES="$PLUGIN_SUFFIXES $NATIVE_SHARED_LIBS_SUFFIX"
	BIN_SUFFIXES="$BIN_SUFFIXES $NATIVE_BIN_SUFFIX"
	BEST_SUFFIX="$NATIVE_BIN_SUFFIX"
	OCAML_VERSION=$("$OCAMLOPT" -version)
fi

AS_VERSION_COMPARE([$OCAML_VERSION],[3.11],
                   AC_MSG_ERROR([OCaml version $OCAML_VERSION is not supported (>=3.11 required).]))

if test "$BEST_SUFFIX" = "" ; then
	AC_MSG_WARN(You may want to enable at least one type of compilation.)
else
	if test "X$enable_debug" = Xyes ; then
		AC_PATH_PROGS(OCAMLDEBUG,ocamldebug.opt ocamldebug,no)
		AS_IF([test "X$OCAMLDEBUG" = Xno],
		      [AC_MSG_ERROR(Cannot find ocamldebug.)])
	fi

	AC_PATH_PROGS(OCAMLDEP,ocamldep.opt ocamldep,no)
	AS_IF([test "X$OCAMLDEP" = Xno],
	      [AC_MSG_ERROR(Cannot find ocamldep.)])

	AC_PATH_PROGS(OCAMLLEX,ocamllex.opt ocamllex,no)
	AS_IF([test "X$OCAMLLEX" = Xno],
	      [AC_MSG_ERROR(Cannot find ocamllex.)])

	AC_PATH_PROGS(OCAMLYACC,ocamlyacc.opt ocamlyacc,no)
	AS_IF([test "X$OCAMLYACC" = Xno],
	      [AC_MSG_ERROR(Cannot find ocamlyacc.)])

	AC_PATH_PROGS(OCAMLBUILD,ocamlbuild.opt ocamlbuild.native ocamlbuild ocamlbuild.byte,no)
	AS_IF([test "X$OCAMLBUILD" = Xno],
	      [AC_MSG_ERROR(Cannot find ocamlbuild.)])
fi

#
# Optional functionalities
#
##############################################################################

AC_MSG_CHECKING(for findlib (runtime version))
if ocamlfind_findlib=$(OCAMLFIND_CONF="$OCAMLFIND_CONF" "$OCAMLFIND" query findlib 2>/dev/null) ; then
	AC_MSG_RESULT($ocamlfind_findlib)
	FINDLIB_PACKAGE_DIRECTORY="Findlib.package_directory"
	FINDLIB_TAG="findlib"
else
	AC_MSG_RESULT(no)
fi

AC_MSG_CHECKING(for xmlm)
AC_ARG_WITH([xmlm],
            AC_HELP_STRING([--with-xmlm],
                           [add support for XML proof skeleton export (auto)]),
            [],[with_xmlm="auto"])
if test "X$with_xmlm" = Xno ; then
	AC_MSG_RESULT(no)
else
	if ocamlfind_xmlm=$("$OCAMLFIND" query xmlm 2>/dev/null) ; then
		AC_MSG_RESULT(${ocamlfind_xmlm})
		OCAMLFIND_XMLM="${ocamlfind_xmlm}"
                TABLE_XML_EXPORT="tableXmlExport"
                PLUGINS_CMA="${PLUGINS_CMA} ${TABLE_XML_EXPORT}.cma"
                PLUGINS_CMXA="${PLUGINS_CMXA} ${TABLE_XML_EXPORT}.cmxa"
                PLUGINS_CMXS="${PLUGINS_CMXS} ${TABLE_XML_EXPORT}.cmxs"
	else
		AC_MSG_RESULT(no)
		AS_IF([test "X$with_xmln" = Xyes],
		      [AC_MSG_ERROR(Cannot find xmlm.)])
	fi
fi

AC_MSG_CHECKING(for oUnit)
if ocamlfind_oUnit=$("$OCAMLFIND" query oUnit 2>/dev/null) ; then
	AC_MSG_RESULT(${ocamlfind_oUnit})
	OCAMLFIND_OUNIT="${ocamlfind_oUnit}"
else
	AC_MSG_RESULT(no (library tests will be disabled))
fi

#
# Documentation stuff
#
##############################################################################

AC_MSG_CHECKING(if the documentation should be built)
AC_ARG_ENABLE([doc],
	AC_HELP_STRING([--enable-doc],[build the complete documentation (no)]),
	[AC_MSG_RESULT($enable_doc)],
	[AC_MSG_RESULT(no)])
if test "X$enable_doc" = Xyes ; then
	AC_PATH_PROGS(OCAMLDOC,ocamldoc.opt ocamldoc,no)
	AS_IF([test "X$OCAMLDOC" = Xno],
	      [AC_MSG_ERROR(Cannot find ocamldoc.)])

	#AC_PATH_PROG(FIG2DEV,fig2dev,no)
	#if test "X$FIG2DEV" = Xno ; then
	#	AC_MSG_ERROR(Cannot find fig2dev. Install transfig.)
	#fi

	AC_PATH_PROG(LATEX,pdflatex latex,no)
	AS_IF([test "X$LATEX" = Xno],
	      [AC_MSG_ERROR(Cannot find a latex alternative.)])

	AC_PATH_PROG(KPSEWHICH,kpsewhich,no)
	if test "X$KPSEWHICH" = Xno ; then
		AC_CHECK_FILE(/usr/share/texmf-dist/tex/generic/xypic/xypic.sty,,
		              AC_CHECK_FILE(/usr/share/texlive/texmf-dist/tex/generic/xypic/xypic.sty,,
		                            AC_MSG_ERROR(Cannot find xypic.sty. Install texlive-pictures.)))
		AC_CHECK_FILE(/usr/share/texmf-dist/tex/latex/txfonts/txfonts.sty,,
		              AC_CHECK_FILE(/usr/share/texlive/texmf-dist/tex/latex/txfonts/txfonts.sty,,
		                            AC_MSG_ERROR(Cannot find txfonts.sty. Install texlive-fonts-recommended.)))
	else
		AC_MSG_CHECKING(for xypic.sty)
		if ! kpsewhich_xypic=$("$KPSEWHICH" xypic.sty) ; then
			AC_MSG_RESULT(no)
			AC_MSG_ERROR(Cannot find xypic.sty. Install texlive-pictures.)
		fi
		AC_MSG_RESULT(${kpsewhich_xypic})
		AC_MSG_CHECKING(for txfonts.sty)
		if ! kpsewhich_txfonts=$("$KPSEWHICH" txfonts.sty) ; then
			AC_MSG_RESULT(no)
			AC_MSG_ERROR(Cannot find xypic.sty. Install texlive-fonts-recommended.)
		fi
		AC_MSG_RESULT(${kpsewhich_txfonts})
	fi

	AC_PATH_PROG(BIBTEX,bibtex,no)
	AS_IF([test "X$BIBTEX" = Xno],
	      [AC_MSG_ERROR(Cannot find bibtex.)])

	AC_PATH_PROG(DVIPS,dvips,no)
	AS_IF([test "X$DVIPS" = Xno],
	      [AC_MSG_ERROR(Cannot find dvips.)])

	AC_PATH_PROG(PS2PDF,ps2pdf,no)
	AS_IF([test "X$PS2PDF" = Xno],
	      [AC_MSG_ERROR(Cannot find ps2pdf. Install ghostscript.)])

	AC_PATH_PROGS(HEVEA,hevea.opt hevea,no)
	AS_IF([test "X$HEVEA" = Xno],
	      [AC_MSG_ERROR(Cannot find hevea.)])

	AC_PATH_PROGS(BIBHVA,bibhva.opt bibhva,no)
	AS_IF([test "X$BIBHVA" = Xno],
	      [AC_MSG_ERROR(Cannot find bibhva.)])

	AC_PATH_PROG(IMAGEN,imagen,no)
	AS_IF([test "X$IMAGEN" = Xno],
	      [AC_MSG_ERROR(Cannot find imagen.)])

	AC_PATH_PROGS(HACHA,hacha.opt hacha,no)
	AS_IF([test "X$HACHA" = Xno],
	      [AC_MSG_ERROR(Cannot find hacha.)])
fi

#
# Installation-related options
#
##############################################################################

AC_MSG_CHECKING(if bash completion files should be installed)
AC_ARG_WITH([bash_completion],
            AC_HELP_STRING([--with-bash_completion],[install bash completion files (no)]),
            [AC_MSG_RESULT($with_bash_completion)],
            [AC_MSG_RESULT(no)])
AS_IF([test "X$with_bash_completion" = Xyes],
      [BASHCOMP_D='${sysconfdir}/bash_completion.d'])

AC_MSG_CHECKING(if vim files should be installed)
AC_ARG_WITH([vimfiles],
            AC_HELP_STRING([--with-vimfiles],[install vim files (no)]),
            [AC_MSG_RESULT($with_vimfiles)],
            [AC_MSG_RESULT(no)])
AS_IF([test "X$with_vimfiles" = Xyes],
      [VIMFILES='${datarootdir}/vim/vimfiles'])

AC_PROG_INSTALL

AC_MSG_CHECKING(if a Debian package should be built)
AC_ARG_ENABLE([deb],
	AC_HELP_STRING([--enable-deb],[build deb and debsrc packages (no)]),
	[AC_MSG_RESULT($enable_deb)],
	[AC_MSG_RESULT(no)])
if test "X$enable_deb" = Xyes ; then
	AC_PATH_PROG(DPKG_BUILDPACKAGE,dpkg-buildpackage,no)
	AS_IF([test "X$DPKG_BUILDPACKAGE" = Xno],
	      [AC_MSG_ERROR(Cannot find dpkg-buildpackage. Install dpkg-dev.)])

	AC_PATH_PROG(DCH,dch,no)
	AS_IF([test "X$DCH" = Xno],
	      [AC_MSG_ERROR(Cannot find dch. Install devscripts.)])

	AC_PATH_PROG(DEBUILD,debuild,no)
	AS_IF([test "X$DEBUILD" = Xno],
	      [AC_MSG_ERROR(Cannot find debuild. Install devscripts.)])

	AC_PATH_PROG(LINTIAN,lintian,no)
	AS_IF([test "X$LINTIAN" = Xno],
	      [AC_MSG_WARN(Cannot find lintian.)])

	AC_PATH_PROG(FAKEROOT,fakeroot,no)
	AS_IF([test "X$FAKEROOT" = Xno],
	      [AC_MSG_ERROR(Cannot find fakeroot.)])

	AC_PATH_PROG(DH,dh,no)
	AS_IF([test "X$DH" = Xno],
	      [AC_MSG_ERROR(Cannot find dh. Install debhelper.)])

	AC_PATH_PROG(GPG,gpg,no)
	AS_IF([test "X$GPG" = Xno],
	      [AC_MSG_ERROR(Cannot find gpg. Install gnupg.)])
fi

AC_MSG_CHECKING(if a Windows installer should be built)
AC_ARG_ENABLE([nsis],
	AC_HELP_STRING([--enable-nsis],
                       [build a Nullsoft installer for Windows (no)]),
	[AC_MSG_RESULT($enable_nsis)],
	[AC_MSG_RESULT(no)])
if test "X$enable_nsis" = Xyes ; then
	AC_PATH_PROG(MAKENSIS,makensis,no)
	AS_IF([test "X$MAKENSIS" = Xno],
	      [AC_MSG_ERROR(Cannot find makensis. Install nsis.)])
fi

#
# Misc
#
##############################################################################

REVISION=$((((svn info 2>&- || git svn info 2>&-) || git describe --tags --dirty 2>&- 1>&3) | sed -n -e 's/Revision: //p') 3>&1 | tr -d '\n')
BUILD_DATE_F=$(date -u +%F)
UPSTREAM_EMAIL="parsifal@lix.polytechnique.fr"
UPSTREAM_FULLNAME="Parsifal"
PROJECT_NAME=Slimmer
PROJECT_TARNAME=slimmer
PACKAGE_TAGLINE="the not-so-sound logician"
PROGRAM_ICON=dutch-wick-0.3.ico
FILE_ICON=dutch-wick-0.3-file.ico

AC_CONFIG_FILES([Makefile.include],[chmod a-w Makefile.include])
AC_CONFIG_FILES([_tags],[chmod a-w _tags])
AC_CONFIG_FILES([src/interface/interface/config.ml],[chmod a-w src/interface/interface/config.ml])
AC_CONFIG_FILES([src/META.part],[chmod a-w src/META.part])
AC_CONFIG_FILES([doc/Makefile],[chmod a-w doc/Makefile])
AC_CONFIG_FILES([man/bedwyr.1],[chmod a-w man/bedwyr.1])
AC_CONFIG_FILES([contrib/bedwyr.desktop],[chmod a-w contrib/bedwyr.desktop])
AC_CONFIG_FILES([contrib/bedwyr],[chmod a-w+x contrib/bedwyr])
AC_CONFIG_FILES([opam-files/opam],[])
AC_CONFIG_FILES([opam-files/descr],[])
AC_CONFIG_FILES([debian-files/control],[])
AC_CONFIG_FILES([debian-files/copyright],[chmod a-w debian-files/copyright])
AC_CONFIG_FILES([debian-files/bedwyr.menu],
                [chmod a-w debian-files/bedwyr.menu])
AC_CONFIG_FILES([nsis-files/bedwyr.nsi],[chmod a-w nsis-files/bedwyr.nsi])
AC_CONFIG_FILES([nsis-files/bedwyr.rc],[chmod a-w nsis-files/bedwyr.rc])

OCAML_FILES=$(for i in $($FIND src -type f '!' -path '*.svn*' \
              '!' -name '*~' '!' -name '.*.sw*' '!' -name '*.in') ; do \
              bash -c "grep ' $i ' <<<' $ac_config_files ' -qv" && \
              printf ' \\\n\t'"$i" ; done)
OCAML_IN_FILES=$(for i in $($FIND src -type f '!' -path '*.svn*' \
                 -name '*.in') ; do \
                 printf ' \\\n\t'"$i" ; done)
EXAMPLES_FILES=$($FIND examples -type f '!' -path '*.svn*' \
                 '!' -name '*~' '!' -name '.*.sw*' '!' -name '*.old' \
                 -printf ' \\\n\t%p')

#
# Regular ./configure stuff
#
##############################################################################

AC_SUBST(VERSION_MAJOR)
AC_SUBST(VERSION_MINOR)
AC_SUBST(VERSION_PATCH)
AC_SUBST(VERSION_BUILD)
AC_SUBST(VERSION_DEV)

AC_SUBST(ARCH_SUFFIXES)
AC_SUBST(LIB_SUFFIXES)
AC_SUBST(PLUGIN_SUFFIXES)
AC_SUBST(BIN_SUFFIXES)
AC_SUBST(BEST_SUFFIX)
AC_SUBST(OCAML_VERSION)
AC_SUBST(MINGW32_OCAMLFIND_CONF)

AC_SUBST(FINDLIB_PACKAGE_DIRECTORY)
AC_SUBST(FINDLIB_TAG)
AC_SUBST(OCAMLFIND_XMLM)
AC_SUBST(PLUGINS_CMA)
AC_SUBST(PLUGINS_CMXA)
AC_SUBST(PLUGINS_CMXS)
AC_SUBST(OCAMLFIND_OUNIT)

AC_SUBST(INSTALL)
AC_SUBST(INSTALL_DATA)
AC_SUBST(INSTALL_PROGRAM)

AC_SUBST(BASHCOMP_D)
AC_SUBST(VIMFILES)
AC_SUBST(REVISION)
AC_SUBST(BUILD_DATE_F)
AC_SUBST(UPSTREAM_EMAIL)
AC_SUBST(UPSTREAM_FULLNAME)
AC_SUBST(PROJECT_NAME)
AC_SUBST(PROJECT_TARNAME)
AC_SUBST(PACKAGE_TAGLINE)
AC_SUBST(PROGRAM_ICON)
AC_SUBST(FILE_ICON)

AC_SUBST(ac_config_files)
AC_SUBST(OCAML_FILES)
AC_SUBST(OCAML_IN_FILES)
AC_SUBST(EXAMPLES_FILES)

AC_OUTPUT
