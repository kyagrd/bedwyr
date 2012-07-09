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

AC_INIT([Bedwyr],[1.4-dev1],[https://gforge.inria.fr/tracker/?atid=1543&group_id=367],[bedwyr],[http://slimmer.gforge.inria.fr/bedwyr/])
AC_PREREQ(2.60)
AC_CONFIG_SRCDIR([src/bedwyr.ml])
AC_PROG_INSTALL

REVISION=$((((svn info 2>&- || git svn info 2>&-) || git describe --tags --dirty 2>&- 1>&3) | sed -n -e 's/Revision: //p') 3>&1 | tr -d '\n')

#
# Additional options
#
##############################################################################

AC_MSG_CHECKING(if a Debian package should be built)
AC_ARG_WITH([deb],
	([--with-deb],[build deb and debsrc packages]),
	[AC_MSG_RESULT($with_deb)],
	[AC_MSG_RESULT(no)])
if test "$with_deb" = "yes" ; then
	AC_MSG_ERROR(Not available yet.)
fi

#
# Common build stuff
#
##############################################################################

AC_PATH_PROG(BASH,bash,no)
if test "$BASH" = no ; then
	AC_MSG_ERROR(Cannot find bash (needed by the makefiles).)
fi

AC_PATH_PROG(TAR,tar,no)
if test "$TAR" = no ; then
	AC_MSG_ERROR(Cannot find tar.)
fi

AC_PATH_PROG(FIND,find,no)
if test "$FIND" = no ; then
	AC_MSG_ERROR(Cannot find find.)
fi

AC_PATH_PROG(GZIP,gzip,no)
if test "$GZIP" = no ; then
	AC_MSG_WARN(Cannot find gzip.)
else
	ARCH_SUFFIXES="$ARCH_SUFFIXES tgz"
fi

AC_PATH_PROG(BZIP2,bzip2,no)
if test "$BZIP2" = no ; then
	AC_MSG_WARN(Cannot find bzip2.)
else
	ARCH_SUFFIXES="$ARCH_SUFFIXES tbz"
fi

#
# Documentation stuff
#
##############################################################################

AC_MSG_CHECKING(if the documentation should be built)
AC_ARG_ENABLE([doc],
	AC_HELP_STRING([--enable-doc],[build the complete documentation]),
	[AC_MSG_RESULT($enable_doc)],
	[AC_MSG_RESULT(no)])
if test "$enable_doc" = "yes" ; then
	AC_PATH_PROGS(OCAMLDOC,ocamldoc.opt ocamldoc,no)
	if test "$OCAMLDOC" = no ; then
		AC_MSG_ERROR(Cannot find ocamldoc.)
	fi

	AC_PATH_PROG(FIG2DEV,fig2dev,no)
	if test "$FIG2DEV" = no ; then
		AC_MSG_ERROR(Cannot find fig2dev.)
	fi

	AC_PATH_PROG(LATEX,latex,no)
	if test "$LATEX" = no ; then
		AC_MSG_ERROR(Cannot find latex.)
	fi

	AC_PATH_PROG(BIBTEX,bibtex,no)
	if test "$BIBTEX" = no ; then
		AC_MSG_ERROR(Cannot find bibtex.)
	fi

	AC_PATH_PROG(DVIPS,dvips,no)
	if test "$DVIPS" = no ; then
		AC_MSG_ERROR(Cannot find dvips.)
	fi

	AC_PATH_PROG(PS2PDF,ps2pdf,no)
	if test "$PS2PDF" = no ; then
		AC_MSG_ERROR(Cannot find ps2pdf.)
	fi

	AC_PATH_PROG(HEVEA,hevea,no)
	if test "$HEVEA" = no ; then
		AC_MSG_ERROR(Cannot find hevea.)
	fi

	AC_PATH_PROG(BIBHVA,bibhva,no)
	if test "$BIBHVA" = no ; then
		AC_MSG_ERROR(Cannot find bibhva.)
	fi

	AC_PATH_PROG(IMAGEN,imagen,no)
	if test "$IMAGEN" = no ; then
		AC_MSG_ERROR(Cannot find imagen.)
	fi

	AC_PATH_PROG(HACHA,hacha,no)
	if test "$HACHA" = no ; then
		AC_MSG_ERROR(Cannot find hacha.)
	fi
fi

#
# OCaml stuff (only $OCAMLBUILD and $OCAMLDEBUG is actually used)
#
##############################################################################

AC_PATH_PROGS(OCAMLDEP,ocamldep.opt ocamldep,no)
if test "$OCAMLDEP" = no ; then
	AC_MSG_ERROR(Cannot find ocamldep.)
fi

AC_PATH_PROGS(OCAMLLEX,ocamllex.opt ocamllex,no)
if test "$OCAMLLEX" = no ; then
	AC_MSG_ERROR(Cannot find ocamllex.)
fi

AC_PATH_PROGS(OCAMLYACC,ocamlyacc.opt ocamlyacc,no)
if test "$OCAMLYACC" = no ; then
	AC_MSG_ERROR(Cannot find ocamlyacc.)
fi

AC_PATH_PROGS(OCAMLBUILD,ocamlbuild.opt ocamlbuild.native ocamlbuild ocamlbuild.byte,no)
if test "$OCAMLBUILD" = no ; then
	AC_MSG_ERROR(Cannot find ocamlbuild.)
fi

AC_MSG_CHECKING(if debugging information should be added)
AC_ARG_ENABLE([debug],
	AC_HELP_STRING([--enable-debug],[add debugging/profiling information]),
	[AC_MSG_RESULT($enable_debug)],
	[AC_MSG_RESULT(no)])
if test "$enable_debug" = "yes" ; then
	AC_PATH_PROGS(OCAMLDEBUG,ocamldebug.opt ocamldebug,no)
	if test "$OCAMLDEBUG" = no ; then
		AC_MSG_ERROR(Cannot find ocamldebug.)
	fi

	BYTE_SUFFIX="d.byte"
	NATIVE_SUFFIX="p.native"
	BYTE_LIBS="d.cma"
	NATIVE_LIBS="p.a p.cmxa"
else
	BYTE_SUFFIX="byte"
	NATIVE_SUFFIX="native"
	BYTE_LIBS="cma"
	NATIVE_LIBS="a cmxa"
fi

AC_MSG_CHECKING(if native code should be generated)
AC_ARG_ENABLE([nativecode],
	AC_HELP_STRING([--enable-nativecode],[output native code]),
	[AC_MSG_RESULT($enable_nativecode)],
	[AC_MSG_RESULT(no)])
AC_MSG_CHECKING(if bytecode should be generated)
AC_ARG_ENABLE([bytecode],
	AC_HELP_STRING([--enable-bytecode],[output bytecode (default)]),
	[AC_MSG_RESULT($enable_bytecode)],
	[AC_MSG_RESULT(yes)])
if test "$enable_nativecode" = "yes" ; then
	AC_PATH_PROGS(OCAMLOPT,ocamlopt.opt ocamlopt,no)
	if test "$OCAMLOPT" = no ; then
		AC_MSG_ERROR(Cannot find a native code compiler.)
	fi

	if test "$enable_bytecode" = "no" ; then
		LIB_SUFFIXES="$NATIVE_LIBS"
		BIN_SUFFIXES="$NATIVE_SUFFIX"
	else
		AC_PATH_PROGS(OCAMLC,ocamlc.opt ocamlc,no)
		if test "$OCAMLC" = no ; then
			AC_MSG_ERROR(Cannot find a bytecode compiler.)
		fi
		LIB_SUFFIXES="$BYTE_LIBS $NATIVE_LIBS"
		BIN_SUFFIXES="$BYTE_SUFFIX $NATIVE_SUFFIX"
	fi
	BEST_SUFFIX="$NATIVE_SUFFIX"
	OCAML_VERSION=$("$OCAMLOPT" -version)
else
	if test "$enable_bytecode" = "no" ; then
		AC_MSG_ERROR(You must either enable native or bytecode compilation.)
	else
		AC_PATH_PROGS(OCAMLC,ocamlc.opt ocamlc,no)
		if test "$OCAMLC" = no ; then
			AC_MSG_ERROR(Cannot find a bytecode compiler.)
		fi
		LIB_SUFFIXES="$BYTE_LIBS"
		BIN_SUFFIXES="$BYTE_SUFFIX"
	fi
	BEST_SUFFIX="$BYTE_SUFFIX"
	OCAML_VERSION=$("$OCAMLC" -version)
fi

#
# Misc
#
##############################################################################

AC_CONFIG_FILES([Makefile.include],[chmod a-w Makefile.include])
AC_CONFIG_FILES([src/config.ml],[chmod a-w src/config.ml])
AC_CONFIG_FILES([src/ndcore/META],[chmod a-w src/ndcore/META])
AC_CONFIG_FILES([doc/Makefile],[chmod a-w doc/Makefile])
AC_CONFIG_FILES([doc/bedwyr.1],[chmod a-w doc/bedwyr.1])

EXAMPLES_FILES=$($FIND examples -type f '!' -path '*.svn*' \
                 '!' -name '*~' '!' -name '.*.sw*' '!' -name '*.old' \
                 -exec echo -n -e ' \\\n\t'"{}" \;)
BUILD_DATE=$(date -u +%F)
OCAML_FILES=$(for i in $($FIND src -type f '!' -path '*.svn*' \
              '!' -name '*~' '!' -name '.*.sw*') ; do \
              bash -c "grep ' $i ' <<<' $ac_config_files ' -qv" && echo -n -e ' \\\n\t'"$i" ; done)

#
# Regular ./configure stuff
#
##############################################################################

AC_SUBST(ARCH_SUFFIXES)
AC_SUBST(LIB_SUFFIXES)
AC_SUBST(BIN_SUFFIXES)
AC_SUBST(BEST_SUFFIX)
AC_SUBST(REVISION)
AC_SUBST(OCAML_VERSION)
AC_SUBST(BUILD_DATE)
AC_SUBST(INSTALL)
AC_SUBST(INSTALL_DATA)
AC_SUBST(INSTALL_PROGRAM)
AC_SUBST(EXAMPLES_FILES)
AC_SUBST(OCAML_FILES)

AC_OUTPUT
