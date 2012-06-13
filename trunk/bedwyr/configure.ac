AC_INIT([Bedwyr],[1.3-rc2],[https://gforge.inria.fr/tracker/?atid=1543&group_id=367],[bedwyr],[http://slimmer.gforge.inria.fr/bedwyr/])
AC_PREREQ(2.60)
AC_CONFIG_SRCDIR([src/bedwyr.ml])
AC_PROG_INSTALL

REVISION=$((((svn info 2>&- || git svn info 2>&-) || git describe --tags --dirty 2>&- 1>&3) | grep Revision | sed -e "s/Revision: //") 3>&1 | tr -d '\n')

#
# Additional options
#
##############################################################################

AC_ARG_ENABLE([doc],
   AC_HELP_STRING(
      [--enable-doc],
      [build the complete documentation (default)]))

AC_ARG_ENABLE([bytecode],
   AC_HELP_STRING(
      [--enable-bytecode],
      [compile in bytecode (default)]))

AC_ARG_ENABLE([nativecode],
   AC_HELP_STRING(
      [--enable-nativecode],
      [compile in native code (default)]))

AC_ARG_ENABLE([debug],
   AC_HELP_STRING(
      [--enable-debug],
      [compile with debugging information (disabled by default)]))

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
	DIST_SUFFIXES="$DIST_SUFFIXES tar.gz"
fi

AC_PATH_PROG(BZIP2,bzip2,no)
if test "$BZIP2" = no ; then
	AC_MSG_WARN(Cannot find bzip2.)
else
	DIST_SUFFIXES="$DIST_SUFFIXES tar.bz2"
fi

#
# Documentation stuff
#
##############################################################################

if test "$enable_doc" != "no" ; then
	AC_PATH_PROGS(OCAMLDOC,ocamldoc.opt ocamldoc,no)
	if test "$OCAMLDOC" = no ; then
		AC_MSG_ERROR(Cannot find ocamldoc.)
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

if test "$enable_nativecode" = "no" ; then
	if test "$enable_bytecode" = "no" ; then
		AC_MSG_ERROR(You must either enable native or bytecode compilation.)
	else
		LIB_SUFFIXES="$BYTE_LIBS"
		BIN_SUFFIXES="$BYTE_SUFFIX"
	fi
	TEST_SUFFIX="$BYTE_SUFFIX"
else
	AC_PATH_PROGS(OCAMLOPT,ocamlopt.opt ocamlopt,no)
	if test "$OCAMLOPT" = no ; then
		AC_MSG_ERROR(Cannot find a native code compiler.)
	fi

	if test "$enable_bytecode" = "no" ; then
		LIB_SUFFIXES="$NATIVE_LIBS"
		BIN_SUFFIXES="$NATIVE_SUFFIX"
	else
		LIB_SUFFIXES="$BYTE_LIBS $NATIVE_LIBS"
		BIN_SUFFIXES="$BYTE_SUFFIX $NATIVE_SUFFIX"
	fi
	TEST_SUFFIX="$NATIVE_SUFFIX"
fi

#
# Regular ./configure stuff
#
##############################################################################

AC_SUBST(DIST_SUFFIXES)
AC_SUBST(LIB_SUFFIXES)
AC_SUBST(BIN_SUFFIXES)
AC_SUBST(TEST_SUFFIX)
AC_SUBST(REVISION)
AC_SUBST(INSTALL)
AC_SUBST(INSTALL_DATA)
AC_SUBST(INSTALL_PROGRAM)

AC_CONFIG_FILES([Makefile],[chmod a-w Makefile])
AC_CONFIG_FILES([src/Makefile],[chmod a-w src/Makefile])
AC_CONFIG_FILES([src/config.ml],[chmod a-w src/config.ml])
AC_CONFIG_FILES([src/ndcore/Makefile],[chmod a-w src/ndcore/Makefile])
AC_CONFIG_FILES([src/ndcore/META],[chmod a-w src/ndcore/META])
AC_CONFIG_FILES([doc/Makefile],[chmod a-w doc/Makefile])
AC_OUTPUT
