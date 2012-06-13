AC_INIT([Bedwyr],[1.3-rc2],[https://gforge.inria.fr/tracker/?atid=1543&group_id=367],[bedwyr],[http://slimmer.gforge.inria.fr/bedwyr/])
AC_PREREQ(2.60)
AC_CONFIG_SRCDIR([src/bedwyr.ml])
AC_PROG_INSTALL

REVISION=$((svn info 2>&- || git svn info 2>&-) | grep Revision | sed -e "s/Revision: //" | tr -d '\n')

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
	AC_MSG_ERROR(Cannot find bash.)
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
	AC_MSG_ERROR(Cannot find gzip.)
fi

AC_PATH_PROG(BZIP2,bzip2,no)
if test "$BZIP2" = no ; then
	AC_MSG_ERROR(Cannot find bzip2.)
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

        AC_PATH_PROG(PDFLATEX,pdflatex,no)
        if test "$PDFLATEX" = no ; then
                AC_MSG_ERROR(Cannot find pdflatex.)
        fi

        AC_PATH_PROG(HEVEA,hevea,no)
        if test "$HEVEA" = no ; then
                AC_MSG_ERROR(Cannot find hevea.)
        fi
fi

#
# OCaml stuff (only $OCAMLBUILD is actually used)
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

if test "$enable_nativecode" = "no" ; then
	if test "$enable_bytecode" = "no" ; then
		AC_MSG_ERROR(You must either enable native or bytecode compilation.)
	else
		LIB_SUFFIXES="cma"
		BIN_SUFFIXES="byte"
	fi
	TEST_SUFFIX="byte"
else
	AC_PATH_PROGS(OCAMLOPT,ocamlopt.opt ocamlopt,no)
	if test "$OCAMLOPT" = no ; then
		AC_MSG_ERROR(Cannot find a native code compiler.)
	fi

	if test "$enable_bytecode" = "no" ; then
		LIB_SUFFIXES="a cmxa"
		BIN_SUFFIXES="native"
	else
		LIB_SUFFIXES="cma a cmxa"
		BIN_SUFFIXES="byte native"
	fi
	TEST_SUFFIX="native"
fi

if test "$enable_debug" = "yes" ; then
    OCAMLCFLAGS="-g"
    OCAMLLFLAGS="-g"
else
    OCAMLCFLAGS=""
    OCAMLLFLAGS=""
fi

#
# Regular ./configure stuff
#
##############################################################################

AC_SUBST(LIB_SUFFIXES)
AC_SUBST(BIN_SUFFIXES)
AC_SUBST(TEST_SUFFIX)
AC_SUBST(OCAMLCFLAGS)
AC_SUBST(OCAMLLFLAGS)
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
