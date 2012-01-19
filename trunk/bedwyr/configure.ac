AC_INIT([Bedwyr],[1.3-beta4],[https://gforge.inria.fr/tracker/?atid=1543&group_id=367],[bedwyr],[http://slimmer.gforge.inria.fr/bedwyr/])
AC_PREREQ(2.57)
AC_CONFIG_SRCDIR([src/main.ml])
AC_PROG_INSTALL

REVISION=$((svn info 2>&- || git svn info 2>&-) | grep Revision | sed -e "s/Revision: //" | tr -d '\n')

#
# OCaml stuff
#
###############################################################################

AC_PATH_PROG(TAR,tar,no)
if test "$TAR" = no ; then
	AC_MSG_ERROR(Cannot find tar.)
fi

AC_PATH_PROG(FIND,find,no)
if test "$FIND" = no ; then
	AC_MSG_ERROR(Cannot find find.)
fi

AC_PATH_PROG(CPIO,cpio,no)
if test "$CPIO" = no ; then
	AC_MSG_ERROR(Cannot find cpio.)
fi

AC_PATH_PROG(CHMOD,chmod,no)
if test "$CHMOD" = no ; then
	AC_MSG_ERROR(Cannot find chmod.)
fi

AC_PATH_PROG(OCAMLDEP,ocamldep,no)
if test "$OCAMLDEP" = no ; then
	AC_MSG_ERROR(Cannot find ocamldep.)
fi

AC_ARG_ENABLE([doc],
   AC_HELP_STRING(
      [--enable-doc],
      [build the html documentation from the sources (disabled by default)]))

if test "$enable_doc" = "yes" ; then
        AC_PATH_PROG(OCAMLDOC,ocamldoc,no)
        if test "$OCAMLDEP" = no ; then
                AC_MSG_ERROR(Cannot find ocamldoc.)
        fi
fi

AC_PATH_PROG(OCAMLLEX,ocamllex,no)
if test "$OCAMLLEX" = no ; then
	AC_MSG_ERROR(Cannot find ocamllex.)
fi

AC_PATH_PROG(OCAMLYACC,ocamlyacc,no)
if test "$OCAMLYACC" = no ; then
	AC_MSG_ERROR(Cannot find ocamlyacc.)
fi

AC_ARG_ENABLE([nativecode],
   AC_HELP_STRING(
      [--enable-nativecode],
      [compile bedwyr in nativecode (default)]))

if test "$enable_nativecode" = "no" ; then
    cma=cma
    cmo=cmo
    OCAMLC="ocamlc"
else
    cma=cmxa
    cmo=cmx
    OCAMLC="ocamlopt"
    OCAMLDEP="$OCAMLDEP -native"
fi

AC_ARG_ENABLE([debug],
   AC_HELP_STRING(
      [--enable-debug],
      [compile bedwyr with debugging information (disabled by default)]))

if test "$enable_debug" = "yes" ; then
    OCAMLCFLAGS="-g"
    OCAMLLFLAGS="-g"
else
    OCAMLCFLAGS=""
    OCAMLLFLAGS=""
fi

AC_SUBST(OCAMLC)
AC_SUBST(OCAMLDEP)
AC_SUBST(OCAMLDOC)
AC_SUBST(OCAMLLEX)
AC_SUBST(OCAMLYACC)
AC_SUBST(OCAMLCFLAGS)
AC_SUBST(OCAMLLFLAGS)
AC_SUBST(cma)
AC_SUBST(cmo)
AC_SUBST(REVISION)
AC_SUBST(INSTALL)
AC_SUBST(INSTALL_DATA)
AC_SUBST(INSTALL_PROGRAM)

AC_CONFIG_FILES([src/config.ml],[chmod a-w src/config.ml])
AC_CONFIG_FILES([src/ndcore/Makefile],[chmod a-w src/ndcore/Makefile])
AC_CONFIG_FILES([src/Makefile],[chmod a-w src/Makefile])
AC_CONFIG_FILES([Makefile],[chmod a-w Makefile])
AC_OUTPUT

echo "All done! You may now run \"make\"."
