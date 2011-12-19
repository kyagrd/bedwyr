
AC_INIT([bedwyr],[1.3-alpha1],[https://gforge.inria.fr/tracker/?atid=1543&group_id=367])
AC_PREREQ(2.57)
AC_CONFIG_SRCDIR([src/main.ml])
AC_PROG_INSTALL

# This is ugly, I'd like to find a better solution.
if test "x$prefix" = "xNONE" ; then
  prefix=/usr/local
fi

#
# OCaml stuff
#
###############################################################################

AC_PATH_PROG(OCAMLDEP,ocamldep,no)
if test "$OCAMLDEP" = no ; then
	AC_MSG_ERROR(Cannot find ocamldep.)
fi

AC_ARG_ENABLE([doc],
   AC_HELP_STRING(
      [--enable-doc],
      [build html documentation from the sources (disabled by default)]))

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
    OCAMLCFLAGS="-g "
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

AC_CONFIG_FILES([src/Makefile],[chmod a-w src/Makefile])
AC_CONFIG_FILES([Makefile],[chmod a-w Makefile])
AC_OUTPUT

echo "All done! You may now run \"make\"."
