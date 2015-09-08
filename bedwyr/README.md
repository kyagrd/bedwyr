Bedwyr, the not-so-sound logician
=================================
v1.4 -- Bedwyr-with-round-tables
--------------------------------

1. what
2. license
3. getting
4. building
5. documentation
6. installing
7. distribution


### 1. What is Bedwyr? ###

Bedwyr is a theorem prover for the Level-0/1 fragment of the Linc logic.

It is based on Alwen Tiu's **Level-0/1**, and Nadathur & Linell's
**LLambda** library, both written in SML. The OCaml translation has been
done by Baelde & Ziegler and further development by Baelde & Gacek.
It is currently under work by Heath.  The system also benefited from the
wisdom of Miller, Nadathur and Pientka.

For background on the system, see
*Mixing Finite Success and Finite Failure in an Automated Prover*
(Alwen Tiu and Gopalan Nadathur and Dale Miller):
[http://www.lix.polytechnique.fr/Labo/Dale.Miller/papers/eshol05.pdf](http://www.lix.polytechnique.fr/Labo/Dale.Miller/papers/eshol05.pdf)

Webpage:
[http://slimmer.gforge.inria.fr/bedwyr/](http://slimmer.gforge.inria.fr/bedwyr/)


### 2. License ###

This is free software, licensed under GPL version 2.  A copy of this
license can be found in COPYING or, depending on your distribution,
`/usr/share/common-licenses/GPL-2` or `/usr/portage/licenses/GPL-2`.


### 3. Obtaining Bedwyr ###

Released sources, binaries and packages may be obtained from:
  [https://gforge.inria.fr/frs/?group_id=367](https://gforge.inria.fr/frs/?group_id=367)

Development sources may be obtained via the commands
  `svn checkout svn://scm.gforge.inria.fr/svn/slimmer`
or
  `svn checkout --username anonsvn https://scm.gforge.inria.fr/svn/slimmer`
(the password is the username).

The project is also available as an opam package, and for Debian
(`http://slimmer.gforge.inria.fr/releases/debian/ squeeze main`), Gentoo
(public user overlay `dawan`) and Windows.  The Linux packages contains
the core libraries as well as the complete program.


### 4. Building Bedwyr ###

For proper compilation and installation, a Linux environment and the
following packages are required:

- OCaml (4.01.0 or later) and findlib (often packaged as ocaml-findlib)
- autotools (at least autoconf-2.60) and GNU make
- bash, tar, gzip, bzip2 and some other standard tools

With the vanilla archive, the single command

    $ make

will build bedwyr with default options (no documentation, byte code
only).  You can customize the process with configure options:

    $ autoconf
    $ ./configure --no-create [--enable-doc] [--enable-nativecode] [...]
    $ make

Use the `./configure --help` and `make help` commands for more details.

Then pick an example in examples/ and run

    $ ./bedwyr examples/<file>.def

or just run

    $ ./bedwyr

and type "#help." for a little help.


### 5. Documentation ###

- `doc/quickstart.(pdf|html)`: more information on how to use bedwyr
- `doc/refman/index.html`: complete system description
- `_build/src_docdir/index.html`: source code documentation

Building these files requires the "--enable-doc" configure option (which
adds some dependencies on LaTeX, HeVeA, etc), and is done by the

    $ make doc

command.


### 6. Installation ###

If for some reason you don't want to use bedwyr fresh out of the
tarball, and you won't or can't use one of the provided packages, you
can use the `make install` facility.  It makes good use of the standard
$DESTDIR variable, which is an absolute prefix added to all installation
paths.  You can install all the files in a temporary copy of the file
hierarchy by typing

    $ make DESTDIR=~/tmpdir install

or in a alternative standard place with

    $ ./configure --prefix=/usr
    $ make
    $ make install


### 7. Distribution ###

- /contrib
  > Vim and Emacs files.

- /doc
  > LaTeX documentation.

- /examples
  > A few simple examples.

- /src
  - /ndcore
    > Code for the unification and non-destructive normalization of LLambda.
    > Also contains a term indexing module, currently only used for tabling.

  - /iO
    > Generic low-level input/output functions.

  - /parsetree
    > Construction of a typed parse tree (lexer and parser), transformation
    > to an untyped but type-checked abstract syntax tree.

  - /prover
    > Tabling, environments and proof-search procedure.

  - /interface
    > High-level interface.

  - /plugins
    > Optional functionallies (XML proof export).
