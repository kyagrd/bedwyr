##############################################################################
#  Bedwyr prover -- bash autocompletion                                      #
#  Copyright (C) 2015 Quentin Heath                                          #
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

# to use, pick the first available method:
# - place in /etc/bash_completion.d
# - source from $HOME/.bash_completion
# - source from $HOME/.bashrc

_bedwyr_long_options () {
  local IFS=$'\n'
  COMPREPLY=($(bedwyr --help | sed -n -e 's/^\s\+\('"$cur"'[a-zA-Z-]*\).*$/\1/p'))
}

_bedwyr_all_options () {
  local IFS=$'\n'
  COMPREPLY=($(bedwyr --help | sed -n -e 's/^\s\+\('"$cur"'[a-zA-Z-]*\).*$/\1/p'))
}

_bedwyr_string_argument () {
  COMPREPLY=(\')
}

_bedwyr_int_argument () {
  COMPREPLY=()
}

_bedwyr_colours_argument () {
  local IFS=$'\n'
  COMPREPLY=($(IFS=' '; compgen -W "0 8 256" -- "$cur"))
}

_bedwyr_files () {
  _filedir '@(thm|def)'
}

_bedwyr ()
{
  local c=1 word prev

  # get last option
  while [ $c -lt $COMP_CWORD ] ; do
    word="${COMP_WORDS[c]}"
    case "$word" in
    *)
      prev="$word"
      ;;
    esac
    c=$((c+1))
  done

  cur="${COMP_WORDS[COMP_CWORD]}"

  # complete new option
  case "$cur" in
  --*) _bedwyr_long_options ;;
  -*)  _bedwyr_all_options ;;
  *)
    # complete last option argument
    case "$prev" in
    '-d')           _bedwyr_string_argument ;;
    '-e')           _bedwyr_string_argument ;;
    '--freezing')   _bedwyr_int_argument ;;
    '--saturation') _bedwyr_int_argument ;;
    '--colours')    _bedwyr_colours_argument ;;
    *)              _bedwyr_files ;;
    esac
    ;;
  esac

}
complete -F _bedwyr bedwyr
