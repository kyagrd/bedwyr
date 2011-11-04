" Vim syntax file for Bedwyr
" To have this syntax file used automatically for *.def files, add the
" following line to your ~/.vimrc file:
" au BufRead,BufNewFile *.def set filetype=bedwyr

if version < 600
  syntax clear
elseif exists("b:current_syntax")
  finish
endif

syn case match

syn match       bedwyrParenErr ")"
syn region      bedwyrEncl transparent matchgroup=keyword start="(" matchgroup=keyword end=")" contains=ALLBUT,bedwyrParenErr
hi def link     bedwyrParenErr error

syn match       normal          "\<\(\w\|[-+*/\\^<>=`'~?@#$&!_]\)*\>"
syn match       identifier      "\<\(\u\|_\)\(\w\|[-+*/\\^<>=`'~?@#$&!]\)*\>"

syn region      comment         start="%" end="$"
syn match       preproc         "#[a-z_]*"

syn keyword     boolean         true false
syn keyword     keyword         Kind Type
syn keyword     keyword         Define by
syn keyword     keyword         inductive coinductive
syn keyword     function        forall exists nabla
syn match       special         "\\"

syn match       delimiter       ":"
syn match       delimiter       ":="
syn match       delimiter       ","
syn match       delimiter       ";"
syn match       delimiter       "\."

syn match       constant        "+"
syn match       constant        "-"
syn match       constant        "*"

syn match       operator        "="
syn match       operator        "/\\"
syn match       operator        "\\/"
syn match       operator        "->"

syn match       error           "=>"
syn region      string          start=+"+ skip=+\\\\\|\\"+ end=+"+
