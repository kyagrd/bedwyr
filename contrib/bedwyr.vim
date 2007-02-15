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

syn match   bedwyrParenErr ")"
syn region  bedwyrEncl transparent matchgroup=keyword start="(" matchgroup=keyword end=")" contains=ALLBUT,bedwyrParenErr
hi def link bedwyrParenErr error

syn match   normal   "\<\(\w\|[-+*/\\^<>=`'~?@#$&!_]\)*\>"
syn match   keyword  "\<\(\u\|_\)\(\w\|[-+*/\\^<>=`'~?@#$&!]\)*\>"

syn region  comment  start="%" end="$"
syn match   statement "#[a-z_]*"

syn keyword boolean  true false
syn keyword keyword  inductive coinductive
syn keyword special  pi sigma nabla
syn match   special  "\\"
syn match   special  ":="
syn match   special  "\."
syn match   special  "&"
syn match   special  ","
syn match   special  ";"
syn match   special  "+"
syn match   special  "-" 
syn match   special  "*"
syn match   special  "/"
syn match   special  "->"
syn match   special  "=>"
syn region  string   start=+"+ skip=+\\\\\|\\"+ end=+"+
