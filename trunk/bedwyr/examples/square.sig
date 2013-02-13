sig square.

type select          A -> list A -> list A -> o.

kind nat      type.
type z        nat.
type s        nat -> nat.

type plus     nat -> nat -> nat -> o.
type leq, lt         nat -> nat -> o.

type fiveNten           nat -> o.
type one2nine           list nat -> o.
type nat_int            nat -> int -> o.
type nat_list_int_list  list nat -> list int -> o.

kind option   type -> type.
type none     option A.
type some     A -> option A.

type fifteen         nat -> nat -> option nat -> o.
type square          list nat -> o.
type list_all        o.
type square'         list nat -> o.
type list_all'       o.
type print_list      list int -> o.
