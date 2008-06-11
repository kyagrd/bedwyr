% Words are made of _z_eros and _o_nes,
% represented as z(z(o(z(o(o...))))).

% An automata recognizing infinite
% words on {z,o} that do not eventually
% end with only _o_nes.

#define "coinductive qz {x} :=
  (sigma w\ x = z w, qz w) ;
  (sigma w\ x = o w, qo w)"
        "inductive qo {x} :=
  (sigma w\ x = z w, qz w) ;
  (sigma w\ x = o w, qo w)".

% Specifications of z^omega and o^omega.

#define "coinductive infz x :=
  sigma w\ x = z w, infz w".
#define "coinductive info x :=
  sigma w\ x = o w, info w".

#theorem qz_infz_auto "pi x\ infz x => qz x".
prove.
% Qed.

#theorem qz_inf_steps "pi x\ infz x => qz x".
prove.
% Qed.

#theorem qz_not_info "pi x\ qz x, info x => false".
prove.
% Qed.
