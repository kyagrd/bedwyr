% All number are odd or even

% Summary:
% Mutual Recursion
% Not Equality.

#define "nat x := x=0 ; sigma y\ x = s y, nat y".

#define "evenm x := x=0 ; sigma y\ x=s y, oddm y"
        "oddm  x := sigma y\ x=s y, evenm y".

#theorem sanity_1 "evenm 0".
prove.

#theorem sanity_2 "oddm (s 0)".
prove.

#theorem sanity_3 "evenm (s 0) => false".
prove.

#theorem test "pi x\ nat x => (evenm x; oddm x)".
prove.

% "Functional" version
% For once the functional version is interesting:
% it takes slightly longer to prove,
% and the induction on nat, although not necessary in theory,
% is needed in practice because Tac doesn't support too well
% induction on interleaved fixed points.

#define "evenfm {x} o := (x=0, o=tt); (sigma y\ x = s y, oddfm y o)"
        "oddfm {x} o := (x=0, o=ff); (sigma y\ x = s y, evenfm y o)".

#define "or x y := x=tt; y=tt".

#theorem test_fun "pi x\o\o'\ nat x => evenfm x o => oddfm x o' => or o o'".
prove.

