% Two Definitions of Even are Equivalent

% Summary:
% Mutual Recursion.

#define "evenm x := x=0 ; sigma y\ x=s y, oddm y"
        "oddm  x := sigma y\ x=s y, evenm y".

#define "evenr x := x=0 ; sigma y\ x = s (s y), evenr y".

#theorem test "pi x\ (evenm x => evenr x), (evenr x => evenm x)".
prove.

% "Functional" version.

#define "evenfm x o := (x=0, o=tt); (sigma y\ x = s y, oddfm y o)"
        "oddfm x o := (x=0, o=ff); (sigma y\ x = s y, evenfm y o)".

#define "evenfr x o := (x=0, o=tt); (x=s 0, o=ff);
                       (sigma y\ x=s (s y), evenfr x o)".

#theorem test_fun "pi x\o\o'\ evenfm x o => evenfr x o' => o=o'".
prove.

