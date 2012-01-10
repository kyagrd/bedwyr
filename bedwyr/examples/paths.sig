% This Teyjus signature file provides the signature to describe
% untyped lambda terms, marked beta-reduction, and paths through
% these.  Three predicates are also declared.

sig paths.

kind  tm           type.
type  app          tm -> (tm -> tm).
type  abs          (tm -> tm) -> tm.
type  beta         (tm -> tm) -> tm -> tm.

kind p             type.
type bnd           (p -> p) -> p.
type left, right    p -> p.

type path   tm -> p  -> o.
type bpath  tm -> p  -> o.
type jump   tm -> tm -> o.
