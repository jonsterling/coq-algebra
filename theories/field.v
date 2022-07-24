From algebra Require Import preamble semigroup monoid group ring.
From HB Require Import structures.

Definition field_property (A : CRing.type) :=
  forall x : A, ~ (x = zero) <-> is_unit x.

Definition residue_field_property (A : CRing.type) :=
  forall x : A, (x = zero) <-> ~ (is_unit x).

Definition geometric_field_property (A : CRing.type) :=
 ~ ((zero : A) = one) /\ forall x : A, x = zero \/ is_unit x.
