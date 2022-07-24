From algebra Require Import preamble semigroup monoid group ring.
From HB Require Import structures.

HB.mixin Record nontrivial_cring_is_field A of NontrivialCRing A :=
  { nonzero_is_unit : forall x : A, ~ (x = zero) -> is_unit x }.

HB.mixin Record nontrivial_cring_is_geometric_field A of NontrivialCRing A :=
  { zero_or_unit : forall x : A, x = zero \/ is_unit x }.

HB.mixin Record nontrivial_cring_is_residue_field A of NontrivialCRing A :=
  { non_unit_is_zero : forall x : A, ~ (is_unit x) -> x = zero }.


HB.structure Definition Field := {A of nontrivial_cring_is_field A &}.
(** For instance, the generic local ring is a field in this sense. *)

HB.structure Definition GeometricField := {A of nontrivial_cring_is_geometric_field A &}.
(** I don't know if the generic local ring is a "geometric field". *)


HB.structure Definition ResidueField := {A of nontrivial_cring_is_residue_field A &}.
(** As an example, real numbers object in Sh(X) for a topological space X is a residue field. *)

HB.builders Context A of nontrivial_cring_is_geometric_field A.
  Fact non_unit_is_zero : forall x : A, ~ (is_unit x) -> x = zero.
  Proof. by move=> x hx; case: (zero_or_unit x). Qed.

  Fact nonzero_is_unit : forall x : A, ~ (x = zero) -> is_unit x.
  Proof. by move=> x hx; by case: (zero_or_unit x). Qed.

  HB.instance Definition _ := nontrivial_cring_is_residue_field.Build A non_unit_is_zero.
  HB.instance Definition _ := nontrivial_cring_is_field.Build A nonzero_is_unit.
HB.end.
