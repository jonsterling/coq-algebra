From algebra Require Import preamble semigroup.
From HB Require Import structures.
From Coq Require Import ZArith.

HB.mixin Record semigroup_is_monoid M of is_semigroup M :=
  { zero  : M;
    add0r : left_id zero add;
    addr0 : right_id zero add }.

HB.factory Record is_monoid M :=
  { zero  : M;
    add   : M -> M -> M;
    addrA : associative add;
    add0r : left_id zero add;
    addr0 : right_id zero add }.

HB.builders Context (M : Type) of is_monoid M.
  HB.instance Definition _ := is_semigroup.Build M add addrA.
  HB.instance Definition _ := semigroup_is_monoid.Build M zero add0r addr0.
HB.end.

HB.structure Definition Monoid := { M of is_monoid M }.

HB.mixin Record subsemigroup_is_submonoid (M : Monoid.type) S of Subsemigroup M S :=
  { has_zero : S zero }.

HB.structure Definition Submonoid (M : Monoid.type) := {S of subsemigroup_is_submonoid M S &}.

Section Submonoid.
  Context (M : Monoid.type) (S : Submonoid.type M).

  Definition zero' : {x : M | S x}.
  Proof. by esplit; apply: has_zero. Defined.

  Fact add0r' : left_id zero' add.
  Proof.
    move=> u; apply: sigE=> //=.
    by rewrite add0r.
  Qed.

  Fact addr0' : right_id zero' add.
  Proof.
    move=> u; apply: sigE=> //=.
    by rewrite addr0.
  Qed.

  HB.instance Definition _ := semigroup_is_monoid.Build {x : M | S x} zero' add0r' addr0'.
End Submonoid.

HB.instance Definition _ := semigroup_is_monoid.Build Z 0%Z  Z.add_0_l Z.add_0_r.
