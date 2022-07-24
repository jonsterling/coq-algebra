From algebra Require Import preamble semigroup monoid.
From HB Require Import structures.

HB.mixin Record monoid_is_group G of Monoid G :=
 { opp : G -> G;
   subrr : forall x, add x (opp x) = zero;
   addNr : forall x, add (opp x) x = zero }.

HB.factory Record is_group G :=
 { zero : G;
   add : G -> G -> G;
   opp : G -> G;
   addrA : associative add;
   add0r : left_id zero add;
   subrr : forall x, add x (opp x) = zero;
   addNr : forall x, add (opp x) x = zero }.

HB.builders Context G of is_group G.
  Let addr0 : forall x, add x zero = x.
  Proof. by move=> x; rewrite -(addNr x) addrA subrr add0r. Qed.
  HB.instance Definition _ := is_monoid.Build G zero add addrA add0r addr0.
  HB.instance Definition _ := monoid_is_group.Build G opp subrr addNr.
HB.end.

HB.structure Definition Group := {G of is_group G}.

HB.mixin Record is_abgroup G of Group G :=
  { addC : commutative (add : G -> G -> G) }.


HB.structure Definition AbGroup := {G of is_abgroup G &}.



HB.mixin Record submonoid_is_subgroup (G : Group.type) S of Submonoid G S :=
  { has_opp : forall u : G, S u -> S (opp u) }.

HB.factory Record is_subgroup (G : Group.type) (S : G -> Prop) :=
  { has_zero : S zero;
    has_add : forall u v : G, S u -> S v -> S (add u v);
    has_opp : forall u : G, S u -> S (opp u) }.

HB.structure Definition Subgroup (G : Group.type) := {S of submonoid_is_subgroup G S &}.

HB.builders Context G S of is_subgroup G S.
  HB.instance Definition _ := is_subsemigroup.Build G S has_add.
  HB.instance Definition _ := subsemigroup_is_submonoid.Build G S has_zero.
HB.end.


Section Subgroup.
  Context (G : Group.type) (S : Subgroup.type G).

  Definition opp' : {x : G | S x} -> {x : G | S x}.
  Proof. by move=> u; esplit; apply: has_opp; apply: pi2 u. Defined.

  Fact subrr' : forall x, add x (opp' x) = zero.
  Proof.
    move=> u.
    apply: sigE=> //=.
    by rewrite subrr.
  Qed.

  Fact addNr' : forall x, add (opp' x) x = zero.
  Proof.
    move=> u.
    apply: sigE=> //=.
    by rewrite addNr.
  Qed.

  HB.instance Definition _ := monoid_is_group.Build {x : G | S x} opp' subrr' addNr'.
End Subgroup.
