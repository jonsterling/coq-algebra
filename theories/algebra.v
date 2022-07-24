From algebra Require Import preamble.
From HB Require Import structures.

HB.mixin Record is_semigroup (S : Type) :=
 { add   : S -> S -> S;
   addrA : associative add }.

HB.structure Definition Semigroup := {S of is_semigroup S}.

HB.mixin Record is_subsemigroup (G : Semigroup.type) (S : G -> Prop) :=
  { has_add : forall u v : G, S u -> S v -> S (add u v) }.

HB.structure Definition Subsemigroup (G : Semigroup.type) := {S of is_subsemigroup G S}.

Section Subsemigroup.
  Context (G : Semigroup.type) (S : Subsemigroup.type G).

  Definition add' : {x : G | S x} -> {x : G | S x} -> {x : G | S x}.
  Proof.
    move=> u v; esplit.
    apply: (has_add _ _ (pi2 u) (pi2 v)).
  Defined.

  Fact addrA' : associative add'.
  Proof.
    move=> u v w.
    apply: sigE=> //=.
    by rewrite addrA.
  Qed.

  HB.instance Definition _ := is_semigroup.Build {x : G | S x} add' addrA'.
End Subsemigroup.


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

HB.mixin Record abgroup_is_ring A of AbGroup A :=
  { one : A;
    mul : A -> A -> A;
    mulrA : associative mul;
    mul1r : left_id one mul;
    mulr1 : right_id one mul;
    mulrDl : left_distributive mul add;
    mulrDr : right_distributive mul add }.

HB.structure Definition Ring := {A of abgroup_is_ring A &}.

HB.mixin Record is_comm_ring A of Ring A :=
  { mulC : commutative (mul : A -> A -> A) }.

HB.structure Definition CRing := {A of is_comm_ring A &}.

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


HB.mixin Record subgroup_is_ideal (A : CRing.type) S of Subgroup A S :=
  { has_mul : forall u v : A, S u -> S v -> S (mul u v) }.

HB.factory Record is_ideal (A : CRing.type) (S : A -> Prop) :=
  { has_zero : S zero;
    has_add : forall u v : A, S u -> S v -> S (add u v);
    has_opp : forall u : A, S u -> S (opp u);
    has_mul : forall u v : A, S u -> S v -> S (mul u v) }.

HB.structure Definition Ideal (A : CRing.type) := {I of subgroup_is_ideal A I &}.

HB.builders Context A S of is_ideal A S.
  HB.instance Definition _ := is_subsemigroup.Build A S has_add.
  HB.instance Definition _ := subsemigroup_is_submonoid.Build A S has_zero.
  HB.instance Definition _ := submonoid_is_subgroup.Build A S has_opp.
  HB.instance Definition _ := subgroup_is_ideal.Build A S has_mul.
HB.end.

HB.mixin Record ideal_is_proper (A : CRing.type) I of Ideal A I :=
  { proper : ~ forall u : A, I u }.

HB.structure Definition ProperIdeal (A : CRing.type) := {I of ideal_is_proper A I &}.

HB.mixin Record proper_ideal_is_prime (A : CRing.type) I of ProperIdeal A I :=
  { choose : forall u v : A, I (mul u v) -> I u \/ I v }.

HB.structure Definition PrimeIdeal (A : CRing.type) := {I of proper_ideal_is_prime A I &}.

HB.factory Record is_prime (A : CRing.type) I of Ideal A I :=
  { proper : ~ forall u : A, I u;
    choose : forall u v : A, I (mul u v) -> I u \/ I v }.

HB.builders Context A I of is_prime A I.
  HB.instance Definition _ := ideal_is_proper.Build A I proper.
  HB.instance Definition _ := proper_ideal_is_prime.Build A I choose.
HB.end.


HB.mixin Record is_domain A of CRing A :=
  { zero_prime : PrimeIdeal.type [the CRing.type of A];
    zero_prime_is_empty : forall x : A, ~ (zero_prime x) }.

HB.structure Definition Domain := {A of is_domain A &}.

HB.mixin Record proper_ideal_is_maximal (A : CRing.type) I of ProperIdeal A I :=
  {maximal : forall J : ProperIdeal.type A, (forall x : A, I x -> J x) -> (forall x : A, J x -> I x)}.

HB.structure Definition MaximalIdeal (A : CRing.type) := {I of proper_ideal_is_maximal A I &}.

Section CRing.
  Context {A : CRing.type}.

  Definition is_inverse_of (u v : A) : Prop :=
    mul u v = one.

  Definition inverse_unique (u v v' : A) :
    is_inverse_of u v
    -> is_inverse_of u v'
    -> v = v'.
  Proof.
    rewrite /is_inverse_of.
    move=> hv hv'.
    rewrite -[v]mulr1 -hv'.
    rewrite -{2}[v']mulr1 -hv.
    rewrite mulC mulrA.
    congr (mul _ v).
    by rewrite mulC.
  Defined.

  Definition is_unit (u : A) :=
    exists v : A, is_inverse_of u v.

  Definition is_zerodivisor (u : A) :=
    exists v : A, ~ (v = zero) /\ mul u v = zero.
End CRing.
