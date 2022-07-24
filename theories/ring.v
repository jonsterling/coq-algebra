From algebra Require Import preamble semigroup monoid group.
From HB Require Import structures.

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
