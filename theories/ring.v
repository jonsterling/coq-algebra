From algebra Require Import preamble semigroup monoid group.
From HB Require Import structures.
Require Import Lia.

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

Fact mulr0 {A : CRing.type} : forall x : A, mul x zero = zero.
Proof.
  move=> x.
  suff: add (mul x zero) (mul x zero) = (mul x zero).
  - move=> Q.
    suff: add (mul x zero) (opp (mul x zero)) = add (add (mul x zero) (mul x zero)) (opp (mul x zero)).
    + rewrite -addrA subrr => {2}->.
      by rewrite addC add0r.
    + by rewrite Q.
  - by rewrite -mulC -mulrDl add0r.
Qed.

Fact mul0r {A : CRing.type} : forall x : A, mul zero x = zero.
Proof. by move=> ?; rewrite mulC mulr0. Qed.



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

Section Properties.
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
  Qed.

  Definition is_unit (u : A) :=
    exists v : A, is_inverse_of u v.

  Definition is_zerodivisor (u : A) :=
    exists v : A, ~ (v = zero) /\ mul u v = zero.
End Properties.

Section Facts.
  Context {A : CRing.type}.

  Fixpoint pow (m : nat) (f : A) : A :=
    match m with
    | 0 => one
    | S n => mul f (pow n f)
    end.

  Lemma sum_pow : forall (m n : nat) (f : A), pow (m + n) f = mul (pow m f) (pow n f).
  Proof.
    elim=>//=.
    - by move=> ??; rewrite mul1r.
    - move=> m ih n f.
      by rewrite ih mulrA.
  Qed.

  Lemma prod_pow : forall (m n : nat) (f : A), pow (m * n) f = pow m (pow n f).
  Proof.
    elim=> //=.
    move=> m ih n f.
    by rewrite -ih sum_pow.
  Qed.

  Lemma pow_mul : forall (m : nat) (f g : A), pow m (mul f g) = mul (pow m f) (pow m g).
  Proof.
    elim=> //=.
    - by move=> _ _; rewrite mul1r.
    - move=> m ih f g.
      rewrite ih.
      rewrite -?mulrA.
      congr (mul f).
      rewrite [mul (pow m f) (mul g (pow m g))]mulC.
      rewrite -mulrA.
      congr (mul g).
      by rewrite mulC.
  Qed.

  Lemma pow_one : forall m : nat, pow m (one : A) = one.
  Proof.
    elim=> //=.
    move=> n ih.
    by rewrite ih mul1r.
  Qed.

  Fact cancel_add : forall a, injective (add a : A -> A).
  Proof.
    move=> a b c h.
    rewrite (_ : b = add (add a b) (opp a)).
    - by rewrite [add a b]addC -addrA subrr addr0.
    - rewrite (_ : c = add (add a c) (opp a)).
      + by rewrite [add a c]addC -addrA subrr addr0.
      + by rewrite h.
  Qed.

  Lemma neg_mul_neg_one : forall a : A, mul (opp a) (opp one) = a.
  Proof.
    move=> a.
    apply: (cancel_add (opp a)).
    by rewrite addNr -{1}[opp a]mulr1 -mulrDr subrr mulr0.
  Qed.

  Lemma mul_neg_one : forall a : A, mul a (opp one) = (opp a).
  Proof.
    move=> a.
    apply: (cancel_add a).
    by rewrite subrr -{1}[a]mulr1 -mulrDr subrr mulr0.
  Qed.

  Lemma mul_neg_neg : forall a b : A, mul (opp a) (opp b) = mul a b.
  Proof.
    move=> a b.
    rewrite (_ : opp b = mul (opp one) b).
    - by rewrite -mul_neg_one mulC.
    - by rewrite mulrA neg_mul_neg_one.
  Qed.
End Facts.

Module Rad.
  Section Rad.
    Context {A : CRing.type} (I : Ideal.type A).

    Lemma ideal_has_pow (f : A) (hf : I f) : forall n, I (mul f (pow n f)).
    Proof.
      elim=> //=.
      - by rewrite mulr1.
      - move=> n ih.
        by apply: has_mul.
    Qed.

    Definition prop (f : A) : Prop :=
      exists m : nat, I (pow m f).

    Local Lemma rad_is_ideal : is_ideal A prop.
    Proof.
      build.
      - by exists 1; rewrite //= mul0r; apply: has_zero.
      - move=> f g [m hf] [n hg].
        (* TODO: need to use the binomial theorem. *)
        admit.
      - move=> f [n hf].
        exists (n * 2).
        rewrite prod_pow //= mulr1.
        rewrite mul_neg_neg pow_mul.
        by apply: has_mul.
      - move=> f g [m hf] [n hg].
        exists (m * n).
        rewrite pow_mul.
        apply: has_mul.
        + rewrite (_ : m * n = n * m); first by lia.
          rewrite prod_pow.
          case: n hg=> //=.
          move=> n hg.
          by apply: ideal_has_pow.
        + rewrite prod_pow.
          case: m hf=> //=.
          move=> m hf.
          by apply: ideal_has_pow.
    Abort.
  End Rad.
End Rad.
