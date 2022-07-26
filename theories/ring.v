From algebra Require Import preamble semigroup monoid group.
From HB Require Import structures.
From Coq Require Import ZArith.

HB.mixin Record abgroup_is_ring A of AbGroup A :=
  { one : A;
    mul : A -> A -> A;
    mulrA : associative mul;
    mul1r : left_id one mul;
    mulr1 : right_id one mul;
    mulrDl : left_distributive mul add;
    mulrDr : right_distributive mul add }.

HB.structure Definition Ring := {A of abgroup_is_ring A &}.

Definition Z_is_ring : abgroup_is_ring Z.
Proof.
  build.
  - by apply: 1%Z.
  - by apply: Z.mul.
  - by apply: Z.mul_assoc.
  - by apply: Z.mul_1_l.
  - by apply: Z.mul_1_r.
  - by apply: Z.mul_add_distr_r.
  - by apply: Z.mul_add_distr_l.
Defined.

HB.instance Definition _ := Z_is_ring.


HB.mixin Record is_comm_ring A of Ring A :=
  { mulC : commutative (mul : A -> A -> A) }.

HB.structure Definition CRing := {A of is_comm_ring A &}.

HB.instance Definition _ := is_comm_ring.Build Z Z.mul_comm.


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

  Fact mulr0 : forall x : A, mul x zero = zero.
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

  Fact mul0r : forall x : A, mul zero x = zero.
  Proof. by move=> ?; rewrite mulC mulr0. Qed.


  Fact cancel_add : forall a, injective (add a : A -> A).
  Proof.
    move=> a b c h.
    rewrite (_ : b = add (add a b) (opp a)).
    - by rewrite [add a b]addC -addrA subrr addr0.
    - rewrite (_ : c = add (add a c) (opp a)).
      + by rewrite [add a c]addC -addrA subrr addr0.
      + by rewrite h.
  Qed.

  Fact neg_mul_neg_one : forall a : A, mul (opp a) (opp one) = a.
  Proof.
    move=> a.
    apply: (cancel_add (opp a)).
    by rewrite addNr -{1}[opp a]mulr1 -mulrDr subrr mulr0.
  Qed.

  Fact mul_neg_one : forall a : A, mul a (opp one) = (opp a).
  Proof.
    move=> a.
    apply: (cancel_add a).
    by rewrite subrr -{1}[a]mulr1 -mulrDr subrr mulr0.
  Qed.

  Fact mul_neg_neg : forall a b : A, mul (opp a) (opp b) = mul a b.
  Proof.
    move=> a b.
    rewrite (_ : opp b = mul (opp one) b).
    - by rewrite -mul_neg_one mulC.
    - by rewrite mulrA neg_mul_neg_one.
  Qed.

End Facts.

Section Pow.
  Context {A : CRing.type}.

  Fixpoint pow (m : nat) (f : A) : A :=
    match m with
    | 0 => one
    | S n => mul f (pow n f)
    end.

  Fact sum_pow : forall (m n : nat) (f : A), pow (m + n) f = mul (pow m f) (pow n f).
  Proof.
    elim=>//=.
    - by move=> ??; rewrite mul1r.
    - move=> m ih n f.
      by rewrite ih mulrA.
  Qed.

  Fact prod_pow : forall (m n : nat) (f : A), pow (m * n) f = pow m (pow n f).
  Proof.
    elim=> //=.
    move=> m ih n f.
    by rewrite -ih sum_pow.
  Qed.

  Fact pow_mul : forall (m : nat) (f g : A), pow m (mul f g) = mul (pow m f) (pow m g).
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

  Fact pow_one : forall m : nat, pow m (one : A) = one.
  Proof.
    elim=> //=.
    move=> n ih.
    by rewrite ih mul1r.
  Qed.
End Pow.
