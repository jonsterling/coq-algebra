From algebra Require Import preamble semigroup monoid group ring.
From HB Require Import structures.

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


Require Import Lia.
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
