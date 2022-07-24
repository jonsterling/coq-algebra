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
