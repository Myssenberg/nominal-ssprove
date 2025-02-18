Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_ssreflect all_algebra reals distr realsum
  fingroup.fingroup solvable.cyclic prime ssrnat ssreflect ssrfun ssrbool ssrnum
  eqtype choice seq.
Set Warnings "notation-overridden,ambiguous-paths".

From Coq Require Import Utf8.
From extructures Require Import ord fset fmap.

From Equations Require Import Equations.
Require Equations.Prop.DepElim.

Set Equations With UIP.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".
Set Primitive Projections.

From NominalSSP Require Import Prelude Group.
Import Num.Def Num.Theory Order.POrderTheory.
Import PackageNotation.
#[local] Open Scope ring_scope.
#[local] Open Scope package_scope.
Import GroupScope GRing.Theory.


Notation "'getNone' n ;; c" :=
  ( v ← get n ;;
    #assert (v == None) ;;
    c
  )
  (at level 100, n at next level, right associativity,
  format "getNone  n  ;;  '//' c")
  : package_scope.

Notation "x ← 'getSome' n ;; c" :=
  ( v ← get n ;;
    #assert (isSome v) as vSome ;;
    let x := getSome v vSome in
    c
  )
  (at level 100, n at next level, right associativity,
  format "x  ←  getSome  n  ;;  '//' c")
  : package_scope.


Definition quad (l₀ l₁ l₂ l₃ : Location) (R : l₀ → l₁ → l₂ → l₃ → Prop)
  : precond := λ '(h₀, h₁),
    R (get_heap h₀ l₀) (get_heap h₀ l₁) (get_heap h₁ l₂) (get_heap h₁ l₃).

Arguments quad : simpl never.

Lemma quad_SemiInvariant {l₀ l₁ l₂ l₃ : Location} {L₀ L₁ : {fset Location}} {R} :
  l₀ \in L₀ → l₁ \in L₀ → l₂ \in L₁ → l₃ \in L₁ → 
  quad l₀ l₁ l₂ l₃ R (empty_heap, empty_heap) →
  SemiInvariant L₀ L₁ (quad l₀ l₁ l₂ l₃ R).
Proof.
  intros H0 H1 H2 H3 H4.
  eapply Build_SemiInvariant; [| done ].
  intros s0 s1 l v.
  move=> /negP H5 /negP H6.
  intros Q.
  unfold quad.
  do 4 try rewrite get_set_heap_neq //.
  1-4: apply /eqP; move=> ?; by subst.
Qed.

#[export] Hint Extern 10 (is_true (_ \in _)) =>
  fset_solve : ssprove_invariant.

#[export] Hint Resolve quad_SemiInvariant : ssprove_invariant.
