
Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_ssreflect all_algebra reals distr realsum
  fingroup.fingroup solvable.cyclic prime ssrnat ssreflect ssrfun ssrbool ssrnum
  eqtype choice seq.
Set Warnings "notation-overridden,ambiguous-paths".

From Coq Require Import Utf8.
From extructures Require Import ord fset fmap.


Module FsetSolve.

  Local Open Scope fset_scope.

  Create HintDb in_fset_eq.

  Definition fsetUP' T x y z := boolp.reflect_eq (@fsetUP T x y z).
  #[export] Hint Rewrite <- fsetUP' : in_fset_eq.

  Lemma in_consP {T : ordType} (x y : T) (ys : seq T) : reflect (x = y \/ x \in ys) (x \in cons y ys).
  Proof.
    rewrite in_cons.
    apply orPP.
    + rewrite -in_fset1.
      apply fset1P.
    + apply idP.
  Qed.

  #[export] Hint Rewrite in_fset : in_fset_eq.
  Definition in_consP' T x y z := boolp.reflect_eq (@in_consP T x y z).
  #[export] Hint Rewrite <- in_consP' : in_fset_eq.

  Definition fsetDP' T x y z := boolp.reflect_eq (@fsetDP T x y z).
  #[export] Hint Rewrite <- fsetDP' : in_fset_eq.

  Lemma falseP : reflect False false.
  Proof.
    by apply Bool.ReflectF.
  Qed.
  Definition falseP' := boolp.reflect_eq falseP.
  #[export] Hint Rewrite <- falseP' : in_fset_eq.

  Definition negP' b := boolp.reflect_eq (@negP b).
  #[export] Hint Rewrite <- negP' : in_fset_eq.

  #[export] Hint Rewrite -> in_nil : in_fset_eq.
  #[export] Hint Rewrite -> fset1E : in_fset_eq.

  Ltac fset_into_prop x :=
    lazymatch goal with
      | |- is_true (fsubset _ _) =>
          let P := fresh "P" in
          apply /fsubsetP => x P
      | |- is_true (fdisjoint _ _) =>
          let P := fresh "P" in
          apply /fdisjointP => x P
      | |- is_true (fdisjoint _ _) -> _ =>
          let Disj := fresh "Disj" in
          move=> /fdisjointP Disj ;
          fset_into_prop x ;
          specialize Disj with x
      | |- is_true (_ \in _) =>
          idtac
      | |- is_true (_ \notin _) =>
          let P := fresh "P" in
          apply /negP => P
      | |- is_true (_ != _) =>
          let P := fresh "P" in
          apply /negP => P ;
          rewrite -in_fset1 in P
      | |- (_ = _) =>
          apply /eqP ;
          rewrite eqEfsubset ;
          apply /andP ; split ;
          fset_into_prop x
      | |- False =>
          idtac
      | |- _ =>
          fail "unknown goal type in fset_into_prop"
    end.

  Ltac fset_solve :=
    let x := fresh "x" in
    fset_into_prop x ;
    autounfold with in_fset_eq in * ;
    autorewrite with in_fset_eq in * ;
    intuition (subst; try discriminate).

End FsetSolve.


Module FsetSolveTest.

  Local Open Scope fset_scope.
  Import FsetSolve.

  Context {T : ordType}.

  Lemma test_disjoint (A : {fset T}) : fdisjoint fset0 A.
  Proof. fset_solve. Qed.

  Lemma test_union (A B C : {fset T}) :
    fdisjoint A B → fdisjoint B C → fdisjoint (A :|: C) B.
  Proof. fset_solve. Qed.

  Lemma test_disj : fdisjoint (fset [:: 1; 3]) (fset [:: 2; 4; 6]).
  Proof. fset_solve. Qed.

  Lemma test_disj2 A B :
    fdisjoint A B → fdisjoint (fset [:: 1; 2; 3; 4; 6]) (A :|: B) → 
    fdisjoint (A :|: fset [:: 1; 3]) (B :|: fset [:: 2; 4; 6]).
  Proof. fset_solve. Qed.
End FsetSolveTest.
