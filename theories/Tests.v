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

From NominalSSP Require Import Prelude.
Import PackageNotation.
#[local] Open Scope package_scope.

Module Tests.


Definition I1 :=
  [interface #val #[ 1 ] : 'unit → 'unit ].

Definition I2 :=
  [interface #val #[ 2 ] : 'unit → 'unit ].

Definition I3 :=
  [interface #val #[ 3 ] : 'unit → 'unit ].

Definition I12 := [interface
  #val #[ 1 ] : 'unit → 'unit ;
  #val #[ 2 ] : 'unit → 'unit ].

Definition I123 := I3 :|: I12.

Hint Unfold I1 I2 I3 I12 I123 : in_fset_eq.

Goal (flat (I1 :|: I2)).
Proof. nssprove_valid. Qed.

Local Obligation Tactic := nssprove_valid.

Program Definition M12 : module _ _ :=
    {module I1 :|: I2 ; I1 :|: I2 ; ID I1 || ID I2 }.

Program Definition M123 : module _ _ :=
    {module I1 :|: I2 :|: I3 ; I1 :|: I2 :|: I3 ; ID I1 || ID I2 || ID I3 }.

Goal ((ID I1 || ID I2 || ID I3) ≡ (ID I3 || ID I12)).
Proof.
  rewrite -> id_sep_par by nssprove_valid.
  rewrite -> sep_par_commut by nssprove_valid.
  rewrite -> id_sep_par by nssprove_valid.
  rewrite -> id_sep_par by nssprove_valid.
  apply alpha_eq.
  f_equal.
  fset_solve.
Qed.

End Tests.
