(*This is a part of the implementation of the state-separated game-based proof of security for the NaCl crypto_box authenticated encryption scheme.
This file contains the specification for the GAE game and following lemmas*)

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

From NominalSSP Require Import AE KEY NBSES NIKE.
Import AE KEY NBSES NIKE.

Import PackageNotation.

#[local] Open Scope package_scope.

Module GAE.

Definition I_GAE_ID_COMP (N : NIKE_scheme) :=
  [interface
    [ SET ]  : { ('SID N × 'shared_key N) ~> 'unit } ;
    [ CSET ] : { ('SID N × 'shared_key N) ~> 'unit }
].

Definition I_GAE_OUT (E : NBSES_scheme) (N : NIKE_scheme) :=
  (I_GAE_ID_COMP N) :|: (I_AE_OUT E N).


#[export] Hint Unfold I_GAE_OUT I_GAE_ID_COMP I_AE_IN I_AE_OUT I_KEY_OUT I_NIKE_IN I_NIKE_OUT : in_fset_eq.

Definition GAE (E : NBSES_scheme) (N : NIKE_scheme) qset (I : NIKE.inj ('shared_key N) ('k E)) (b : 'bool):
  raw_module := (ID (I_GAE_ID_COMP N) || AE E N I b ) ∘ (KEY N qset true).

Lemma GAE_valid (E : NBSES_scheme) (N: NIKE_scheme) qset (I : NIKE.inj ('shared_key N) ('k E)) (b : 'bool) :
  ValidPackage (GAE E N qset I b).(loc) [interface] (I_GAE_OUT E N) (GAE E N qset I b).
Proof.
unfold GAE. nssprove_valid. Qed.


End GAE.