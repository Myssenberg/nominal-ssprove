(*This is a part of the implementation of the state-separated game-based proof of security for the NaCl crypto_box authenticated encryption scheme.
This file contains the specification for the GNIKE and GuNIKE games and following lemmas*)

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

From NominalSSP Require Import Prelude Group Misc.

From NominalSSP Require Import NIKE KEY PKEY.
Import NIKE NIKE_scheme KEY PKEY.

Import PackageNotation.

#[local] Open Scope package_scope.

Module GNIKE.

Definition GEN := 1%N.
Definition HON := 2%N.
Definition CSETPK := 3%N.
Definition GET := 4%N. (*tal skal være forskellige across filer*)


Definition I_GNIKE_OUT (N: NIKE_scheme) :=
  [interface
    #val #[ SHAREDKEY ]: ('pk N × 'pk N) → 'unit ;
    #val #[ GEN ]: 'unit → 'pk N ;
    #val #[ CSETPK ]: 'pk N → 'unit ;
    #val #[ GET ]:  ('SID N) → 'shared_key N ;
    #val #[ HON ]:  ('SID N) → 'bool
].

Definition I_GNIKE_ID_COMP (N: NIKE_scheme) :=
  [interface
    #val #[ GEN ]: 'unit → 'pk N ;
    #val #[ CSETPK ]: 'pk N → 'unit ;
    #val #[ GET ]:  ('SID N) → 'shared_key N ;
    #val #[ HON ]:  ('SID N) → 'bool
].

#[export] Hint Unfold I_GNIKE_OUT I_GNIKE_ID_COMP I_NIKE_OUT I_NIKE_IN I_PKEY_OUT I_KEY_OUT : in_fset_eq.

Definition GNIKE (N: NIKE_scheme) (b : 'bool) :
  raw_module := (NIKE N || ID (I_GNIKE_ID_COMP N)) ∘ (KEY b || PKEY b N.PK N.SK N.keygen).

Lemma GNIKE_valid (N: NIKE_scheme) (b : 'bool) : ValidPackage (GNIKE N b).(loc) [interface] (I_GNIKE_OUT N) (GNIKE N b).
Proof.
unfold GNIKE. nssprove_valid. 2:{


End GNIKE.