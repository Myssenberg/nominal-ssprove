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

From NominalSSP Require Import Prelude Group Misc.
Import PackageNotation.

#[local] Open Scope package_scope.

From NominalSSP Require Import AE HYBRID KEY NBSES NIKE SAE.

Import AE HYBRID KEY NBSES NIKE_scheme SAE.

Module GH.

Definition I_GH_OUT (E: NBSES_scheme) (N : NIKE_scheme) :=
  [interface
    #val #[ SET ]: (('pk N × 'pk N) × 'fin #|N.(NIKE_scheme.Shared_Key)|) → 'unit  ;
    #val #[ CSET ]: (('pk N × 'pk N) × 'fin #|N.(NIKE_scheme.Shared_Key)|) → 'unit ;
    #val #[ ENC ]: ((('pk N × 'pk N) × 'm E) × 'n E) → 'c E ;
    #val #[ DEC ]: ((('pk N × 'pk N) × 'c E) × 'n E) → 'm E 
].

Definition I_GH_ID_COMP (N : NIKE_scheme) (E : NBSES_scheme) :=
  [interface
    #val #[ SET ]: (('pk N × 'pk N) × 'fin #|N.(NIKE_scheme.Shared_Key)|) → 'unit  ;
    #val #[ CSET ]: (('pk N × 'pk N) × 'fin #|N.(NIKE_scheme.Shared_Key)|) → 'unit
].

#[export] Hint Unfold I_GH_OUT I_GH_ID_COMP I_AE_IN I_AE_OUT I_KEY_OUT I_NIKE_IN I_NIKE_OUT I_SAE_OUT I_HYBRID_IN I_HYBRID_OUT : in_fset_eq.

(*
(* Temporary attempt at composing game *)
Definition GH (E : NBSES_scheme) (N : NIKE_scheme) i (b : 'bool):
  raw_module := ((HYBRID E N i b) ∘ (ID (I_GH_ID_COMP N E) || AE true E N || SAE b E || AE false E N)) ∘ (KEY true N (NIKE_to_SGEN N)).

Lemma GH_valid (E : NBSES_scheme) (N: NIKE_scheme) i (b : 'bool) :
  ValidPackage (GH E N i b).(loc) [interface] (I_GH_OUT E N) (GH E N i b).
Proof.
unfold GH. nssprove_valid. - fset_solve.
*)

End GH.