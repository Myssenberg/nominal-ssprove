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
    #val #[ SET ]: (('pk N × 'pk N) × 'fin #|E.(NBSES.Shared_Key)|) → 'unit  ;
    #val #[ CSET ]: (('pk N × 'pk N) × 'fin #|E.(NBSES.Shared_Key)|) → 'unit ;
    #val #[ ENC ]: ((('pk N × 'pk N) × 'm E) × 'n E) → 'c E ;
    #val #[ DEC ]: ((('pk N × 'pk N) × 'c E) × 'n E) → 'm E 
].

Definition I_GH_ID_COMP (E: NBSES_scheme) (N : NIKE_scheme) :=
  [interface
    #val #[ SET ]: (('pk N × 'pk N) × 'fin #|E.(NBSES.Shared_Key)|) → 'unit  ;
    #val #[ CSET ]: (('pk N × 'pk N) × 'fin #|E.(NBSES.Shared_Key)|) → 'unit ;
    #val #[ GET ]: ('pk N × 'pk N) → 'k E
].

Definition I_GH_FST (E: NBSES_scheme) (N : NIKE_scheme) :=
  [interface
    #val #[ GEN ]: 'unit → 'unit ; 
    #val #[ SENC ]: ('m E × 'n E) → 'c E  ;
    #val #[ SDEC ]: ('c E × 'n E) → 'm E ;
    #val #[ ENC ]: ((('pk N × 'pk N) × 'm E) × 'n E) → 'c E ;
    #val #[ DEC ]: ((('pk N × 'pk N) × 'c E) × 'n E) → 'm E 
].

Definition I_GH_SND (E: NBSES_scheme) (N : NIKE_scheme) :=
  [interface
    #val #[ SET ]: (('pk N × 'pk N) × 'fin #|E.(NBSES.Shared_Key)|) → 'unit  ;
    #val #[ CSET ]: (('pk N × 'pk N) × 'fin #|E.(NBSES.Shared_Key)|) → 'unit ;
    #val #[ GET ]: ('pk N × 'pk N) → 'k E ;
    #val #[ GEN ]: 'unit → 'unit ; 
    #val #[ SENC ]: ('m E × 'n E) → 'c E  ;
    #val #[ SDEC ]: ('c E × 'n E) → 'm E 
].

Definition I_GH_TRD (E: NBSES_scheme) (N : NIKE_scheme) :=
  [interface
    #val #[ SET ]: (('pk N × 'pk N) × 'fin #|E.(NBSES.Shared_Key)|) → 'unit  ;
    #val #[ CSET ]: (('pk N × 'pk N) × 'fin #|E.(NBSES.Shared_Key)|) → 'unit ;
    #val #[ GET ]: ('pk N × 'pk N) → 'k E ;
    #val #[ GET ]: ('pk N × 'pk N) → 'k E ;
    #val #[ HON ]: ('pk N × 'pk N)  → 'option 'bool
].

#[export] Hint Unfold I_GH_OUT I_GH_ID_COMP I_HYBRID_IN I_HYBRID_OUT I_GH_FST I_GH_SND I_GH_TRD I_AE_IN I_AE_OUT I_KEY_OUT I_SAE_OUT : in_fset_eq.

Definition GH (E : NBSES_scheme) (N : NIKE_scheme) i (b : 'bool):
  raw_module := (HYBRID E N i) ∘ (((ID (I_GH_ID_COMP E N) || ID (I_GH_FST E N)) ∘ (AE b E N || ID (I_GH_SND E N)) ∘ (SAE b E || ID (I_GH_TRD E N))) ∘ (KEY true N (NBSES_to_SGEN E))).

Lemma GAE_valid (E : NBSES_scheme) (N: NIKE_scheme) i (b : 'bool) :
  ValidPackage (GH E N i b).(loc) [interface] (I_GH_OUT E N) (GH E N i b).
Proof.
unfold GH. nssprove_valid. Qed.

End GH.