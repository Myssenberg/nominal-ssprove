(*This is a part of the implementation of the state-separated game-based proof of security for the NaCl crypto_box authenticated encryption scheme.
This file contains the specification for a GMODPKAE game*)

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

From NominalSSP Require Import AE KEY MODPKAE NBSES NIKE PKEY.
Import AE KEY MODPKAE NBSES NIKE_scheme PKEY.

Import PackageNotation.

#[local] Open Scope package_scope.

Module GMODPKAE.

Definition I_GMODPKAE_OUT (N: NIKE_scheme) (E : NBSES_scheme) :=
  [interface
    #val #[ GEN ]: 'unit → 'T 'fin #|N.(NIKE_scheme.PK)| ;
    #val #[ CSETPK ]: 'T 'fin #|N.(NIKE_scheme.PK)| → 'unit ;
    #val #[ PKENC_MOD ]: ((('T 'fin #|N.(NIKE_scheme.PK)| × 'T 'fin #|N.(NIKE_scheme.PK)|) × 'T E.(M)) × 'T 'fin #|E.(Nonce)|) → 'T E.(C) ; 
    #val #[ PKDEC_MOD ]: ((('T 'fin #|N.(NIKE_scheme.PK)| × 'T 'fin #|N.(NIKE_scheme.PK)|) × 'T E.(C)) × 'T 'fin #|E.(Nonce)|) → 'T E.(M)
].

Definition I_GMODPKAE_ID_COMP (N: NIKE_scheme) (E : NBSES_scheme) :=
  [interface
    #val #[ GEN ]: 'unit → 'T 'fin #|N.(NIKE_scheme.PK)| ;
    #val #[ CSETPK ]: 'T 'fin #|N.(NIKE_scheme.PK)| → 'unit
].

(*Definition I_GMODPKAE_OUT (N: NIKE_scheme) (E : NBSES_scheme) := I_MODPKAE_OUT N E :|: I_PKEY_OUT (NIKE_to_GEN N).

Definition I_GMODPKAE_ID_COMP (N: NIKE_scheme) := I_PKEY_OUT (NIKE_to_GEN N).*)

#[export] Hint Unfold I_GMODPKAE_OUT I_GMODPKAE_ID_COMP I_MODPKAE_OUT I_MODPKAE_IN I_NIKE_OUT I_NIKE_IN I_AE_OUT I_AE_IN I_PKEY_OUT I_KEY_OUT : in_fset_eq.

(*
Definition GMODPKAE (E : NBSES_scheme) (N : NIKE_scheme) (b : 'bool) :
  raw_module := (MODPKAE N E || ID (I_GMODPKAE_ID_COMP N)) ∘ (NIKE N || AE false E N).

Definition GMODPKAE (E : NBSES_scheme) (N : NIKE_scheme) (b : 'bool) :
  raw_module := (MODPKAE N E || ID (I_GMODPKAE_ID_COMP N)) ∘ (NIKE N || (AE false E N ∘ KEY false N (NBSES_to_SGEN E))).
*)

(* [THIS ONE SHOULD CONTAIN THE CORRECT SCHEMES]
Definition GMODPKAE (E : NBSES_scheme) (N : NIKE_scheme) (b : 'bool) :
  raw_module := (MODPKAE N E || ID (I_GMODPKAE_ID_COMP N)) ∘ ((NIKE N ∘ (PKEY true (NIKE_to_GEN N) || KEY false N (NBSES_to_SGEN E))) || (AE false E N ∘ KEY false N (NBSES_to_SGEN E))).
*)

(*
Definition GMODPKAE (E : NBSES_scheme) (N : NIKE_scheme) (b : 'bool) :
  raw_module := (MODPKAE N E || ID (I_GMODPKAE_ID_COMP N E)) ∘ ((NIKE N ∘ (PKEY true (NIKE_to_GEN N) || KEY false N (NIKE_to_SGEN N))) || (AE false E N ∘ KEY false N (NBSES_to_SGEN E))).
*)

(*
Definition GMODPKAE (E : NBSES_scheme) (N : NIKE_scheme) (b : 'bool) :
  raw_module := (MODPKAE N E || ID (I_GMODPKAE_ID_COMP N E)) ∘ (((NIKE N || AE false E N)) ∘ (PKEY true (NIKE_to_GEN N) || KEY false N (NIKE_to_SGEN N))).
*)

(* [THIS VERSION PROVES ALL GOALS BUT WON'T FINISH THE QED]
Definition GMODPKAE (E : NBSES_scheme) (N : NIKE_scheme) (b : 'bool) :
  raw_module := ((MODPKAE N E) ∘ ((NIKE N ∘ (PKEY true (NIKE_to_GEN N) || KEY false N (NIKE_to_SGEN N))) || (AE false E N ∘ KEY false N (NBSES_to_SGEN E)))) || (ID (I_GMODPKAE_ID_COMP N E) ∘ PKEY true (NIKE_to_GEN N)).


Lemma GMODPKAE_valid (E : NBSES_scheme) (N: NIKE_scheme) (b : 'bool) : ValidPackage (GMODPKAE E N b).(loc) [interface] (I_GMODPKAE_OUT N E) (GMODPKAE E N b).
Proof.
unfold GMODPKAE. nssprove_valid. Qed.
*)

End GMODPKAE.