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

Definition I_GMODPKAE_ID_COMP (N: NIKE_scheme) :=
  [interface
    #val #[ GEN ]: 'unit → 'T 'fin #|N.(NIKE_scheme.PK)| ;
    #val #[ CSETPK ]: 'T 'fin #|N.(NIKE_scheme.PK)| → 'unit
].

(*#[export] Hint Unfold I_GMODPKAE_OUT I_GMODPKAE_ID_COMP I_MODPKAE_OUT I_MODPKAE_IN I_NIKE_OUT I_NIKE_IN I_AE_OUT I_AE_IN I_PKEY_OUT I_KEY_OUT : in_fset_eq.*)

#[export] Hint Unfold I_GMODPKAE_OUT I_GMODPKAE_ID_COMP I_MODPKAE_OUT I_MODPKAE_IN I_NIKE_OUT I_NIKE_IN_E I_AE_OUT I_AE_IN I_PKEY_OUT I_KEY_OUT : in_fset_eq.

(* 
(* Solution without modified NIKE package *)
Definition GMODPKAE (E : NBSES_scheme) (N : NIKE_scheme) (b : 'bool) :
  raw_module := (ID (I_GMODPKAE_ID_COMP N) || ((MODPKAE N E) ∘ ((NIKE N || AE false E N)))) ∘ ((PKEY true (NIKE_to_GEN N) || KEY false N (NBSES_to_SGEN E))).
*)

(* Working solution with modified NIKE package *)
Definition GMODPKAE (E : NBSES_scheme) (N : NIKE_scheme) (b : 'bool) (I : inj 'shared_key N 'k E) :
  raw_module := (ID (I_GMODPKAE_ID_COMP N) || ((MODPKAE N E) ∘ ((NIKE_E N E I || AE false E N)))) ∘ ((PKEY true (NIKE_to_GEN N) || KEY false N (NBSES_to_SGEN E))).

Lemma GMODPKAE_valid (E : NBSES_scheme) (N: NIKE_scheme) (b : 'bool) (I : inj 'shared_key N 'k E) : ValidPackage (GMODPKAE E N b I).(loc) [interface] (I_GMODPKAE_OUT N E) (GMODPKAE E N b I).
Proof.
unfold GMODPKAE. nssprove_valid. Qed.

End GMODPKAE.