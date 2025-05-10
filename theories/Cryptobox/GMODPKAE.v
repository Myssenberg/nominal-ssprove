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

From NominalSSP Require Import Prelude Group.

From NominalSSP Require Import AE KEY MODPKAE NBSES NIKE PKAE PKEY.
Import AE KEY MODPKAE NBSES NIKE_scheme NBPES_scheme PKEY.

Import PackageNotation.

#[local] Open Scope package_scope.

Module GMODPKAE.

(* VERSION WITHOUT NBPES *)

Definition PKENC := 14%N.
Definition PKDEC := 15%N.

Definition I_GMODPKAE_OUT (N: NIKE_scheme) (E : NBSES_scheme) :=
  [interface
    #val #[ GEN ]: 'unit → 'T 'fin #|N.(NIKE_scheme.PK)| ;
    #val #[ CSETPK ]: 'T 'fin #|N.(NIKE_scheme.PK)| → 'unit ;
    #val #[ PKENC ]: ((('T 'fin #|N.(NIKE_scheme.PK)| × 'T 'fin #|N.(NIKE_scheme.PK)|) × 'T E.(NBSES.M)) × 'T 'fin #|E.(NBSES.Nonce)|) → 'T E.(NBSES.C) ; 
    #val #[ PKDEC ]: ((('T 'fin #|N.(NIKE_scheme.PK)| × 'T 'fin #|N.(NIKE_scheme.PK)|) × 'T E.(NBSES.C)) × 'T 'fin #|E.(NBSES.Nonce)|) → 'T E.(NBSES.M)
].

Definition I_GMODPKAE_ID_COMP (N: NIKE_scheme) :=
  [interface
    #val #[ GEN ]: 'unit → 'T 'fin #|N.(NIKE_scheme.PK)| ;
    #val #[ CSETPK ]: 'T 'fin #|N.(NIKE_scheme.PK)| → 'unit
].

(* Solution without modified NIKE package *)
(* #[export] Hint Unfold I_GMODPKAE_OUT I_GMODPKAE_ID_COMP I_MODPKAE_OUT I_MODPKAE_IN I_NIKE_OUT I_NIKE_IN I_AE_OUT I_AE_IN I_PKEY_OUT I_KEY_OUT : in_fset_eq.

Definition GMODPKAE (E : NBSES_scheme) (N : NIKE_scheme) (b : 'bool) :
  raw_module := (ID (I_GMODPKAE_ID_COMP N) || ((MODPKAE N E) ∘ ((NIKE N || AE E N false)))) ∘ ((PKEY (NIKE_to_GEN N) true || KEY N (NBSES_to_SGEN E) false)).
*)

(* Working solution with modified NIKE package *)
#[export] Hint Unfold I_GMODPKAE_OUT I_GMODPKAE_ID_COMP I_MODPKAE_OUT I_MODPKAE_IN I_NIKE_OUT I_NIKE_IN I_AE_OUT I_AE_IN I_PKEY_OUT I_KEY_OUT : in_fset_eq.


Definition GMODPKAE (E : NBSES_scheme) (N : NIKE_scheme) qset (I : inj 'shared_key N 'k E) (b : 'bool) :
  raw_module := (ID (I_GMODPKAE_ID_COMP N) || ((MODPKAE N E) ∘ ((NIKE N || AE E N I b)))) ∘ ((PKEY (NIKE_to_GEN N) true || KEY N qset b)).

Lemma GMODPKAE_valid (E : NBSES_scheme) (N: NIKE_scheme) qset (b : 'bool) (I : inj 'shared_key N 'k E) : ValidPackage (GMODPKAE E N qset I b).(loc) [interface] (I_GMODPKAE_OUT N E) (GMODPKAE E N qset I b).
Proof.
unfold GMODPKAE. nssprove_valid. Qed.

(* VERSION WITH NBPES *)

(*
Definition I_GMODPKAE_OUT (N: NIKE_scheme) (F : NBPES_scheme) :=
  [interface
    #val #[ GEN ]: 'unit → 'T 'fin #|N.(NIKE_scheme.PK)| ;
    #val #[ CSETPK ]: 'T 'fin #|N.(NIKE_scheme.PK)| → 'unit ;
    #val #[ PKENC_MOD ]: ((('T 'fin #|F.(NBPES_scheme.PK)| × 'T 'fin #|F.(NBPES_scheme.PK)|) × 'T F.(NBPES_scheme.M)) × 'T 'fin #|F.(NBPES_scheme.Nonce)|) → 'T F.(NBPES_scheme.C) ;
    #val #[ PKDEC_MOD ]: ((('T 'fin #|F.(NBPES_scheme.PK)| × 'T 'fin #|F.(NBPES_scheme.PK)|) × 'T F.(NBPES_scheme.C)) × 'T 'fin #|F.(NBPES_scheme.Nonce)|) → 'T F.(NBPES_scheme.M)
].

Definition I_GMODPKAE_ID_COMP (N: NIKE_scheme) :=
  [interface
    #val #[ GEN ]: 'unit → 'T 'fin #|N.(NIKE_scheme.PK)| ;
    #val #[ CSETPK ]: 'T 'fin #|N.(NIKE_scheme.PK)| → 'unit
].

#[export] Hint Unfold I_GMODPKAE_OUT I_GMODPKAE_ID_COMP I_MODPKAE_OUT_F I_MODPKAE_IN I_NIKE_OUT I_NIKE_IN_E I_AE_OUT I_AE_IN I_PKEY_OUT I_KEY_OUT : in_fset_eq.

Definition GMODPKAE (E : NBSES_scheme) (N : NIKE_scheme) (F : NBPES_scheme) (I : inj 'shared_key N 'k E) (A : inji 'fin #|F.(NBPES_scheme.PK)| 'fin #|N.(NIKE_scheme.PK)|) (B : inji 'm F 'T E.(NBSES.M)) (C : inji 'n F 'T 'fin #|E.(NBSES.Nonce)|) (D : inji 'c F 'T E.(NBSES.C)) (b : 'bool) :
  raw_module := (ID (I_GMODPKAE_ID_COMP N) || ((MODPKAE_F N E F A B C D) ∘ ((NIKE_E N E I || AE E N false)))) ∘ ((PKEY (NIKE_to_GEN N) true || KEY N (NBSES_to_SGEN E) false)).

Lemma GMODPKAE_valid (E : NBSES_scheme) (N: NIKE_scheme) (F : NBPES_scheme) (I : inj 'shared_key N 'k E) (A : inji 'fin #|F.(NBPES_scheme.PK)| 'fin #|N.(NIKE_scheme.PK)|) (B : inji 'm F 'T E.(NBSES.M)) (C : inji 'n F 'T 'fin #|E.(NBSES.Nonce)|) (D : inji 'c F 'T E.(NBSES.C))  (b : 'bool) : ValidPackage (GMODPKAE E N F I A B C D b).(loc) [interface] (I_GMODPKAE_OUT N F) (GMODPKAE E N F I A B C D b).
Proof.
unfold GMODPKAE. nssprove_valid. Qed.*)

End GMODPKAE.