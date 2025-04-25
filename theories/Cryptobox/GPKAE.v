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

From NominalSSP Require Import PKAE PKEY.
Import NBPES_scheme PKEY.

Import PackageNotation.

#[local] Open Scope package_scope.

Module GPKAE.

Definition GEN := 2%N.
Definition CSETPK := 3%N.
Definition PKENC := 14%N.
Definition PKDEC := 15%N.
(*tal skal være forskellige across filer*)

Notation " 'T c " := (c) (in custom pack_type at level 2, c constr at level 20).
Notation " 'T c " := (c) (at level 2): package_scope.


Definition I_GPKAE_OUT (E: NBPES_scheme) :=
  [interface
    #val #[ GEN ]: 'unit → 'T 'fin #|E.(NBPES_scheme.PK)| ;
    #val #[ CSETPK ]: 'T 'fin #|E.(NBPES_scheme.PK)| → 'unit ;
    #val #[ PKENC ]: (((('fin #|E.(NBPES_scheme.PK)|) × ('fin #|E.(NBPES_scheme.PK)|)) × 'm E) × 'n E) → 'c E ;
    #val #[ PKDEC ]: (((('fin #|E.(NBPES_scheme.PK)|) × ('fin #|E.(NBPES_scheme.PK)|)) × 'c E) × 'n E) → 'm E
].

Definition I_GPKAE_ID_COMP (E: NBPES_scheme) :=
  [interface
    #val #[ GEN ]: 'unit → 'T 'fin #|E.(NBPES_scheme.PK)| ;
    #val #[ CSETPK ]: 'T 'fin #|E.(NBPES_scheme.PK)| → 'unit 
].

#[export] Hint Unfold I_GPKAE_OUT I_GPKAE_ID_COMP I_PKAE_OUT I_PKAE_IN I_PKEY_OUT : in_fset_eq.

Definition GPKAE (E: NBPES_scheme) (b : 'bool) :
  raw_module := (PKAE b E || ID (I_GPKAE_ID_COMP E)) ∘ (PKEY b (NBPES_to_GEN E)).

Definition GuPKAE (E: NBPES_scheme) (b: 'bool) :
  raw_module := (PKAE b E || ID (I_GPKAE_ID_COMP E)) ∘ (PKEY true (NBPES_to_GEN E)).

Lemma GuPKAE_valid (E: NBPES_scheme) (b: 'bool) : ValidPackage (GuPKAE E b).(loc) [interface] (I_GPKAE_OUT E) (GuPKAE E b).
Proof.
unfold GuPKAE. nssprove_valid. Qed.

Lemma GPKAE_valid (E: NBPES_scheme) (b : 'bool) : ValidPackage (GPKAE E b).(loc) [interface] (I_GPKAE_OUT E) (GPKAE E b).
Proof.
unfold GPKAE. nssprove_valid. Qed. 


End GPKAE.