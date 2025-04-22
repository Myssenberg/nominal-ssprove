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

From NominalSSP Require Import NIKE KEY PKEY PKAE.
Import NIKE_scheme NBPES_scheme KEY PKEY.

Import PackageNotation.

#[local] Open Scope package_scope.

Module GNIKE.

Definition GEN := 2%N.
Definition HON := 30%N.
Definition CSETPK := 3%N.
Definition GET := 29%N. (*tal skal være forskellige across filer*)

Notation " 'T c " := (c) (in custom pack_type at level 2, c constr at level 20).
Notation " 'T c " := (c) (at level 2): package_scope.


(*
Definition I_GNIKE_OUT (N: NIKE_scheme) :=
  [interface
    #val #[ SHAREDKEY ]: (('fin #|N.(NIKE_scheme.PK)|) × ('fin #|N.(NIKE_scheme.PK)|)) → 'unit ;
    #val #[ GEN ]: 'unit → 'T 'fin #|N.(NIKE_scheme.PK)| ;
    #val #[ CSETPK ]: 'T 'fin #|N.(NIKE_scheme.PK)| → 'unit ;
    #val #[ GET ]:  ('SID N) → 'shared_key N ;
    #val #[ HON ]:  ('SID N) → 'bool
].

Definition I_GNIKE_ID_COMP (N: NIKE_scheme) :=
  [interface
    #val #[ GEN ]: 'unit → 'T 'fin #|N.(NIKE_scheme.PK)| ;
    #val #[ CSETPK ]: 'T 'fin #|N.(NIKE_scheme.PK)| → 'unit ;
    #val #[ GET ]:  ('SID N) → 'shared_key N ;
    #val #[ HON ]:  ('SID N) → 'bool
].*)

Definition I_GNIKE_OUT (N: NIKE_scheme) :=
  [interface
    #val #[ SHAREDKEY ]: (('fin #|N.(NIKE_scheme.PK)|) × ('fin #|N.(NIKE_scheme.PK)|)) → 'unit ;
    #val #[ GEN ]: 'unit → 'T 'fin #|N.(NIKE_scheme.PK)| ;
    #val #[ CSETPK ]: 'T 'fin #|N.(NIKE_scheme.PK)| → 'unit ;
    #val #[ GET ]:  (('fin #|N.(NIKE_scheme.PK)|) × ('fin #|N.(NIKE_scheme.PK)|)) → 'fin #|N.(NIKE_scheme.Shared_Key)| ;
    #val #[ HON ]:  (('fin #|N.(NIKE_scheme.PK)|) × ('fin #|N.(NIKE_scheme.PK)|)) → 'bool
].

Definition I_GNIKE_ID_COMP (N: NIKE_scheme) :=
  [interface
    #val #[ GEN ]: 'unit → 'T 'fin #|N.(NIKE_scheme.PK)| ;
    #val #[ CSETPK ]: 'T 'fin #|N.(NIKE_scheme.PK)| → 'unit ;
    #val #[ GET ]:  (('fin #|N.(NIKE_scheme.PK)|) × ('fin #|N.(NIKE_scheme.PK)|)) → 'fin #|N.(NIKE_scheme.Shared_Key)| ;
    #val #[ HON ]:  (('fin #|N.(NIKE_scheme.PK)|) × ('fin #|N.(NIKE_scheme.PK)|)) → 'bool
].

Definition I_R_PKEY_OUT (N: NIKE_scheme) := I_NIKE_OUT N :|: I_KEY_OUT N (NIKE_to_SGEN N).

#[export] Hint Unfold I_GNIKE_OUT I_GNIKE_ID_COMP I_NIKE_OUT I_NIKE_IN I_PKEY_OUT I_KEY_OUT I_R_PKEY_OUT : in_fset_eq.

Definition GNIKE (N: NIKE_scheme) (b : 'bool) :
  raw_module := (NIKE N || ID (I_GNIKE_ID_COMP N)) ∘ (KEY b N (NIKE_to_SGEN N) || PKEY b (NIKE_to_GEN N)).

Definition GuNIKE (N: NIKE_scheme) (b : 'bool) :
  raw_module := (NIKE N || ID (I_GNIKE_ID_COMP N)) ∘ (KEY b N (NIKE_to_SGEN N) || PKEY true (NIKE_to_GEN N)).

Lemma GuNIKE_valid (N: NIKE_scheme) (b : 'bool) : ValidPackage (GuNIKE N b).(loc) [interface] (I_GNIKE_OUT N) (GuNIKE N b).
Proof.
unfold GuNIKE. nssprove_valid. Qed.


Definition R_PKEY (N: NIKE_scheme) (b : 'bool) :
  raw_module := (NIKE N || KEY b N (NIKE_to_SGEN N)).

Lemma R_PKEY_valid (N: NIKE_scheme) (b : bool) : ValidPackage (R_PKEY N b).(loc) (I_NIKE_IN N) (I_R_PKEY_OUT N) (R_PKEY N b).
Proof.
unfold R_PKEY. nssprove_valid. Qed.

Lemma GNIKE_valid (N: NIKE_scheme) (b : 'bool) : ValidPackage (GNIKE N b).(loc) [interface] (I_GNIKE_OUT N) (GNIKE N b).
Proof.
unfold GNIKE. nssprove_valid. Qed.


End GNIKE.