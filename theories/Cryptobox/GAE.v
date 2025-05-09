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
Import AE KEY NBSES NIKE_scheme.

Import PackageNotation.

#[local] Open Scope package_scope.

Module GAE.

Notation " 'T c " := (c) (in custom pack_type at level 2, c constr at level 20).
Notation " 'T c " := (c) (at level 2): package_scope.

Definition SET := 27%N.
Definition CSET := 28%N.
Definition ENC := 52%N.
Definition DEC := 53%N.

Definition I_GAE_OUT (E : NBSES_scheme) (N : NIKE_scheme) :=
  [interface
    #val #[ SET ]: ('SID N × 'fin #|N.(NIKE_scheme.Shared_Key)|) → 'unit ;
    #val #[ CSET ]: ('SID N × 'fin #|N.(NIKE_scheme.Shared_Key)|) → 'unit ;
    #val #[ ENC ]: ((('pk N × 'pk N) × 'm E) × 'n E) → 'c E ;
    #val #[ DEC ]: ((('pk N × 'pk N) × 'c E) × 'n E) → 'm E 
].

Definition I_GAE_ID_COMP (N : NIKE_scheme) :=
  [interface
    #val #[ SET ]: ('SID N × 'fin #|N.(NIKE_scheme.Shared_Key)|) → 'unit ;
    #val #[ CSET ]: ('SID N × 'fin #|N.(NIKE_scheme.Shared_Key)|) → 'unit
].

#[export] Hint Unfold I_GAE_OUT I_GAE_ID_COMP I_AE_IN I_AE_OUT I_KEY_OUT I_NIKE_IN I_NIKE_OUT : in_fset_eq.

Definition GAE (E : NBSES_scheme) (N : NIKE_scheme) (I : NIKE_scheme.inj ('fin #|N.(NIKE_scheme.Shared_Key)|) ('fin #|E.(NBSES.Shared_Key)|)) (b : 'bool):
  raw_module := (AE E N I b || ID (I_GAE_ID_COMP N)) ∘ (KEY N true).

Lemma GAE_valid (E : NBSES_scheme) (N: NIKE_scheme) (I : NIKE_scheme.inj ('fin #|N.(NIKE_scheme.Shared_Key)|) ('fin #|E.(NBSES.Shared_Key)|)) (b : 'bool) :
  ValidPackage (GAE E N I b).(loc) [interface] (I_GAE_OUT E N) (GAE E N I b).
Proof.
unfold GAE. nssprove_valid. Qed.


(* Definition I_GAE_OUT (E : NBSES_scheme) (N : NIKE_scheme) :=
  [interface
    #val #[ SET ]: ('SID N × 'fin #|E.(NBSES.Shared_Key)|) → 'unit ;
    #val #[ CSET ]: ('SID N × 'fin #|E.(NBSES.Shared_Key)|) → 'unit ;
    #val #[ ENC ]: ((('pk N × 'pk N) × 'm E) × 'n E) → 'c E ;
    #val #[ DEC ]: ((('pk N × 'pk N) × 'c E) × 'n E) → 'm E 
].

Definition I_GAE_ID_COMP (N : NIKE_scheme) (E : NBSES_scheme) :=
  [interface
    #val #[ SET ]: ('SID N × 'fin #|E.(NBSES.Shared_Key)|) → 'unit ;
    #val #[ CSET ]: ('SID N × 'fin #|E.(NBSES.Shared_Key)|) → 'unit
].

#[export] Hint Unfold I_GAE_OUT I_GAE_ID_COMP I_AE_IN I_AE_OUT I_KEY_OUT I_NIKE_IN I_NIKE_OUT : in_fset_eq.

Definition GAE (E : NBSES_scheme) (N : NIKE_scheme) (b : 'bool):
  raw_module := (AE E N b || ID (I_GAE_ID_COMP N E)) ∘ (KEY N (NBSES_to_SGEN E) true).

Lemma GAE_valid (E : NBSES_scheme) (N: NIKE_scheme) (b : 'bool) :
  ValidPackage (GAE E N b).(loc) [interface] (I_GAE_OUT E N) (GAE E N b).
Proof.
unfold GAE. nssprove_valid. Qed. *)

End GAE.