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

From NominalSSP Require Import AE KEY NBSES NIKE.
Import AE KEY NBSES NIKE_scheme.

Import PackageNotation.

#[local] Open Scope package_scope.

Module GAE.

Notation " 'T c " := (c) (in custom pack_type at level 2, c constr at level 20).
Notation " 'T c " := (c) (at level 2): package_scope.

Definition SET := 27%N.
Definition CSET := 28%N.
Definition ENC := 3%N.
Definition DEC := 4%N.


Definition I_GAE_OUT (E : NBSES_scheme) (N : NIKE_scheme) (pk : choice_type) :=
  [interface
    #val #[ SET ]: ('SID N × 'shared_key N) → 'unit ;
    #val #[ CSET ]: ('SID N × 'shared_key N) → 'unit ;
    #val #[ ENC ]: ((('T pk × 'T pk) × 'm E) × 'n E) → 'c E ;
    #val #[ DEC ]: ((('T pk × 'T pk) × 'c E) × 'n E) → 'm E 
].

Definition I_GAE_ID_COMP (E : NBSES_scheme) (N : NIKE_scheme) (pk : choice_type) :=
  [interface
    #val #[ SET ]: ('SID N × 'shared_key N) → 'unit ;
    #val #[ CSET ]: ('SID N × 'shared_key N) → 'unit ;
    #val #[ GET ]: ('T pk × 'T pk) → 'k E ;
    #val #[ HON ]: ('T pk × 'T pk)  → 'bool 
].

#[export] Hint Unfold I_GAE_OUT I_GAE_ID_COMP I_AE_IN I_AE_OUT I_KEY_OUT (*I_NIKE_OUT I_NIKE_IN*) : in_fset_eq.

(*Definition GAE (E : NBSES_scheme) (N : NIKE_scheme) (b : 'bool) (pk: finType) `{Positive #|pk|} :
  raw_module := (AE b E pk || ID (I_GAE_ID_COMP E N 'fin #|pk|)) ∘ (KEY b N).

Lemma GAE_valid (E : NBSES_scheme) (N: NIKE_scheme) (b : 'bool) (pk: finType) `{Positive #|pk|} : ValidPackage (GAE E N b pk).(loc) [interface] (I_GAE_OUT E N 'fin #|pk|) (GAE E N b pk).
Proof.
unfold GAE. nssprove_valid. fset_solve.*)

End GAE.