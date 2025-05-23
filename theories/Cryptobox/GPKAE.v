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

Import Num.Def.
Import Num.Theory.
Import Order.POrderTheory.

From NominalSSP Require Import Prelude Group.

From NominalSSP Require Import PKAE PKEY.
Import NBPES_scheme PKEY.

Import PackageNotation.

#[local] Open Scope package_scope.
#[local] Open Scope ring_scope.

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
  raw_module := (PKAE E b || ID (I_GPKAE_ID_COMP E)) ∘ (PKEY (NBPES_to_GEN E) false).

Definition GuPKAE (E: NBPES_scheme) (b: 'bool) :
  raw_module := (PKAE E b || ID (I_GPKAE_ID_COMP E)) ∘ (PKEY (NBPES_to_GEN E) true).

Lemma GuPKAE_valid (E: NBPES_scheme) (b: 'bool) : ValidPackage (GuPKAE E b).(loc) [interface] (I_GPKAE_OUT E) (GuPKAE E b).
Proof.
unfold GuPKAE. nssprove_valid. Qed.

Lemma GPKAE_valid (E: NBPES_scheme) (b : 'bool) : ValidPackage (GPKAE E b).(loc) [interface] (I_GPKAE_OUT E) (GPKAE E b).
Proof.
unfold GPKAE. nssprove_valid. Qed. 


Theorem Corollary1_Adv_GPKAE {E} (A : adversary (I_GPKAE_OUT E)) :
  AdvFor (GPKAE E) A
  <=  AdvFor (PKEY (NBPES_to_GEN E)) (A ∘ (PKAE E false || ID (I_GPKAE_ID_COMP E))) +
      AdvFor (GuPKAE E) A +
      AdvFor (PKEY (NBPES_to_GEN E)) (A ∘ (PKAE E true || ID (I_GPKAE_ID_COMP E))).
Proof.
unfold AdvFor, GPKAE, GuPKAE.
erewrite Adv_sym.
nssprove_adv_trans ((PKAE E false || ID (I_GPKAE_ID_COMP E)) ∘ (PKEY (NBPES_to_GEN E) true))%sep.
rewrite Adv_sep_link.
rewrite -GRing.addrA.
apply lerD.
  - rewrite Adv_sym.
    apply lexx.
  - nssprove_adv_trans ((PKAE E true || ID (I_GPKAE_ID_COMP E)) ∘ (PKEY (NBPES_to_GEN E) true))%sep.
    apply lerD.
  -- rewrite Adv_sym.
     apply lexx.
  -- rewrite Adv_sep_link.
     apply lexx.
Qed.


End GPKAE.