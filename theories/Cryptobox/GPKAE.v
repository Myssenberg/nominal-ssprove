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

From NominalSSP Require Import PKAE PKEY NBPES.
Import NBPES PKEY PKAE.

Import PackageNotation.

#[local] Open Scope package_scope.
#[local] Open Scope ring_scope.

Module GPKAE.


Definition I_GPKAE_OUT (E: NBPES_scheme) :=
  [interface
    [ GEN ]    : { 'unit ~> 'option 'F E.(NBPES.PK) } ;
    [ CSETPK ] : { 'F E.(NBPES.PK) ~> 'unit } ;
    [ PKENC ]  : { (((('F E.(NBPES.PK)) × ('F E.(NBPES.PK))) × M E) × 'n E) ~> C E } ;
    [ PKDEC ]  : { (((('F E.(NBPES.PK)) × ('F E.(NBPES.PK))) × C E) × 'n E) ~> M E }
].

Definition I_GPKAE_ID_COMP (E: NBPES_scheme) :=
  [interface
    [ GEN ]    : { 'unit ~> 'option 'F E.(NBPES.PK) } ;
    [ CSETPK ] : { 'F E.(NBPES.PK) ~> 'unit }
].

#[export] Hint Unfold I_GPKAE_OUT I_GPKAE_ID_COMP I_PKAE_OUT I_PKAE_IN I_PKEY_OUT : in_fset_eq.

Definition GPKAE (E: NBPES_scheme) (b : 'bool) :
  raw_module := (PKAE E b || ID (I_GPKAE_ID_COMP E)) ∘ (PKEY (NBPES_to_GEN E) false).

Definition GuPKAE (E: NBPES_scheme) (b: 'bool) :
  raw_module := (PKAE E b || ID (I_GPKAE_ID_COMP E)) ∘ (PKEY (NBPES_to_GEN E) true).


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
1: rewrite Adv_sym ; apply lexx.
nssprove_adv_trans ((PKAE E true || ID (I_GPKAE_ID_COMP E)) ∘ (PKEY (NBPES_to_GEN E) true))%sep.
apply lerD.
1: rewrite Adv_sym ; apply lexx.
rewrite Adv_sep_link.
apply lexx.
Qed.


End GPKAE.