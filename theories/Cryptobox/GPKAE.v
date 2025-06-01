(*This is a part of the implementation of the state-separated proof of security for the NaCl crypto_box public-key authenticated encryption scheme.
This file contains the specification for the GPKAE/GuPKAE games and corollary Corollary1_Adv_GPKAE.*)

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


Definition I_GPKAE_OUT (P: NBPES_scheme) :=
  [interface
    [ GEN ]    : { 'unit ~> 'option 'F P.(NBPES.PK) } ;
    [ CSETPK ] : { 'F P.(NBPES.PK) ~> 'unit } ;
    [ PKENC ]  : { (((('F P.(NBPES.PK)) × ('F P.(NBPES.PK))) × M P) × 'n P) ~> C P } ;
    [ PKDEC ]  : { (((('F P.(NBPES.PK)) × ('F P.(NBPES.PK))) × C P) × 'n P) ~> M P }
].

Definition I_GPKAE_ID_COMP (P: NBPES_scheme) :=
  [interface
    [ GEN ]    : { 'unit ~> 'option 'F P.(NBPES.PK) } ;
    [ CSETPK ] : { 'F P.(NBPES.PK) ~> 'unit }
].

#[export] Hint Unfold I_GPKAE_OUT I_GPKAE_ID_COMP I_PKAE_OUT I_PKAE_IN I_PKEY_OUT : in_fset_eq.

Definition GPKAE (P: NBPES_scheme) (b : 'bool) :
  raw_module := (PKAE P b || ID (I_GPKAE_ID_COMP P)) ∘ (PKEY (NBPES_to_GEN P) false).

Definition GuPKAE (P: NBPES_scheme) (b: 'bool) :
  raw_module := (PKAE P b || ID (I_GPKAE_ID_COMP P)) ∘ (PKEY (NBPES_to_GEN P) true).


Theorem Corollary1_Adv_GPKAE {P} (A : adversary (I_GPKAE_OUT P)) :
  AdvFor (GPKAE P) A
  <=  AdvFor (PKEY (NBPES_to_GEN P)) (A ∘ (PKAE P false || ID (I_GPKAE_ID_COMP P))) +
      AdvFor (GuPKAE P) A +
      AdvFor (PKEY (NBPES_to_GEN P)) (A ∘ (PKAE P true || ID (I_GPKAE_ID_COMP P))).
Proof.
unfold AdvFor, GPKAE, GuPKAE.
erewrite Adv_sym.
nssprove_adv_trans ((PKAE P false || ID (I_GPKAE_ID_COMP P)) ∘ (PKEY (NBPES_to_GEN P) true))%sep.
rewrite Adv_sep_link.
rewrite -GRing.addrA.
apply lerD.
1: rewrite Adv_sym ; apply lexx.
nssprove_adv_trans ((PKAE P true || ID (I_GPKAE_ID_COMP P)) ∘ (PKEY (NBPES_to_GEN P) true))%sep.
apply lerD.
1: rewrite Adv_sym ; apply lexx.
rewrite Adv_sep_link.
apply lexx.
Qed.


End GPKAE.