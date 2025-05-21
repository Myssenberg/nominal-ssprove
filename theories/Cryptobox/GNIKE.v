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

From NominalSSP Require Import NIKE NBPES KEY PKEY PKAE GMODPKAE AE.
Import NIKE NBPES KEY PKEY GMODPKAE AE.

Import PackageNotation.

#[local] Open Scope package_scope.
#[local] Open Scope ring_scope.

Module GNIKE.

Definition I_GNIKE_OUT (N: NIKE_scheme) :=
  [interface
    [ SHAREDKEY ] : { (('F N.(NIKE.PK) × 'F N.(NIKE.PK))) ~> 'option 'unit } ;
    [ GEN ]       : { 'unit ~> 'F N.(NIKE.PK) } ;
    [ CSETPK ]    : { 'F N.(NIKE.PK) ~> 'unit } ;
    [ GET ]       : { ('F N.(NIKE.PK) × 'F N.(NIKE.PK)) ~> 'F N.(NIKE.Shared_Key) } ;
    [ HON ]       : { ('F N.(NIKE.PK) × 'F N.(NIKE.PK)) ~> 'option 'bool }
].

Definition I_GNIKE_ID_COMP (N: NIKE_scheme) :=
(I_GMODPKAE_ID_COMP N) :|: (I_AE_IN N).


#[export] Hint Unfold I_GNIKE_OUT I_GNIKE_ID_COMP I_NIKE_OUT I_NIKE_IN I_PKEY_OUT I_KEY_OUT I_GMODPKAE_ID_COMP I_AE_IN: in_fset_eq.

Definition GNIKE (N: NIKE_scheme) qset (b : 'bool) :
  raw_module := (NIKE N || ID (I_GNIKE_ID_COMP N)) ∘ (KEY N qset b || PKEY (NIKE_to_GEN N) false).

Definition GuNIKE (N: NIKE_scheme) qset (b : 'bool) :
  raw_module := (NIKE N || ID (I_GNIKE_ID_COMP N)) ∘ (KEY N qset b || PKEY (NIKE_to_GEN N) true).


(*
Lemma GuNIKE_valid (N: NIKE_scheme) qset (b : 'bool) : ValidPackage (GuNIKE N qset b).(loc) [interface] (I_GNIKE_OUT N) (GuNIKE N qset b).
Proof.
unfold GuNIKE. unfold I_GNIKE_ID_COMP. nssprove_valid. Qed.


Lemma GNIKE_valid (N: NIKE_scheme) qset (b : 'bool) :
  ValidPackage (GNIKE N qset b).(loc) [interface] (I_GNIKE_OUT N) (GNIKE N qset b).
Proof.
unfold GNIKE. unfold I_GNIKE_ID_COMP. nssprove_valid. Qed.*)


Theorem Corollary3_Adv_GNIKE_GuNIKE {N} (A : adversary (I_GNIKE_OUT N)) qset:
let A' := (A ∘ (NIKE N || ID (I_GNIKE_ID_COMP N)))%sep in
  AdvFor (GuNIKE N qset) A
  <= AdvFor (PKEY (NIKE_to_GEN N)) (A' ∘ (KEY N qset false || ID (I_PKEY_OUT (NIKE_to_GEN N)))) +
     AdvFor (GNIKE N qset) A +
     AdvFor (PKEY (NIKE_to_GEN N)) (A' ∘ (KEY N qset true || ID (I_PKEY_OUT (NIKE_to_GEN N)))).
Proof.
unfold AdvFor, GNIKE, GuNIKE.
repeat rewrite Adv_sep_link.
erewrite Adv_sym.
nssprove_adv_trans (KEY N qset false || PKEY (NIKE_to_GEN N) false).
erewrite -> Adv_par_r by nssprove_valid.
erewrite Adv_sym.
rewrite -GRing.addrA.
apply lerD.
- apply lexx.
- nssprove_adv_trans (KEY N qset true || PKEY (NIKE_to_GEN N) false).
  apply lerD.
  + erewrite Adv_sym.
    apply lexx.
  + erewrite -> Adv_par_r by nssprove_valid.
    rewrite Adv_sym.
    apply lexx.
Qed.


End GNIKE.