(*This is a part of the implementation of the state-separated game-based proof of security for the NaCl crypto_box authenticated encryption scheme.
This file contains the specification for the GSAE game and following lemmas*)

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

From NominalSSP Require Import SAE NBSES.
Import SAE NBSES.

Import PackageNotation.

#[local] Open Scope package_scope.

Module GSAE.

Definition I_GSAE_OUT (E : NBSES_scheme) :=
  [interface
    [ GEN ]  : { 'unit ~> 'unit } ;
    [ SENC ] : { (M E × 'n E) ~> C E } ;
    [ SDEC ] : { (C E × 'n E) ~> M E }
].

Definition GSAE (E : NBSES_scheme) (b : 'bool) :
  raw_module := SAE E b.

Lemma GSAE_valid (E : NBSES_scheme) (b : 'bool) :
  ValidPackage (GSAE E b).(loc) [interface] (I_GSAE_OUT E) (GSAE E b).
Proof.
unfold GSAE. nssprove_valid. Qed.

End GSAE.