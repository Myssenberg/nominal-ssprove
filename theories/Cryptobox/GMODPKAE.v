(*This is a part of the implementation of the state-separated proof of security for the NaCl crypto_box public-key authenticated encryption scheme.
This file contains the specification for the GMODPKAE game*)

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

From NominalSSP Require Import AE KEY MODPKAE NBSES NBPES NIKE PKAE PKEY.
Import AE KEY MODPKAE NBSES NBPES NIKE PKEY.

Import PackageNotation.

#[local] Open Scope package_scope.

Module GMODPKAE.

Definition I_GMODPKAE_OUT (N: NIKE_scheme) (E : NBSES_scheme) :=
  [interface
    [ GEN ]    : { 'unit ~> 'option 'F (N.(NIKE.PK)) } ;
    [ CSETPK ] : { 'F (N.(NIKE.PK)) ~> 'unit } ;
    [ PKENC ]  : { ((('F (N.(NIKE.PK)) × 'F (N.(NIKE.PK))) × E.(NBSES.M)) × 'F (E.(NBSES.Nonce))) ~> E.(NBSES.C) } ; 
    [ PKDEC ]  : { ((('F (N.(NIKE.PK)) × 'F (N.(NIKE.PK))) × E.(NBSES.C)) × 'F (E.(NBSES.Nonce))) ~> E.(NBSES.M) }
].

Definition I_GMODPKAE_ID_COMP (N: NIKE_scheme) :=
  [interface
    [ GEN ]    : { 'unit ~> 'option 'F N.(NIKE.PK) };
    [ CSETPK ] : { 'F N.(NIKE.PK) ~> 'unit }
].


#[export] Hint Unfold I_GMODPKAE_OUT I_GMODPKAE_ID_COMP I_MODPKAE_OUT I_MODPKAE_IN I_NIKE_OUT I_NIKE_IN I_AE_OUT I_AE_IN I_PKEY_OUT I_KEY_OUT : in_fset_eq.


Definition GMODPKAE (E : NBSES_scheme) (N : NIKE_scheme) qset (I : inj 'shared_key N 'k E) (b : 'bool) :
  raw_module := (ID (I_GMODPKAE_ID_COMP N) || ((MODPKAE N E) ∘ ((NIKE N || AE E N I b)))) ∘ ((PKEY (NIKE_to_GEN N) true || KEY N qset b)).


End GMODPKAE.