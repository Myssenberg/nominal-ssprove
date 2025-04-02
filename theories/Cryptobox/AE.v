(*This is an implementation of the state-separated game-based proof of security for the NaCl crypto_box authenticated encryption scheme.*)

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
Import PackageNotation.

#[local] Open Scope package_scope.

From NominalSSP Require Import NBSES.

Import NBSES.

Module AE.


Variable (n: nat).
Definition Big_N: nat := 2^n.
Definition PK: choice_type := chFin (mkpos Big_N).
Definition SessionID : choice_type := (PK × PK).

Notation " 'pk " := (PK) (in custom pack_type at level 2).
Notation " 'pk " := (PK) (at level 2): package_scope.
Notation " 'SID " := (SessionID) (in custom pack_type at level 2).
Notation " 'SID " := (SessionID) (at level 2): package_scope.

Notation " 'k E " := ('fin #|K E|)
  (in custom pack_type at level 2, E constr at level 20).

Notation " 'k E " := ('fin #|K E|)
  (at level 3) : package_scope.

Notation " 'm E " := (M E)
  (in custom pack_type at level 2, E constr at level 20).

Notation " 'm E " := (M E)
  (at level 3) : package_scope.

Notation " 'c E " := (C E)
  (in custom pack_type at level 2, E constr at level 20).

Notation " 'c E " := (C E)
  (at level 3) : package_scope.

Notation " 'n E " := (Nonce E)
  (in custom pack_type at level 2, E constr at level 20).

Notation " 'n E " := (Nonce E)
  (at level 3) : package_scope.


Definition chSet t := chMap t 'unit.

Notation " 'set t " := (chSet t) (in custom pack_type at level 2).
Notation " 'set t " := (chSet t) (at level 2): package_scope. 

Definition SID (E: NBSES_scheme) : choice_type := ('k E × 'k E). 




Definition M_loc (E: NBSES_scheme): Location := (chMap (SID E × 'n E) ('m E × 'c E) ; 0). 


Definition AE_locs_tt (E : NBSES_scheme):= fset [::  M_loc E]. (*If they're using the same loc, can they share then because Nom-SSP will rename or do we get into trouble?*)
Definition AE_locs_ff (E : NBSES_scheme):= fset [::  M_loc E].

Definition GET := 1%N.
Definition HON := 2%N.

Definition ENC := 3%N.
Definition DEC := 4%N.


Definition I_AE_IN (E: NBSES_scheme) :=
  [interface
    #val #[ GET ]: 'SID → 'k E ;
    #val #[ HON ]: 'SID  → 'bool 
].

Definition I_AE_OUT (E: NBSES_scheme) :=
  [interface
    #val #[ ENC ]: (('SID × 'm E) × 'n E) → 'c E ;
    #val #[ DEC ]: ('SID × 'c E × 'n E) → 'm E 
].


Notation "'getNone' n ;; c" :=
  ( v ← get n ;;
    #assert (v == None) ;;
    c
  )
  (at level 100, n at next level, right associativity,
  format "getNone  n  ;;  '//' c")
  : package_scope.

Notation "x ← 'getSome' n ;; c" :=
  ( v ← get n ;;
    #assert (isSome v) as vSome ;;
    let x := getSome v vSome in
    c
  )
  (at level 100, n at next level, right associativity,
  format "x  ←  getSome  n  ;;  '//' c")
  : package_scope.

Definition AE (E: NBSES_scheme):
  module (I_AE_IN E) (I_AE_OUT E)  := 
  [module PKAE_locs_tt E ;
    #def #[ ENC ] ('(PKs, PKr) : 'pk E × 'pk E) : 'bool {
      #import {sig #[ GET ]: 'SID → 'k E } as get ;;
      #import {sig #[ HON ]: 'SID → 'bool } as hon ;;
     
    }
  ].




Definition GPKAE_tt_PKEY_tt :=
  True. (*TEMPORARY*)

Definition GPKAE_tt_PKEY_ff :=
  False. (*TEMPORARY*)



End AE.