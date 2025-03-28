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

Module AE.

(*

Definition ae : NBSES := {|
    K         : 'fin #|el| ;
    K_pos     : Positive #|K| ;
    Nonce     : 'fin #|el| ;
    M         : 'fin #|el| ;
    C         : 'fin #|el| ;
    sample_C  := 
      {code
          c ← sample uniform #|el| ;;
          ret c
      } ;
    kgen      :



} 


Definition chSet t := chMap t 'unit.

Notation " 'set t " := (chSet t) (in custom pack_type at level 2).
Notation " 'set t " := (chSet t) (at level 2): package_scope.



Definition PK_loc (E : NBPES): Location := (chMap 'pk E 'bool ; 0).

Definition SK_loc (E : NBPES): Location := (chMap 'pk E 'sk E ; 1).

Definition M_loc (E: NBPES): Location := (chMap ('set (h E × 'n E)) ('set ('m E × 'c E)) ; 2). 


Definition PKAE_locs_tt (E : NBPES):= fset [:: PK_loc E ; SK_loc E ; M_loc E]. (*If they're using the same loc, can they share then because Nom-SSP will rename or do we get into trouble?*)
Definition PKAE_locs_ff (E : NBPES):= fset [:: PK_loc E ; SK_loc E ; M_loc E].

Definition GEN := 2%N.
Definition GETSK := 4%N.
Definition HONPK := 5%N.

Definition PKENC := 6%N.
Definition PKDEC := 7%N.


Definition I_AE_IN (E: NBPES) :=
  [interface
    #val #[ GETSK ]: 'pk E → 'sk E ;  
    #val #[ HONPK ]: 'pk E → 'bool 
].

Definition I_AE_OUT (E: NBPES) :=
  [interface
    #val #[ PKENC ]: ('pk E × 'pk E × 'm E × 'n E) → 'c E ;
    #val #[ PKDEC ]: ('pk E × 'pk E × 'c E × 'n E) → 'm E 
].

Definition I_AE_OUT_TEMP (E: NBPES) :=
  [interface
    #val #[ PKENC ]: ('pk E × 'pk E) → 'bool
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

Definition AE (E: NBSES):
  module (I_AE_IN E) (I_AE_OUT_TEMP E)  := 
  [module PKAE_locs_tt E ;
    #def #[ PKENC ] ('(PKs, PKr) : 'pk E × 'pk E) : 'bool {
      #import {sig #[ GETSK ]: 'pk E → 'sk E } as getsk ;;
      #import {sig #[ HONPK ]: 'pk E → 'bool } as honpk ;;
      SKs ← getsk PKs ;;
      HONpkr ← honpk PKr ;;
      (*let h := if (PKs < PKr) then (PKs, PKr) else (PKr, PKs) in*)
      ret HONpkr
    }
  ].




Definition GPKAE_tt_PKEY_tt :=
  True. (*TEMPORARY*)

Definition GPKAE_tt_PKEY_ff :=
  False. (*TEMPORARY*)



End AE. *)