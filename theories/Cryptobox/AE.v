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

Notation " 'pk " := (PK) (in custom pack_type at level 2).
Notation " 'pk " := (PK) (at level 2): package_scope. 

Definition H : choice_type := ('pk × 'pk).


Notation " 'h " := (H) (in custom pack_type at level 2).
Notation " 'h " := (H) (at level 2): package_scope.

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

Notation " 'n E " := ('fin #|Nonce E|)
  (in custom pack_type at level 2, E constr at level 20).

Notation " 'n E " := ('fin #|Nonce E|)
  (at level 3) : package_scope.


Definition chSet t := chMap t 'unit.

Notation " 'set t " := (chSet t) (in custom pack_type at level 2).
Notation " 'set t " := (chSet t) (at level 2): package_scope. 


Definition M_loc (E: NBSES_scheme): Location := (chMap (('pk × 'pk) × 'n E) ('m E × 'c E) ; 0). 


Definition AE_locs_tt (E : NBSES_scheme):= fset [::  M_loc E]. (*If they're using the same loc, can they share then because Nom-SSP will rename or do we get into trouble?*)
Definition AE_locs_ff (E : NBSES_scheme):= fset [::  M_loc E].

Definition GET := 1%N.
Definition HON := 2%N.

Definition ENC := 3%N.
Definition DEC := 4%N.


Notation cdist :=
  (c ← sample uniform Big_N ;;
  ret c).


Definition I_AE_IN (E: NBSES_scheme) :=
  [interface
    #val #[ GET ]: ('pk × 'pk)→ 'k E ;
    #val #[ HON ]: ('pk × 'pk)  → 'bool 
].

Definition I_AE_OUT (E: NBSES_scheme) :=
  [interface
    #val #[ ENC ]: ((('pk × 'pk) × 'm E) × 'n E) → 'c E ;
    #val #[ DEC ]: ((('pk × 'pk) × 'c E) × 'n E) → 'm E 
].

Notation "x ← 'getSome' n ;; c" :=
  ( v ← get n ;;
    #assert (isSome v) as vSome ;;
    let x := getSome v vSome in
    c
  )
  (at level 100, n at next level, right associativity,
  format "x  ←  getSome  n  ;;  '//' c")
  : package_scope.

Definition AE (b : bool) (E: NBSES_scheme):
  module (I_AE_IN E) (I_AE_OUT E)  := 
  [module AE_locs_tt E ;
    #def #[ ENC ] ('(((PKr, PKs), m), n) : (('pk × 'pk) × 'm E) × 'n E) : ('c E) {
      #import {sig #[ GET ]: ('pk × 'pk) → 'k E } as geti ;;
      #import {sig #[ HON ]: ('pk × 'pk) → 'bool } as hon ;;
      
      k ← geti (PKr, PKs) ;;
      MLOC ← get M_loc E  ;;
      HON ← hon (PKr, PKs) ;;

      #assert MLOC ((PKr, PKs), n) == None ;;

      if (b && HON) then
        c ← E.(sample_C) ;; 
        #put (M_loc E) := setm MLOC ((PKr, PKs), n) (m, c) ;;
        ret c
      else 
         c ← E.(enc) m k n ;;
         #put (M_loc E) := setm MLOC ((PKr, PKs), n) (m, c) ;;
          ret c 
    } ; 

    #def #[ DEC ] ('(((PKr, PKs), c), n) : (('pk × 'pk) × 'c E) × 'n E) : ('m E) {
      #import {sig #[ GET ]: ('pk × 'pk) → 'k E } as geti ;;
      #import {sig #[ HON ]: ('pk × 'pk) → 'bool } as hon ;;

      k ← geti (PKr, PKs) ;;
      MLOC ← get M_loc E ;;
      HON ← hon (PKr, PKs) ;;
      

      if (b && HON) then
        
        #assert isSome (MLOC ((PKr, PKs), n)) as someC ;;
        let (m, c') := getSome (MLOC ((PKr, PKs), n)) someC in
        ret m

      else

        m ← E.(dec) c k n ;;
        ret m 
      

    } 
  ].




Definition GAE_tt_KEY_tt :=
  True. (*TEMPORARY*)

Definition GAE_tt_KEY_ff :=
  False. (*TEMPORARY*)



End AE.