(*This is a part of the implementation of the state-separated game-based proof of security for the NaCl crypto_box authenticated encryption scheme.
This file contains the specification for a GMODPKAE game*)

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

From NominalSSP Require Import AE NBSES NIKE.
Import AE NBSES NIKE_scheme.

Import PackageNotation.

#[local] Open Scope package_scope.

Module MODPKAE.

Definition PKENC := 14%N.
Definition PKDEC := 15%N.

Definition I_MODPKAE_IN (N : NIKE_scheme) (E : NBSES_scheme) :=
  [interface
    #val #[ SHAREDKEY ]: ('pk N × 'pk N) → 'option 'unit ; 
    #val #[ ENC ]: ((('pk N × 'pk N) × 'm E) × 'n E) → 'c E ;
    #val #[ DEC ]: ((('pk N × 'pk N) × 'c E) × 'n E) → 'm E
].

Definition I_MODPKAE_OUT (N : NIKE_scheme) (E : NBSES_scheme) :=
[interface
    #val #[ PKENC ]: ((('pk N × 'pk N) × 'm E) × 'n E) → 'c E ; (*SHOULD COME FROM NBPES?*)
    #val #[ PKDEC ]: ((('pk N × 'pk N) × 'c E) × 'n E) → 'm E (*SHOULD COME FROM NBPES?*)
].

Definition SORT (N: NIKE_scheme) (PKs PKr : 'pk N) : ('pk N × 'pk N) :=
  if (PKs < PKr) then (PKs, PKr) : (prod _ _) else (PKr, PKs) : (prod _ _).

Definition MODPKAE (N : NIKE_scheme) (E : NBSES_scheme):
  module (I_MODPKAE_IN N E) (I_MODPKAE_OUT N E) :=
  [module no_locs ; 
    #def #[ PKENC ] ('(((PKs, PKr), m), n) : (('pk N × 'pk N) × 'm E) × 'n E) : ('c E) {
      #import {sig #[ SHAREDKEY ]: ('pk N × 'pk N) → 'option 'unit } as sharedkey ;;
      #import {sig #[ ENC ]: ((('pk N × 'pk N) × 'm E) × 'n E) → 'c E } as enc ;;
      #import {sig #[ DEC ]: ((('pk N × 'pk N) × 'c E) × 'n E) → 'm E } as dec ;;      
      let '(fst, snd) := SORT N PKs PKr in
      v ← sharedkey (PKs, PKr) ;;
      #assert v != None ;;
      C ← enc (fst, snd, m, n) ;;
      ret C
    } ;
    #def #[ PKDEC ] ('(((PKs, PKr), c), n) : (('pk N × 'pk N) × 'c E) × 'n E) : ('m E) {
      #import {sig #[ SHAREDKEY ]: ('pk N × 'pk N) → 'option 'unit } as sharedkey ;;
      #import {sig #[ ENC ]: ((('pk N × 'pk N) × 'm E) × 'n E) → 'c E } as enc ;;
      #import {sig #[ DEC ]: ((('pk N × 'pk N) × 'c E) × 'n E) → 'm E } as dec ;;
      let '(fst, snd) := SORT N PKs PKr in      
      v ← sharedkey (PKs, PKr) ;;
      #assert v != None ;;
      M ← dec (fst, snd, c, n) ;;
      ret M
    }
  ].

End MODPKAE.