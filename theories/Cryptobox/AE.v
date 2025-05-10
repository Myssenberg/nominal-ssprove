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

From NominalSSP Require Import Prelude Group.
Import PackageNotation.

#[local] Open Scope package_scope.

From NominalSSP Require Import NBSES NIKE.

Import NBSES NIKE_scheme.

Module AE.


Notation " 'T c " := (c) (in custom pack_type at level 2, c constr at level 20).
Notation " 'T c " := (c) (at level 2): package_scope.

Definition M_loc (E: NBSES_scheme) (N : NIKE_scheme) : Location := (chMap (('pk N × 'pk N) × 'n E) ('m E × 'c E); 54).

Definition AE_locs_tt (E: NBSES_scheme) (N : NIKE_scheme) := fset [::  M_loc E N].
Definition AE_locs_ff (E: NBSES_scheme) (N : NIKE_scheme) := fset [::  M_loc E N].

Definition GET := 29%N.
Definition HON := 30%N.

Definition ENC := 52%N.
Definition DEC := 53%N.


Definition I_AE_IN (N : NIKE_scheme) :=
  [interface
    #val #[ GET ]: ('pk N × 'pk N) → 'fin #|N.(NIKE_scheme.Shared_Key)| ;
    #val #[ HON ]: ('pk N × 'pk N)  → 'option 'bool 
].

Definition I_AE_OUT (E: NBSES_scheme) (N : NIKE_scheme) :=
  [interface
    #val #[ ENC ]: ((('pk N × 'pk N) × 'm E) × 'n E) → 'c E ;
    #val #[ DEC ]: ((('pk N × 'pk N) × 'c E) × 'n E) → 'm E 
].

Definition AE (E: NBSES_scheme) (N : NIKE_scheme) (I : NIKE_scheme.inj ('fin #|N.(NIKE_scheme.Shared_Key)|) ('fin #|E.(NBSES.Shared_Key)|)) (b : bool) :
  module (I_AE_IN N) (I_AE_OUT E N) := 
  [module AE_locs_tt E N;
    #def #[ ENC ] ('(((PKr, PKs), m), n) : (('pk N × 'pk N) × 'm E) × 'n E) : ('c E) {
      #import {sig #[ GET ]: ('pk N × 'pk N) → 'fin #|N.(NIKE_scheme.Shared_Key)| } as geti ;;
      #import {sig #[ HON ]: ('pk N × 'pk N) → 'option 'bool } as hon ;;
      
      k ← geti (PKr, PKs) ;;
      MLOC ← get M_loc E N ;;
      HON ← hon (PKr, PKs) ;;

      #assert MLOC ((PKr, PKs), n) == None ;;

      if (b && HON) then
        c ← E.(sample_C) ;; 
        #put (M_loc E N) := setm MLOC ((PKr, PKs), n) (m, c) ;;
        ret c
      else 
         c ← E.(enc) m (I.(encode) k) n ;;
         #put (M_loc E N) := setm MLOC ((PKr, PKs), n) (m, c) ;;
          ret c 
    } ; 

    #def #[ DEC ] ('(((PKr, PKs), c), n) : (('pk N × 'pk N) × 'c E) × 'n E) : ('m E) {
      #import {sig #[ GET ]: ('pk N × 'pk N) → 'fin #|N.(NIKE_scheme.Shared_Key)| } as geti ;;
      #import {sig #[ HON ]: ('pk N × 'pk N) → 'option 'bool } as hon ;;

      k ← geti (PKr, PKs) ;;
      MLOC ← get M_loc E N;;
      HON ← hon (PKr, PKs) ;;
      

      if (b && HON) then
        
        #assert isSome (MLOC ((PKr, PKs), n)) as someC ;;
        let (m, c') := getSome (MLOC ((PKr, PKs), n)) someC in
        ret m

      else

        m ← E.(dec) c (I.(encode) k) n ;;
        ret m 
      

    } 
  ].

End AE.