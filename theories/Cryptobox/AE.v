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


Notation " 'T c " := (c) (in custom pack_type at level 2, c constr at level 20).
Notation " 'T c " := (c) (at level 2): package_scope.

Definition M_loc (pk n : finType) (m c : choice_type) `{Positive #|pk|} `{Positive #|n|} : Location := (chMap (('fin #|pk| × 'fin #|pk|) × 'fin #|n|) (m × c); 0).

(*Definition M_loc (E : NBSES_scheme) : Location := (chMap (('pk E × 'pk E) × 'n E) ('m E × 'c E); 0).*)


Definition AE_locs_tt (pk n : finType) (m c: choice_type) `{Positive #|pk|} `{Positive #|n|}:= fset [::  M_loc pk n m c].
Definition AE_locs_ff (pk n : finType) (m c: choice_type) `{Positive #|pk|} `{Positive #|n|}:= fset [::  M_loc pk n m c].

Definition GET := 1%N.
Definition HON := 2%N.

Definition ENC := 3%N.
Definition DEC := 4%N.


Definition I_AE_IN (pk k : choice_type) :=
  [interface
    #val #[ GET ]: ('T pk × 'T pk) → 'T k ;
    #val #[ HON ]: ('T pk × 'T pk)  → 'bool 
].

Definition I_AE_OUT (pk m n c: choice_type) :=
  [interface
    #val #[ ENC ]: ((('T pk × 'T pk) × 'T m) × 'T n) → 'T c ;
    #val #[ DEC ]: ((('T pk × 'T pk) × 'T c) × 'T n) → 'T m 
].

Definition AE (b : bool) (m c: choice_type) (pk n k: finType) `{Positive #|pk|} `{Positive #|n|} `{Positive #|k|} (sample_C : code fset0 [interface] c) (enc : forall (m' : m) (k' : 'T 'fin #|k|) (n' : 'T 'fin #|n|), code fset0 [interface] c) (dec : forall (c' : c) (k' : 'T 'fin #|k|) (n' : 'fin #|n|), code fset0 [interface] m):
  module (I_AE_IN 'fin #|pk| 'fin #|k|) (I_AE_OUT 'fin #|pk| m 'fin #|n| c)  := 
  [module AE_locs_tt pk n m c ;
    #def #[ ENC ] ('(((PKr, PKs), m'), n') : (('T 'fin #|pk| × 'T 'fin #|pk|) × 'T m) × 'T 'fin #|n|) : ('T c ){
      #import {sig #[ GET ]: ('T 'fin #|pk| × 'T 'fin #|pk|) → 'T 'fin #|k| } as geti ;;
      #import {sig #[ HON ]: ('T 'fin #|pk| × 'T 'fin #|pk|) → 'bool } as hon ;;
      
      k' ← geti (PKr, PKs) ;;
      
      MLOC ← get M_loc pk n m c  ;; 
      HON ← hon (PKr, PKs) ;;   

      #assert MLOC ((PKr, PKs), n') == None ;; 

      if (b && HON) then
        c' ← sample_C ;; 
        #put (M_loc pk n m c) := setm MLOC ((PKr, PKs), n') (m', c') ;;
        ret c'
      else 
         c' ← enc m' k' n' ;;
         #put (M_loc pk n m c) := setm MLOC ((PKr, PKs), n') (m', c') ;;
         ret c' 
      
    } ; 

    #def #[ DEC ] ('(((PKr, PKs), c'), n') : (('T 'fin #|pk| × 'T 'fin #|pk|) × 'T c) × 'T 'fin #|n|) : ('T m) {
      #import {sig #[ GET ]: ('T 'fin #|pk| × 'T 'fin #|pk|) → 'T 'fin #|k| } as geti ;;
      #import {sig #[ HON ]: ('T 'fin #|pk| × 'T 'fin #|pk|) → 'bool } as hon ;;

      k' ← geti (PKr, PKs) ;;
      MLOC ← get M_loc pk n m c ;;
      HON ← hon (PKr, PKs) ;;
      

      if (b && HON) then
        
        #assert isSome (MLOC ((PKr, PKs), n')) as someC ;;
        let (m', c') := getSome (MLOC ((PKr, PKs), n')) someC in
        ret m'

      else

        m' ← dec c' k' n' ;;
        ret m' 
      
    
    } 
  ].




Definition GAE_tt_KEY_tt :=
  True. (*TEMPORARY*)

Definition GAE_tt_KEY_ff :=
  False. (*TEMPORARY*)



End AE.