(*This is a part of the implementation of the state-separated game-based proof of security for the NaCl crypto_box authenticated encryption scheme.
This file contains the specification for the HYBRID package*)

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

From NominalSSP Require Import SAE KEY NBSES NIKE AE.

Import SAE KEY NBSES NIKE AE.

Module HYBRID.


Definition I_HYBRID_IN (E: NBSES_scheme) (N : NIKE_scheme) :=
  [interface
    [ SET ]  : { (('pk N × 'pk N) × 'shared_key N) ~> 'unit } ;
    [ CSET ] : { (('pk N × 'pk N) × 'shared_key N) ~> 'unit } ;
    [ GET ]  : { 'SID N ~> 'shared_key N } ;
    [ GEN ]  : { 'unit ~> 'unit } ; 
    [ SENC ] : { (M E × 'n E) ~> C E } ;
    [ SDEC ] : { (C E × 'n E) ~> M E } 
].

Definition I_HYBRID_OUT (E: NBSES_scheme) (N : NIKE_scheme) :=
  [interface
    [ SET ]  : { (('pk N × 'pk N) × 'shared_key N) ~> 'unit } ;
    [ CSET ] : { (('pk N × 'pk N) × 'shared_key N) ~> 'unit } ;
    [ ENC ]  : { ((('pk N × 'pk N) × M E) × 'n E) ~> C E } ;
    [ DEC ]  : { ((('pk N × 'pk N) × C E) × 'n E) ~> M E }
].

Definition HYBRID (E : NBSES_scheme) (N : NIKE_scheme) (I : inj ('F N.(NIKE.Shared_Key)) ('F E.(NBSES.Shared_Key))) i qset: 
  module (I_HYBRID_IN E N) (I_HYBRID_OUT E N) := 
  [module fset [::  HC_loc N ; M_loc E N] ;
    [ SET ]  : { (('pk N × 'pk N) × 'shared_key N) ~> 'unit } '((PKs, PKr), k) {
      let gen := #import [ GEN ]  : { 'unit ~> 'unit } in
      let set := #import [ SET ]  : { (('pk N × 'pk N) × 'shared_key N) ~> 'unit } in      

      HCLOC ← get HC_loc N ;;
      #assert isSome (HCLOC (PKs, PKr)) as count ;;
      let counts := getSome (HCLOC (PKs, PKr)) count in
      #assert (counts < qset) ;;
      if (HCLOC (PKs, PKr) == None) then  
        if (counts == i) then
          gen Datatypes.tt ;;
          set (PKs, PKr, k) ;;
          ret (Datatypes.tt : 'unit)
        else
          set (PKs, PKr, k) ;;          
          ret (Datatypes.tt : 'unit)
      else
        set (PKs, PKr, k) ;;
        ret (Datatypes.tt : 'unit)
    } ;

    [ CSET ] : { (('pk N × 'pk N) × 'shared_key N) ~> 'unit } '((PKr, PKs), k) { 
      let cset := #import [ CSET ] : { (('pk N × 'pk N) × 'shared_key N) ~> 'unit } in

      cset (PKr, PKs, k) ;;
      ret (Datatypes.tt : 'unit)
    }  ;
    [ ENC ]  : { ((('pk N × 'pk N) × M E) × 'n E) ~> C E } '(((PKs, PKr), m), n) { 
      let geti   := #import [ GET ]  : { ('pk N × 'pk N) ~> 'shared_key N } in      
      let SAEenc := #import [ SENC ] : { (M E × 'n E) ~> C E } in

      k ← geti (PKs, PKr) ;;
      MLOC ← get M_loc E N ;;
      HCLOC ← get HC_loc N ;; 
      
      
      #assert MLOC ((PKs, PKr), n) == None ;; 
      #assert isSome (HCLOC (PKs, PKr)) as count ;; 
      let counts := getSome (HCLOC (PKs, PKr)) count in 

      if (counts < i) then
          c ← E.(sample_C) ;; 
          #put (M_loc E N) := setm MLOC ((PKr, PKs), n) (m, c) ;;
          ret c
      else if (i < counts) then 
          c ← E.(enc) m (I.(encode) k) n ;;
          #put (M_loc E N) := setm MLOC ((PKr, PKs), n) (m, c) ;;
          ret c 
      else 
          c ← SAEenc (m, n) ;; 
          ret c 
          
    } ;
    
    [ DEC ]  : { ((('pk N × 'pk N) × C E) × 'n E) ~> M E } '(((PKr, PKs), c), n) { 
      let geti   := #import [ GET ]  : { ('pk N × 'pk N) ~> 'shared_key N } in
      let SAEdec := #import [ SDEC ] : { (C E × 'n E) ~> M E } in
      
      k ← geti (PKs, PKr) ;;
      MLOC ← get M_loc E N ;;
      HCLOC ← get HC_loc N ;; 

      #assert isSome (HCLOC (PKs, PKr)) as count ;;
      let counts := getSome (HCLOC (PKs, PKr)) count in
      if (counts < i) then
          #assert isSome (MLOC ((PKr, PKs), n)) as someC ;;
          let (m, c') := getSome (MLOC ((PKr, PKs), n)) someC in
          ret m
      else if (i < counts) then 
          m ← E.(dec) c (I.(encode) k) n ;;
          ret m 
      else 
          m ← SAEdec (c, n) ;;
          ret m
    } 

  ].


End HYBRID.