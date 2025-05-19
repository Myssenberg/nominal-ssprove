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


(* Definition HS_loc (N : NIKE_scheme) : Location := (chMap ('pk N × 'pk N) 'nat; 31). *) (*Check loc here*)


Definition GH_locs_tt (E: NBSES_scheme) (N : NIKE_scheme) := fset [::  HC_loc N ; M_loc E N].
Definition GH_locs_ff (E: NBSES_scheme) (N : NIKE_scheme) := fset [::  HC_loc N ; M_loc E N ].


Definition I_HYBRID_IN (E: NBSES_scheme) (N : NIKE_scheme) :=
  [interface
    [ SET ]  : { (('pk N × 'pk N) × 'shared_key N) ~> 'unit } ;
    [ CSET ] : { (('pk N × 'pk N) × 'shared_key N) ~> 'unit } ;
    [ GET ]  : { ('pk N × 'pk N) ~> 'shared_key N } ;
    [ GEN ]  : { 'unit ~> 'unit } ; 
    [ SENC ] : { (M E × 'n E) ~> C E } ;
    [ SDEC ] : { (C E × 'n E) ~> M E } ;
    [ ENC ]  : { ((('pk N × 'pk N) × M E) × 'n E) ~> C E } ;
    [ DEC ]  : { ((('pk N × 'pk N) × C E) × 'n E) ~> M E }
]. 

Definition I_HYBRID_OUT (E: NBSES_scheme) (N : NIKE_scheme) :=
  [interface
    [ SET ]  : { (('pk N × 'pk N) × 'shared_key N) ~> 'unit } ;
    [ CSET ] : { (('pk N × 'pk N) × 'shared_key N) ~> 'unit } ;
    [ ENC ]  : { ((('pk N × 'pk N) × M E) × 'n E) ~> C E } ;
    [ DEC ]  : { ((('pk N × 'pk N) × C E) × 'n E) ~> M E }
].

Definition HYBRID (E : NBSES_scheme) (N : NIKE_scheme) (I : NIKE.inj ('fin #|N.(NIKE.Shared_Key)|) ('fin #|E.(NBSES.Shared_Key)|)) i qset: 
  module (I_HYBRID_IN E N) (I_HYBRID_OUT E N) := 
  [module GH_locs_tt E N ;
    #def #[ SET ] ('((PKs, PKr), k) : (('pk N × 'pk N) × 'fin #|N.(NIKE.Shared_Key)|)) : ('unit) { (*old notation*)
      let gen := #import [ GEN ]  : { 'unit ~> 'unit } in
      let set := #import [ SET ]  : { (('pk N × 'pk N) × 'shared_key N) ~> 'unit } in      

      HCLOC ← get HC_loc N ;;
      #assert isSome (HCLOC (PKs, PKr)) as count ;;
      let counts := getSome (HCLOC (PKs, PKr)) count in
      #assert (counts < qset) ;;
      if (HCLOC (PKs, PKr) == None) then  
        if (counts == i) then
          gen Datatypes.tt ;;
(*           #put (HS_loc N) := setm HSLOC (PKs, PKr) (counts.+1) ;; (*Double check that *) this is correct*)
          set (PKs, PKr, k) ;;
          ret (Datatypes.tt : 'unit)
        else
(*           #put (HS_loc N) := setm HSLOC (PKs, PKr) (counts.+1) ;;           *)
          set (PKs, PKr, k) ;;          
          ret (Datatypes.tt : 'unit)
      else
        set (PKs, PKr, k) ;;
        ret (Datatypes.tt : 'unit)
    } ;

    #def #[ CSET ] ('((PKr, PKs), k) : (('pk N × 'pk N) × 'fin #|N.(NIKE.Shared_Key)|)) : ('unit) { (*old notation*)
      let cset := #import [ CSET ] : { (('pk N × 'pk N) × 'shared_key N) ~> 'unit } in

      cset (PKr, PKs, k) ;;
      ret (Datatypes.tt : 'unit)
    }  ;
    #def #[ ENC ] ('(((PKs, PKr), m), n) : (('pk N × 'pk N) × 'm E) × 'n E) : ('c E) { (*old notation*)
      let geti   := #import [ GET ]  : { ('pk N × 'pk N) ~> 'shared_key N } in      
      let SAEenc := #import [ SENC ] : { (M E × 'n E) ~> C E } in

      k ← geti (PKs, PKr) ;;
      MLOC ← get M_loc E N ;;
      HCLOC ← get HC_loc N ;; 
      
      
      #assert MLOC ((PKs, PKr), n) == None ;; 
      #assert isSome (HCLOC (PKs, PKr)) as count ;; 
      let counts := getSome (HCLOC (PKs, PKr)) count in 

      if (counts < i) then
          c ← E.(sample_C) ;;    (* Should be AE1 here*) 
          #put (M_loc E N) := setm MLOC ((PKr, PKs), n) (m, c) ;;
          ret c
      else if (i < counts) then 
          c ← E.(enc) m (I.(encode) k) n ;; (* Should be AE0 here*) 
          #put (M_loc E N) := setm MLOC ((PKr, PKs), n) (m, c) ;;
          ret c 
      else 
          c ← SAEenc (m, n) ;; 
          ret c 
          
    } ;
    
    #def #[ DEC ] ('(((PKr, PKs), c), n) : (('pk N × 'pk N) × 'c E) × 'n E) : ('m E) { (*old notation*)
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