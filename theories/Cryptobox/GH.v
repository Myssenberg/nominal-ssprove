(*This is a part of the implementation of the state-separated game-based proof of security for the NaCl crypto_box authenticated encryption scheme.
This file contains the specification for the GAE game and following lemmas*)

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

From NominalSSP Require Import GSAE KEY NBSES NIKE AE.

Import GSAE KEY NBSES NIKE_scheme AE.





Module GH.

Notation " 'T c " := (c) (in custom pack_type at level 2, c constr at level 20).
Notation " 'T c " := (c) (at level 2): package_scope.


Variable (i : 'nat).

Definition HS_loc (E: NBSES_scheme) (N : NIKE_scheme) : Location := (chMap ('pk N × 'pk N) 'nat; 31). (*Check loc here*)

Variable (counter : 'nat). 


Definition SET := 27%N.
Definition CSET := 28%N.
Definition ENC := 52%N.
Definition DEC := 53%N.
Definition GET := 29%N.
Definition HON := 30%N.


Definition GH_locs_tt (E: NBSES_scheme) (N : NIKE_scheme) := fset [::  HS_loc E N ].
Definition GH_locs_ff (E: NBSES_scheme) (N : NIKE_scheme) := fset [::  HS_loc E N ].

(*
Definition I_GH_IN (E: NBSES_scheme) (N : NIKE_scheme) (G : SGEN_scheme) :=
  [interface
    #val #[ SET ]: (('pk N × 'pk N) × 'shared_key G) → 'unit ;  
    #val #[ CSET ]: (('pk N × 'pk N) × 'shared_key G) → 'unit ;
    #val #[ ENC ]: ((('pk N × 'pk N) × 'm E) × 'n E) → 'c E ;
    #val #[ DEC ]: ((('pk N × 'pk N) × 'c E) × 'n E) → 'm E ;
    #val #[ GET ]: ('pk N × 'pk N) → 'fin #|E.(NBSES.Shared_Key)| ;
    #val #[ HON ]: ('pk N × 'pk N) → ('option 'bool) ;
    #val #[ GEN ]:  'unit → 'unit 
]. *)


Definition I_GH_IN (E: NBSES_scheme) (N : NIKE_scheme) := I_GSAE_OUT E :|: I_KEY_OUT N (NIKE_to_SGEN N) :|: I_AE_OUT E N.

Definition I_GH_OUT (E: NBSES_scheme) (N : NIKE_scheme) (G : SGEN_scheme) :=
  [interface
    #val #[ SET ]: (('pk N × 'pk N) × 'fin #|G.(SGEN_scheme.Shared_Key)|) → 'unit (* ;
    #val #[ CSET ]: (('pk N × 'pk N) × 'k E) → 'unit ;
    #val #[ ENC ]: ((('pk N × 'pk N) × 'm E) × 'n E) → 'c E ;
    #val #[ DEC ]: ((('pk N × 'pk N) × 'c E) × 'n E) → 'm E *)
].


Definition hybrid (b : bool) (E : NBSES_scheme) (N : NIKE_scheme) (G : SGEN_scheme) : 
  module (I_GH_IN E N) (I_GH_OUT E N) := 
  [module GH_locs_tt E N ;
    #def #[ SET ] ('((PKs, PKr), k) : (('pk N × 'pk N) × 'shared_key G)) : ('unit) {
      #import {sig #[ HON ]: ('pk N × 'pk N) → 'option 'bool} as hon ;;
      #import {sig #[ GEN ]: 'unit → 'unit} as gen ;;
      #import {sig #[ SET ]: (('pk N × 'pk N) × 'fin #|N.(NIKE_scheme.Shared_Key)|) → 'unit  } as seti ;;
      hon_stat ← hon (PKs, PKr) ;; 
      
       HSLOC ← get HS_loc E N ;;

      if  (HSLOC (PKs, PKr) == None) then
        if (counter == i) then
             gen Datatypes.tt;;
             ret (Datatypes.tt : 'unit)
         else
             #put (HS_loc E N) := setm HSLOC (PKs, PKr) (counter) ;;
(*              counter := counter.+1 ;;  *)
             ret (Datatypes.tt : 'unit) 
      else
        (seti) (PKs, PKr) k ;; 

        ret (Datatypes.tt : 'unit)
    } (*;
    #def #[ CSET ] ('((PKr, PKs), k) : (('pk N × 'pk N) × 'k E) : ('unit) {
    
    } ;
    
    #def #[ ENC ] ('(((PKr, PKs), m), n) : (('pk N × 'pk N) × 'm E) × 'n E) : ('c E) {
      
    } ;  
    
    #def #[ DEC ] ('(((PKr, PKs), c), n) : (('pk N × 'pk N) × 'c E) × 'n E) : ('m E) {
      
      
    } *)

  ].


(*      #import {sig #[ GET ]: ('pk N × 'pk N) → ('fin #|E.(NBSES.Shared_Key)|) as geti ;;*)








(*
 *)




End GH.