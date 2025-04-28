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

From NominalSSP Require Import SAE KEY NBSES NIKE AE.

Import SAE KEY NBSES NIKE_scheme AE.

Module HYBRID.

Notation " 'T c " := (c) (in custom pack_type at level 2, c constr at level 20).
Notation " 'T c " := (c) (at level 2): package_scope.


Variable (i : 'nat).

Definition HS_loc (E: NBSES_scheme) (N : NIKE_scheme) : Location := (chMap ('pk N × 'pk N) 'nat; 31). (*Check loc here*)


(*Definition SET := 27%N.
Definition CSET := 28%N.*)
Definition ENC := 52%N.
Definition DEC := 53%N.
Definition GET := 29%N.
Definition HON := 30%N.


Definition GH_locs_tt (E: NBSES_scheme) (N : NIKE_scheme) := fset [::  HS_loc E N ].
Definition GH_locs_ff (E: NBSES_scheme) (N : NIKE_scheme) := fset [::  HS_loc E N ].

(*

Definition I_GH_IN (E: NBSES_scheme) (N : NIKE_scheme) := I_GSAE_OUT E :|: I_KEY_OUT N (NIKE_to_SGEN N) :|: I_AE_OUT E N.
*)

Definition I_GH_IN (E: NBSES_scheme) (N : NIKE_scheme) :=
  [interface
    #val #[ SET ]:  ('SID N × 'fin #|N.(NIKE_scheme.Shared_Key)|) → 'unit ; 
    #val #[ CSET ]: ('SID N × 'fin #|N.(NIKE_scheme.Shared_Key)|) → 'unit ;
    #val #[ HON ]: ('pk N × 'pk N) → ('option 'bool) ; (*Allowed?*)
    #val #[ ENC ]: ((('pk N × 'pk N) × 'm E) × 'n E) → 'c E ;
    #val #[ DEC ]: ((('pk N × 'pk N) × 'c E) × 'n E) → 'm E ;
    #val #[ GEN ]: 'unit → 'unit ;    
    #val #[ ENC ]: ('m E × 'n E) → 'c E  ;
    #val #[ DEC ]: ('c E × 'n E) → 'm E 
].

Definition I_GH_OUT (E: NBSES_scheme) (N : NIKE_scheme) :=
  [interface
    #val #[ SET ]: (('pk N × 'pk N) × 'fin #|N.(NIKE_scheme.Shared_Key)|) → 'unit  ;
    #val #[ CSET ]: (('pk N × 'pk N) × 'fin #|N.(NIKE_scheme.Shared_Key)|) → 'unit (*;
    #val #[ ENC ]: ((('pk N × 'pk N) × 'm E) × 'n E) → 'c E ;
    #val #[ DEC ]: ((('pk N × 'pk N) × 'c E) × 'n E) → 'm E *)
].


Definition HYBRID (b : bool) (E : NBSES_scheme) (N : NIKE_scheme) : 
  module (I_GH_IN E N) (I_GH_OUT E N) := 
  [module GH_locs_tt E N ;
    #def #[ SET ] ('((PKs, PKr), k) : (('pk N × 'pk N) × 'fin #|N.(NIKE_scheme.Shared_Key)|)) : ('unit) {
      #import {sig #[ HON ]: ('pk N × 'pk N) → 'option 'bool} as hon ;;
      #import {sig #[ GEN ]: 'unit → 'unit} as gen ;;
      #import {sig #[ SET ]: (('pk N × 'pk N) × 'fin #|N.(NIKE_scheme.Shared_Key)|) → 'unit  } as set ;;
      hon_stat ← hon (PKs, PKr) ;;
      HSLOC ← get HS_loc E N ;;
      #assert isSome (HSLOC (PKs, PKr)) as count ;;
      let counts := getSome (HSLOC (PKs, PKr)) count in
      if (HSLOC (PKs, PKr) == None) then  
        if (counts == i) then
          gen Datatypes.tt ;;
          #put (HS_loc E N) := setm HSLOC (PKs, PKr) (counts.+1) ;; (*Double check that this is correct*)
          set (PKs, PKr, k) ;;
          ret (Datatypes.tt : 'unit)
        else
          #put (HS_loc E N) := setm HSLOC (PKs, PKr) (counts.+1) ;;          
          set (PKs, PKr, k) ;;          
          ret (Datatypes.tt : 'unit)
      else
        set (PKs, PKr, k) ;;
        ret (Datatypes.tt : 'unit)
    } ;
    #def #[ CSET ] ('((PKr, PKs), k) : (('pk N × 'pk N) × 'fin #|N.(NIKE_scheme.Shared_Key)|)) : ('unit) {
      #import {sig #[ CSET ]: (('pk N × 'pk N) × 'fin #|N.(NIKE_scheme.Shared_Key)|) → 'unit  } as cset ;;
      cset (PKr, PKs, k) ;;
      ret (Datatypes.tt : 'unit)
    } (*;
    
    #def #[ ENC ] ('(((PKr, PKs), m), n) : (('pk N × 'pk N) × 'm E) × 'n E) : ('c E) {
      HSLOC ← get HS_loc E N ;; 
      #assert isSome (HSLOC (PKs, PKr)) as count ;;
      let counts := getSome (HSLOC (PKs, 
    } ;  
    
    #def #[ DEC ] ('(((PKr, PKs), c), n) : (('pk N × 'pk N) × 'c E) × 'n E) : ('m E) {
      
      
    } *)

  ].

End HYBRID.