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

Definition M_loc (E: NBSES_scheme) (pk : finType) `{Positive #|pk|} : Location := (chMap (('fin #|pk| × 'fin #|pk|) × 'n E) ('m E × 'c E); 0).

Definition AE_locs_tt (E: NBSES_scheme) (pk: finType) `{Positive #|pk|} := fset [::  M_loc E pk].
Definition AE_locs_ff (E: NBSES_scheme) (pk: finType) `{Positive #|pk|} := fset [::  M_loc E pk].

Definition GET := 1%N.
Definition HON := 2%N.

Definition ENC := 3%N.
Definition DEC := 4%N.

Definition I_AE_IN (E: NBSES_scheme) (pk : choice_type) :=
  [interface
    #val #[ GET ]: ('T pk × 'T pk) → 'k E ;
    #val #[ HON ]: ('T pk × 'T pk)  → 'bool 
].

Definition I_AE_OUT (E: NBSES_scheme) (pk: choice_type) :=
  [interface
    #val #[ ENC ]: ((('T pk × 'T pk) × 'm E) × 'n E) → 'c E ;
    #val #[ DEC ]: ((('T pk × 'T pk) × 'c E) × 'n E) → 'm E 
].

Definition AE (b : bool) (E: NBSES_scheme) (pk: finType) `{Positive #|pk|} :
  module (I_AE_IN E 'fin #|pk|) (I_AE_OUT E 'fin #|pk|)  := 
  [module AE_locs_tt E pk;
    #def #[ ENC ] ('(((PKr, PKs), m), n) : (('T 'fin #|pk| × 'T 'fin #|pk|) × 'm E) × 'n E) : ('c E) {
      #import {sig #[ GET ]: ('T 'fin #|pk| × 'T 'fin #|pk|) → 'k E } as geti ;;
      #import {sig #[ HON ]: ('T 'fin #|pk| × 'T 'fin #|pk|) → 'bool } as hon ;;
      
      k ← geti (PKr, PKs) ;;
      MLOC ← get M_loc E pk ;;
      HON ← hon (PKr, PKs) ;;

      #assert MLOC ((PKr, PKs), n) == None ;;

      if (b && HON) then
        c ← E.(sample_C) ;; 
        #put (M_loc E pk) := setm MLOC ((PKr, PKs), n) (m, c) ;;
        ret c
      else 
         c ← E.(enc) m k n ;;
         #put (M_loc E pk) := setm MLOC ((PKr, PKs), n) (m, c) ;;
          ret c 
    } ; 

    #def #[ DEC ] ('(((PKr, PKs), c), n) : (('T 'fin #|pk| × 'T 'fin #|pk|) × 'c E) × 'n E) : ('m E) {
      #import {sig #[ GET ]: ('T 'fin #|pk| × 'T 'fin #|pk|) → 'k E } as geti ;;
      #import {sig #[ HON ]: ('T 'fin #|pk| × 'T 'fin #|pk|) → 'bool } as hon ;;

      k ← geti (PKr, PKs) ;;
      MLOC ← get M_loc E pk;;
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