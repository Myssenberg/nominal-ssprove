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

Import NBSES NIKE.

Module AE.

Notation " 'F c " := 'fin #|c| (in custom pack_type at level 2, c constr at level 20).
Notation " 'F c " := 'fin #|c| (at level 2): package_scope.

Definition M_loc (E: NBSES_scheme) (N : NIKE_scheme) : Location := (chMap (('pk N × 'pk N) × 'n E) (M E × C E); 54).


Definition GET := 29%N.
Definition HON := 30%N.
Definition ENC := 52%N.
Definition DEC := 53%N.


Definition I_AE_IN (N : NIKE_scheme) :=
  [interface
    [ GET ] : { 'pk N × 'pk N ~> 'shared_key N } ;
    [ HON ] : { 'pk N × 'pk N ~> 'option 'bool }
].

Definition I_AE_OUT (E: NBSES_scheme) (N : NIKE_scheme) :=
  [interface
    [ ENC ] : { ((('pk N × 'pk N) × M E) × 'n E) ~> C E } ;
    [ DEC ] : { ((('pk N × 'pk N) × C E) × 'n E) ~> M E }
].


Definition AE (E: NBSES_scheme) (N : NIKE_scheme) (I : NIKE.inj ('F N.(NIKE.Shared_Key)) ('F (E.(NBSES.Shared_Key)))) (b : bool) :
  module (I_AE_IN N) (I_AE_OUT E N) := 
  [module fset [::  M_loc E N];
    [ ENC ] : { ((('pk N × 'pk N) × M E) × 'n E) ~> C E } '(((PKr, PKs), m), n) {
      let geti := #import [ GET ] : { 'pk N × 'pk N ~> 'shared_key N } in
      let hon  := #import [ HON ] : { 'pk N × 'pk N ~> 'option 'bool } in
      
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

    [ DEC ] : { ((('pk N × 'pk N) × C E) × 'n E) ~> M E } '(((PKr, PKs), c), n) { 
      let geti := #import [ GET ] : { 'pk N × 'pk N ~> 'shared_key N } in
      let hon  := #import [ HON ] : { 'pk N × 'pk N ~> 'option 'bool } in

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