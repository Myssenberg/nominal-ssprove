(*This is a part of the implementation of the state-separated proof of security for the NaCl crypto_box public-key authenticated encryption scheme.
This file contains the specification for the PKAE module.*)

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

From NominalSSP Require Import Prelude Group NBPES.
Import PackageNotation.
Import NBPES.

Module PKAE.

#[local] Open Scope package_scope.

Notation " 'F c " := 'fin #|c| (in custom pack_type at level 2, c constr at level 20).
Notation " 'F c " := 'fin #|c| (at level 2): package_scope.

Notation " 'SID n " := ('fin #|PK n| × 'fin #|PK n|) (in custom pack_type at level 2, n constr at level 20).
Notation " 'SID n " := ('fin #|PK n| × 'fin #|PK n|) (at level 2): package_scope.


Definition PK_loc (P : NBPES_scheme): Location := (chMap 'pk P 'bool ; 8).

Definition SK_loc (P : NBPES_scheme): Location := (chMap 'pk P 'sk P ; 9).

Definition M_loc (P: NBPES_scheme): Location := (chMap ('SID P × 'n P) (M P × C P) ; 10). 


Definition GETSK := 4%N.
Definition HONPK := 5%N.

Definition PKENC := 14%N.
Definition PKDEC := 15%N.


Definition I_PKAE_IN (P: NBPES_scheme) :=
  [interface
    [ GETSK ] : { 'pk P ~> 'sk P } ;  
    [ HONPK ] : { 'pk P ~> 'bool }
].

Definition I_PKAE_OUT (P: NBPES_scheme) :=
  [interface
    [ PKENC ] : { ((('pk P × 'pk P) × M P) × 'n P) ~> C P } ;
    [ PKDEC ] : { ((('pk P × 'pk P) × C P) × 'n P) ~> M P }
].


Definition SORT (P: NBPES_scheme) (PKs PKr : 'pk P) : 'SID P :=
  if (PKs < PKr) then (PKs, PKr) : (prod _ _) else (PKr, PKs) : (prod _ _).


Definition PKAE (P: NBPES_scheme) (b : bool):
  module (I_PKAE_IN P) (I_PKAE_OUT P)  := 
  [module fset [:: PK_loc P ; SK_loc P ; M_loc P] ;
    [ PKENC ] : { ((('pk P × 'pk P) × M P) × 'n P) ~> C P } '(((PKs, PKr), m), n) { 
      let getsk := #import [ GETSK ] : { 'pk P ~> 'sk P } in
      let honpk := #import [ HONPK ] : { 'pk P ~> 'bool } in

      SKs ← getsk PKs ;;
      HONpkr ← honpk PKr ;;
      let sid := SORT P PKs PKr in
      MLOC ← get M_loc P ;;
      #assert MLOC (sid, n) == None ;;
      if (b && HONpkr) then
        c ← P.(sample_C) ;;        
        #put (M_loc P) := setm MLOC (sid, n) (m, c) ;;
        ret c
      else
        c ← P.(enc) SKs PKr m n ;;
        #put (M_loc P) := setm MLOC (sid, n) (m, c) ;;
        ret c
    } ;
    [ PKDEC ] : { ((('pk P × 'pk P) × C P) × 'n P) ~> M P } '(((PKr, PKs), c), n) { 
      let getsk := #import [ GETSK ] : { 'pk P ~> 'sk P } in
      let honpk := #import [ HONPK ] : { 'pk P ~> 'bool } in
      SKr ← getsk PKr ;;
      HONpks ← honpk PKs ;;
      if (b && HONpks) then
        let sid := SORT P PKs PKr in
        MLOC ← get M_loc P ;;        
        #assert isSome (MLOC (sid, n)) as MC ;;
        let (m, c') := getSome (MLOC (sid, n)) MC in
        ret m
      else
        m ← P.(dec) SKr PKs c n ;;
        ret m
    }
  ].

End PKAE.
