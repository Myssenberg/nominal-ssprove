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

From NominalSSP Require Import Prelude Group NBPES.
Import PackageNotation.
Import NBPES.

Module PKAE.

#[local] Open Scope package_scope.

Notation " 'F c " := 'fin #|c| (in custom pack_type at level 2, c constr at level 20).
Notation " 'F c " := 'fin #|c| (at level 2): package_scope.

Definition h (E: NBPES_scheme) : choice_type := ('pk E × 'pk E).


Definition PK_loc (E : NBPES_scheme): Location := (chMap 'pk E 'bool ; 8).

Definition SK_loc (E : NBPES_scheme): Location := (chMap 'pk E 'sk E ; 9).

Definition M_loc (E: NBPES_scheme): Location := (chMap (h E × 'n E) (M E × C E) ; 10). 


Definition PKAE_locs_tt (E : NBPES_scheme):= fset [:: PK_loc E ; SK_loc E ; M_loc E]. (*If they're using the same loc, can they share then because Nom-SSP will rename or do we get into trouble?*)
Definition PKAE_locs_ff (E : NBPES_scheme):= fset [:: PK_loc E ; SK_loc E ; M_loc E].

Definition GETSK := 4%N.
Definition HONPK := 5%N.

Definition PKENC := 14%N.
Definition PKDEC := 15%N.


Definition I_PKAE_IN (E: NBPES_scheme) :=
  [interface
    [ GETSK ] : { 'pk E ~> 'sk E } ;  
    [ HONPK ] : { 'pk E ~> 'bool }
].

Definition I_PKAE_OUT (E: NBPES_scheme) :=
  [interface
    [ PKENC ] : { ((('pk E × 'pk E) × M E) × 'n E) ~> C E } ;
    [ PKDEC ] : { ((('pk E × 'pk E) × C E) × 'n E) ~> M E }
].


Definition SORT (E: NBPES_scheme) (PKs PKr : 'pk E) : h E :=
  if (PKs < PKr) then (PKs, PKr) : (prod _ _) else (PKr, PKs) : (prod _ _).


Definition PKAE (E: NBPES_scheme) (b : bool):
  module (I_PKAE_IN E) (I_PKAE_OUT E)  := 
  [module PKAE_locs_tt E ;
    [ PKENC ] : { ((('pk E × 'pk E) × M E) × 'n E) ~> C E } '(((PKs, PKr), m), n) { 
      let getsk := #import [ GETSK ] : { 'pk E ~> 'sk E } in
      let honpk := #import [ HONPK ] : { 'pk E ~> 'bool } in

      SKs ← getsk PKs ;;
      HONpkr ← honpk PKr ;;
      let h := SORT E PKs PKr in
      MLOC ← get M_loc E ;;
      #assert MLOC (h, n) == None ;;
      if (b && HONpkr) then
        c ← E.(sample_C) ;;        
        #put (M_loc E) := setm MLOC (h, n) (m, c) ;;
        ret c
      else
        c ← E.(enc) SKs PKr m n ;;
        #put (M_loc E) := setm MLOC (h, n) (m, c) ;;
        ret c
    } ;
    [ PKDEC ] : { ((('pk E × 'pk E) × C E) × 'n E) ~> M E } '(((PKr, PKs), c), n) { 
      let getsk := #import [ GETSK ] : { 'pk E ~> 'sk E } in
      let honpk := #import [ HONPK ] : { 'pk E ~> 'bool } in
      SKr ← getsk PKr ;;
      HONpks ← honpk PKs ;;
      if (b && HONpks) then
        let h := SORT E PKs PKr in
        MLOC ← get M_loc E ;;        
        #assert isSome (MLOC (h, n)) as MC ;;
        let (m, c') := getSome (MLOC (h, n)) MC in
        ret m
      else
        m ← E.(dec) SKr PKs c n ;;
        ret m
    }
  ].

End PKAE.
