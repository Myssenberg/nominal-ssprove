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

Module SAE.

Definition SM_loc (E : NBSES_scheme) : Location := (chMap 'n E ('m E × 'c E) ; 0).
Definition SAEK_loc (E : NBSES_scheme) : Location := ('option 'k E ; 1).

Definition SAE_locs_tt (E : NBSES_scheme) := fset [::  SM_loc E ; SAEK_loc E]. (*If they're using the same loc, can they share then because Nom-SSP will rename or do we get into trouble?*)
Definition SAE_locs_ff (E : NBSES_scheme) := fset [::  SM_loc E ; SAEK_loc E]. (*If they're using the same loc, can they share then because Nom-SSP will rename or do we get into trouble?*)

Definition GEN := 2%N.
Definition SENC := 3%N.
Definition SDEC := 4%N.

Definition I_SAE_OUT (E : NBSES_scheme) :=
  [interface
    #val #[ GEN ]: 'unit → 'unit ;    
    #val #[ SENC ]: ('m E × 'n E) → 'c E  ;
    #val #[ SDEC ]: ('c E × 'n E) → 'm E 
].

Definition SAE (b : bool) (E : NBSES_scheme):
  game (I_SAE_OUT E)  := 
  [module SAE_locs_tt E ;
    #def #[ GEN ] (_ : 'unit) : ('unit) {
      KLOC ← get SAEK_loc E ;;
      match KLOC with
      | None =>
        k ← E.(sample_K) ;;
        #put (SAEK_loc E) := Some k ;;
        ret (Datatypes.tt : 'unit)
      | Some k => ret (Datatypes.tt : 'unit)
      end
    } ;
    #def #[ SENC ] ('(m, n) : ('m E × 'n E)) : ('c E) {
      SMLOC ← get SM_loc E ;;
      #assert SMLOC n == None ;;
      KLOC ← get SAEK_loc E ;;
      #assert isSome KLOC as someKey ;;
      let k := getSome KLOC someKey in
      if (b) then
       c ← E.(sample_C) ;;
       #put (SM_loc E) := setm SMLOC (n) (m, c) ;;
       ret c
      else
       c ← E.(enc) m k n ;;
       #put (SM_loc E) := setm SMLOC (n) (m, c) ;;
       ret c
    } ;
    #def #[ SDEC ] ('(c, n) : ('c E × 'n E)) : ('m E) {
      KLOC ← get SAEK_loc E ;;
      #assert (isSome KLOC) as someKey ;;
      let k := getSome KLOC someKey in
      if (b) then
       SMLOC ← get SM_loc E ;;
       #assert isSome (SMLOC n) as MC ;;
       let (m, c') := getSome (SMLOC n) MC in 
       ret m
      else
       m ← E.(dec) c k n ;;
       ret m
    }
  ].

End SAE.