(*This is a part of the implementation of the state-separated proof of security for the NaCl crypto_box public-key authenticated encryption scheme.
This file contains the specification for the SAE module.*)

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

From NominalSSP Require Import NBSES.

Import NBSES.

Module SAE.

Definition SM_loc (E : NBSES_scheme) : Location := (chMap 'n E (M E × C E) ; 0).
Definition SAEK_loc (E : NBSES_scheme) : Location := ('option 'k E ; 1).

Definition GEN := 2%N.
Definition SENC := 3%N.
Definition SDEC := 4%N.

Definition I_SAE_OUT (E : NBSES_scheme) :=
  [interface
    [ GEN ]  : { 'unit ~> 'unit } ;    
    [ SENC ] : { (M E × 'n E) ~> C E } ;
    [ SDEC ] : { (C E × 'n E) ~> M E }
].

Definition SAE (E : NBSES_scheme) (b : 'bool) :
  game (I_SAE_OUT E)  := 
  [module fset [::  SM_loc E ; SAEK_loc E] ;
    [ GEN ]  : { 'unit ~> 'unit } '_ {
      KLOC ← get SAEK_loc E ;;
      match KLOC with
      | None =>
        k ← E.(sample_K) ;;
        #put (SAEK_loc E) := Some k ;;
        ret (Datatypes.tt : 'unit)
      | Some k => ret (Datatypes.tt : 'unit)
      end
    } ;
    [ SENC ] : { (M E × 'n E) ~> C E } '(m, n) {
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
    [ SDEC ] : { (C E × 'n E) ~> M E } '(c, n) { 
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