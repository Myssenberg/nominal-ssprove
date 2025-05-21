(*This is a part of an implementation of the state-separated game-based proof of security for the NaCl crypto_box authenticated encryption scheme. This file contains the KEY package*)

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

From NominalSSP Require Import NIKE NBSES.

#[local] Open Scope package_scope.

Module KEY.

Import NIKE NBSES.

Definition SID_loc (N: NIKE_scheme) : Location := (chMap 'SID N 'bool ; 25).
Definition K_loc (N: NIKE_scheme) : Location := (chMap 'SID N 'shared_key N ; 26).
Definition HC_loc (N: NIKE_scheme) : Location := (chMap 'SID N 'nat; 58).


Definition SET := 27%N.
Definition CSET := 28%N.
Definition GET := 29%N.
Definition HON := 30%N.

Definition I_KEY_OUT (N: NIKE_scheme) :=
  [interface
    [ SET ]  : { ('SID N × 'shared_key N) ~> 'unit } ;
    [ CSET ] : { ('SID N × 'shared_key N) ~> 'unit } ;
    [ GET ]  : { 'SID N ~> 'shared_key N } ;
    [ HON ]  : { 'SID N ~> 'option 'bool }
].

Definition KEY (N: NIKE_scheme) qset (b : 'bool) :
  game (I_KEY_OUT N) :=
  [module fset [:: SID_loc N ; K_loc N ; HC_loc N];
    [ SET ]  : { ('SID N × 'shared_key N) ~> 'unit } '(sid, k) {
      KLOC ← get K_loc N ;;
      SIDLOC ← get SID_loc N ;;
      HCLOC ← get HC_loc N;;
      
      #assert isSome (HCLOC sid) as count ;;
      let counts := getSome (HCLOC sid) count in
      #assert (counts < qset) ;;
      #put (HC_loc N) := setm HCLOC sid (counts.+1) ;;

      if b then
        key ← N.(kdist) ;;
        #put (K_loc N) := @setm ('SID N : choiceType) _ KLOC sid key ;;
        ret (Datatypes.tt : 'unit)
      else
        #assert isSome (KLOC sid) as someKey ;;
        #put (SID_loc N) := @setm ('SID N : choiceType) _ SIDLOC sid true ;;
        #put (K_loc N) := setm KLOC sid k ;;
        ret (Datatypes.tt : 'unit)
    } ;

    [ CSET ] : { ('SID N × 'shared_key N) ~> 'unit } '(sid, k) { 
      KLOC ← get K_loc N ;;
      #assert isSome (KLOC sid) as someKey ;;
      SIDLOC ← get SID_loc N ;;
      #put (SID_loc N) := @setm ('SID N : choiceType) _ SIDLOC sid false ;;
      ret (Datatypes.tt : 'unit)
    } ;

    [ GET ]  : { 'SID N ~> 'shared_key N } (sid) {
      KLOC ← get K_loc N ;;
      #assert isSome (KLOC sid) as someKey ;;
      let key := getSome (KLOC sid) someKey in
      @ret ('shared_key N) key

    } ;

    [ HON ]  : { 'SID N ~> 'option 'bool } (sid) {
      SIDLOC ← get SID_loc N;;
      #assert isSome (SIDLOC sid) as someBool ;;
      @ret ('option 'bool) (Some(getSome (SIDLOC sid) someBool))

    }
  ].

End KEY.
