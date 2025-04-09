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

From NominalSSP Require Import Prelude Group Misc.
Import PackageNotation.

From NominalSSP Require Import NIKE.

#[local] Open Scope package_scope.

Module KEY.

Import NIKE_scheme.

Definition SID_loc (N: NIKE_scheme) : Location := (chMap 'SID N 'bool ; 25).
Definition K_loc (N: NIKE_scheme) : Location := (chMap 'SID N 'shared_key N ; 26).

Definition KEY_locs_tt (N: NIKE_scheme) := fset [:: SID_loc N ; K_loc N].  
Definition KEY_locs_ff (N: NIKE_scheme) := fset [:: SID_loc N ; K_loc N].

Definition SET := 27%N.
Definition CSET := 28%N.
Definition GET := 29%N.
Definition HON := 30%N.

Definition I_KEY_OUT (N: NIKE_scheme) :=
  [interface
    #val #[ SET ]:  ('SID N × 'shared_key N) → 'unit ;
    #val #[ CSET ]: ('SID N × 'shared_key N) → 'unit ;
    #val #[ GET ]:  'SID N → 'shared_key N ;
    #val #[ HON ]:  'SID N → 'bool
].

Definition KEY b (N: NIKE_scheme):
  game (I_KEY_OUT N) :=
  [module KEY_locs_tt N ;
    #def #[ SET ] ('(sid, k) : 'SID N × 'shared_key N): ('unit) {
      KLOC ← get K_loc N ;;
      SIDLOC ← get SID_loc N ;;

      if b then
        key ← N.(kdist) ;;
        #put (K_loc N) := @setm ('SID N : choiceType) _ KLOC sid key ;;(*This needs to put a uniformly chosen key*)
        ret (Datatypes.tt : 'unit)
      else
        #assert isSome (KLOC sid) as someKey ;;
        #put (SID_loc N) := @setm ('SID N : choiceType) _ SIDLOC sid true ;;
        #put (K_loc N) := setm KLOC sid k ;;
        ret (Datatypes.tt : 'unit)
    } ;

    #def #[ CSET ] ('(sid, k) : 'SID N × 'shared_key N): ('unit) {
      KLOC ← get K_loc N ;;
      #assert isSome (KLOC sid) as someKey ;;
      SIDLOC ← get SID_loc N ;;
      #put (SID_loc N) := @setm ('SID N : choiceType) _ SIDLOC sid false ;;
      ret (Datatypes.tt : 'unit)
    } ;

    #def #[ GET ] (sid : 'SID N): ('shared_key N) {
      KLOC ← get K_loc N;;
      #assert isSome (KLOC sid) as someKey ;;
      let key := getSome (KLOC sid) someKey in
      @ret ('shared_key N) key

    } ;

    #def #[ HON ] (sid : 'SID N): ('bool) {
      SIDLOC ← get SID_loc N;;
      #assert isSome (SIDLOC sid) as someBool ;;
      let bool := getSome (SIDLOC sid) someBool in
      @ret ('bool) bool

    }
  ].

(*

Definition chSet t := chMap t 'unit.

Notation " 'set t " := (chSet t) (in custom pack_type at level 2).
Notation " 'set t " := (chSet t) (at level 2): package_scope.

(*The SessionID will just be represented by a pair of sender and receiver public keys: (pks, pkr)*)

Definition SID_loc (pks pkr : finType) `{Positive #|pks|} `{Positive #|pkr|} : Location := (chMap ('fin #|pks| × 'fin #|pkr|) 'bool ; 8).
Definition K_loc (pks pkr shared_key : finType) `{Positive #|pks|} `{Positive #|pkr|} `{Positive #|shared_key|} : Location := (chMap ('fin #|pks| × 'fin #|pkr|) 'fin #|shared_key| ; 9).

Definition KEY_locs_tt (pks pkr shared_key : finType) `{Positive #|pks|} `{Positive #|pkr|} `{Positive #|shared_key|} := fset [:: SID_loc pks pkr ; K_loc pks pkr shared_key].  
Definition KEY_locs_ff (pks pkr shared_key : finType) `{Positive #|pks|} `{Positive #|pkr|} `{Positive #|shared_key|} := fset [:: SID_loc pks pkr ; K_loc pks pkr shared_key].

Notation " 'T c " := (c) (in custom pack_type at level 2, c constr at level 20).
Notation " 'T c " := (c) (at level 2): package_scope.

Definition SET := 10%N.
Definition CSET := 11%N.
Definition GET := 12%N.
Definition HON := 13%N.


Definition I_KEY_OUT (pks pkr shared_key : choice_type):=
  [interface
    #val #[ SET ]:  'T ((pks × pkr ) × shared_key) → 'unit ;
    #val #[ CSET ]: 'T ((pks × pkr ) × shared_key) → 'unit ;
    #val #[ GET ]:  'T (pks × pkr ) → 'T shared_key ;
    #val #[ HON ]:  'T (pks × pkr ) → 'bool
].



Definition KEY (b : bool) (pks pkr shared_key : finType) `{Positive #|pks|} `{Positive #|pkr|} `{Positive #|shared_key|} (kdist : 
      code fset0 [interface] 'fin #|shared_key|):
  game (I_KEY_OUT 'fin #|pks| 'fin #|pkr| 'fin #|shared_key|) :=
  [module KEY_locs_tt pks pkr shared_key ;
    #def #[ SET ] ('((pks', pkr'), shared_key') : 'T ( ('fin #|pks| × 'fin #|pkr|) × 'fin #|shared_key|)): ('unit) {
      KLOC ← get K_loc pks pkr shared_key ;;
      SIDLOC ← get SID_loc pks pkr ;;

      if b then
        shared_key'' ← kdist ;;
        #put (K_loc pks pkr shared_key) := setm KLOC (pks', pkr') shared_key'' ;;(*This needs to put a uniformly chosen key*)
        ret (Datatypes.tt : 'unit)
      else
        #assert isSome (KLOC (pks', pkr')) as someKey ;;
        #put (SID_loc pks pkr) := setm SIDLOC (pks', pkr') true ;;
        #put (K_loc pks pkr shared_key) := setm KLOC (pks', pkr') shared_key' ;;
        ret (Datatypes.tt : 'unit)
    } ;

    #def #[ CSET ] ('((pks', pkr'), shared_key') : 'T (('fin #|pks| × 'fin #|pkr|) × 'fin #|shared_key|)): ('unit) {
      KLOC ← get K_loc pks pkr shared_key ;;
      #assert isSome (KLOC (pks', pkr')) as someKey ;;
      SIDLOC ← get SID_loc pks pkr ;;
      #put (SID_loc pks pkr) := setm SIDLOC (pks', pkr') false ;;
      ret (Datatypes.tt : 'unit)
    } ;

    #def #[ GET ] ('(pks', pkr') : 'T ('fin #|pks| × 'fin #|pkr|)): ('T 'fin #|shared_key|) {
      KLOC ← get K_loc pks pkr shared_key ;;
      #assert isSome (KLOC (pks', pkr')) as someKey ;;
      let shared_key' := getSome (KLOC (pks', pkr')) someKey in
      @ret ('T 'fin #|shared_key|) shared_key'

    } ;

    #def #[ HON ] ('(pks', pkr') : 'T ('fin #|pks| × 'fin #|pkr|)): ('bool) {
      SIDLOC ← get SID_loc pks pkr ;;
      #assert isSome (SIDLOC (pks', pkr')) as someBool ;;
      let b := getSome (SIDLOC (pks', pkr')) someBool in
      @ret ('bool) b

    }
  ].
*)

End KEY.
