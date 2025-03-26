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

Module KEY.

Variable (n: nat).

Definition Big_N: nat := 2^n.
Definition Key: choice_type := chFin (mkpos Big_N).
Definition PK: choice_type := chFin (mkpos Big_N).
Definition SessionID : choice_type := (PK × PK).
(*Definition kdist : code fset0 [interface] Key.*)


Notation " 'key " := (Key) (in custom pack_type at level 2).
Notation " 'key " := (Key) (at level 2): package_scope.

Notation " 'pk " := (PK) (in custom pack_type at level 2).
Notation " 'pk " := (PK) (at level 2): package_scope.

Notation " 'SID " := (SessionID) (in custom pack_type at level 2).
Notation " 'SID " := (SessionID) (at level 2): package_scope.

Definition SID_loc : Location := (chMap 'SID 'bool ; 0).
Definition K_loc : Location := (chMap 'SID 'key ; 1).

Definition KEY_locs_tt := fset [:: SID_loc ; K_loc].  
Definition KEY_locs_ff := fset [:: SID_loc ; K_loc].

Definition SET := 2%N.
Definition CSET := 3%N.
Definition GET := 4%N.
Definition HON := 5%N.

(*Definition kdist := {code 
                      key ← sample uniform #|el| ;;   
                      ret ('key)}. *)

Definition I_KEY_OUT :=
  [interface
    #val #[ SET ]:  ('SID × 'key) → 'unit ;
    #val #[ CSET ]: ('SID × 'key) → 'unit ;
    #val #[ GET ]:  ('SID) → 'key ;
    #val #[ HON ]:  ('SID) → 'bool
].

Notation "'getNone' n ;; c" :=
  ( v ← get n ;;
    #assert (v == None) ;;
    c
  )
  (at level 100, n at next level, right associativity,
  format "getNone  n  ;;  '//' c")
  : package_scope.

Notation "x ← 'getSome' n ;; c" :=
  ( v ← get n ;;
    #assert (isSome v) as vSome ;;
    let x := getSome v vSome in
    c
  )
  (at level 100, n at next level, right associativity,
  format "x  ←  getSome  n  ;;  '//' c")
  : package_scope.

Definition KEY0:
  game (I_KEY_OUT) :=
  [module KEY_locs_tt ;
    #def #[ SET ] ('(SID, k) : 'SID × 'key): ('unit) {
      KLOC ← get K_loc ;;
      #assert isSome (KLOC SID) as someKey ;;
      SIDLOC ← get SID_loc ;;
      #put (SID_loc) := @setm ('SID : choiceType) _ SIDLOC SID true ;;
      #put (K_loc) := setm KLOC SID k ;;
      ret (Datatypes.tt : 'unit)
    } ;

    #def #[ CSET ] ('(SID, k) : 'SID × 'key): ('unit) {
      KLOC ← get K_loc ;;
      #assert isSome (KLOC SID) as someKey ;;
      SIDLOC ← get SID_loc ;;
      #put (SID_loc) := @setm ('SID : choiceType) _ SIDLOC SID false ;;
      ret (Datatypes.tt : 'unit)
    } ;

    #def #[ GET ] (SID : 'SID): ('key) {
      KLOC ← get K_loc ;;
      #assert isSome (KLOC SID) as someKey ;;
      let key := getSome (KLOC SID) someKey in
      @ret ('key) key

    } ;

    #def #[ HON ] (SID : 'SID): ('bool) {
      SIDLOC ← get SID_loc ;;
      #assert isSome (SIDLOC SID) as someBool ;;
      let bool := getSome (SIDLOC SID) someBool in
      @ret ('bool) bool

    }

  ].

Definition KEY1:
  game (I_KEY_OUT) :=
  [module KEY_locs_tt ;
    #def #[ SET ] ('(SID, k) : 'SID × 'key): ('unit) {
      KLOC ← get K_loc ;;
      #assert isSome (KLOC SID) as someKey ;;
      SIDLOC ← get SID_loc ;;
      #put (SID_loc) := @setm ('SID : choiceType) _ SIDLOC SID true ;;
      
      (*key ← kdist ;;
      #put (K_loc) := setm KLOC SID key ;; *)(*This needs to put a uniformly chosen key*)
      ret (Datatypes.tt : 'unit)
    } ;

    #def #[ CSET ] ('(SID, k) : 'SID × 'key): ('unit) {
      KLOC ← get K_loc ;;
      #assert isSome (KLOC SID) as someKey ;;
      SIDLOC ← get SID_loc ;;
      #put (SID_loc) := @setm ('SID : choiceType) _ SIDLOC SID false ;;
      ret (Datatypes.tt : 'unit)
    } ;

    #def #[ GET ] (SID : 'SID): ('key) {
      KLOC ← get K_loc ;;
      #assert isSome (KLOC SID) as someKey ;;
      let key := getSome (KLOC SID) someKey in
      @ret ('key) key

    } ;

    #def #[ HON ] (SID : 'SID): ('bool) {
      SIDLOC ← get SID_loc ;;
      #assert isSome (SIDLOC SID) as someBool ;;
      let bool := getSome (SIDLOC SID) someBool in
      @ret ('bool) bool

    }

  ].


End KEY.