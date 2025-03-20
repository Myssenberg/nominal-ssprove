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



Instance pk_posi p : Positive #|PK p|.
Proof.
apply PK_pos. Defined.

Instance sk_posi p : Positive #|SK p|.
Proof.
apply SK_pos. Defined.

Definition chSet t := chMap t 'unit.

Notation " 'set t " := (chSet t) (in custom pack_type at level 2).
Notation " 'set t " := (chSet t) (at level 2): package_scope.

Definition h : choice_type := ('set ('pk × 'pk)).
Definition key : choice_type := ().

Definition K_loc : Location := (chMap 'key E 'bool ; 0). (*How to define the key?*)




Definition KEY_locs_tt := fset [:: K_loc ].  
Definition KEY_locs_ff := fset [:: K_loc ].

Definition SET := 2%N.
Definition GET := 4%N.
Definition HON := 5%N.
Definition CSET := 6%N.



Definition I_KEY_OUT :=
  [interface
    #val #[ SET ]:  (h × key) → 'unit ;
    #val #[ GET ]:  (h × key) → 'unit ;
    #val #[ HON ]:  (h) → 'unit ;(*key option*)
    #val #[ CSET ]: (h) → 'unit  (*bool option*)

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

Definition KEY:
  module (I_KEY_OUT)  := 
  [module KEY_locs_tt E ;
    #def #[ SET ] ('(h, key): 'h  × key) : 'bool {
     
    }
  ].




End KEY.