(*This is a part of the implementation of the state-separated game-based proof of security for the NaCl crypto_box authenticated encryption scheme.
This file contains the specification for a NIKE scheme*)

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

Module NIKE_scheme.

Record NIKE_scheme :=
  { PK             : finType ;
    PK_pos         : Positive #|PK|;
    SK             : finType ;
    SK_pos         : Positive #|SK|;
    Shared_Key     : finType ;
    Shared_Key_pos : Positive #|Shared_Key|;

    pkgen : 
      code fset0 [interface] ('fin #|PK| × 'fin #|SK|) ;

    sharedkey : forall (pk : 'fin #|PK|) (sk : 'fin #|SK|),
      code fset0 [interface] ('fin #|Shared_Key|) ;
    
    kdist : 
      code fset0 [interface] 'fin #|Shared_Key| ;
(*thinking kdist should return a value the same type as a shared key, as it's sampling a value uniformly to look like the shared key in the ideal version*)
  }.

Notation " 'pk n " := ('fin #|PK n|)
  (in custom pack_type at level 2, n constr at level 20).

Notation " 'pk n " := ('fin #|PK n|)
  (at level 3) : package_scope.

Notation " 'sk n " := ('fin #|SK n|)
  (in custom pack_type at level 2, n constr at level 20).

Notation " 'sk n " := ('fin #|SK n|)
  (at level 3) : package_scope.

Notation " 'shared_key n " := ('fin #|Shared_Key n|)
  (in custom pack_type at level 2, n constr at level 20).

Notation " 'shared_key n " := ('fin #|Shared_Key n|)
  (at level 3) : package_scope.


Instance pk_posi n : Positive #|PK n|.
Proof.
apply PK_pos. Defined.

Instance sk_posi n : Positive #|SK n|.
Proof.
apply SK_pos. Defined.

Instance sharedkey_posi n : Positive #|Shared_Key n|.
Proof.
apply Shared_Key_pos. Defined.



Definition PK_loc (N : NIKE_scheme): Location := (chMap 'pk N 'bool ; 0).

Definition SK_loc (N : NIKE_scheme): Location := (chMap 'pk N 'sk N ; 1).


Definition NIKE_locs_tt (N : NIKE_scheme):= fset [:: PK_loc N ; SK_loc N]. (*If they're using the same loc, can they share then because Nom-SSP will rename or do we get into trouble?*)
Definition NIKE_locs_ff (N : NIKE_scheme):= fset [:: PK_loc N ; SK_loc N].


Definition GETSK := 2%N.
Definition HONPK := 3%N.
Definition SET := 4%N.
Definition CSET := 5%N.
Definition SHAREDKEY := 6%N.


Definition I_NIKE_IN (N: NIKE_scheme) :=
  [interface
    #val #[ GETSK ]: 'pk N → 'sk N (*;
    #val #[ HONPK ]: 'pk N → 'bool (*lacks the SET and CSET from the KEY package*)*)
].

Definition I_NIKE_OUT (N: NIKE_scheme) :=
  [interface
    #val #[ SHAREDKEY ]: ('pk N × 'sk N) → 'shared_key N
].

Definition NIKE (N : NIKE_scheme):
  game (*(I_NIKE_IN N) *)(I_NIKE_OUT N) :=
  [module no_locs ; 
    #def #[ SHAREDKEY ] ('(pk, sk) : 'pk N × 'sk N ) : ('shared_key N) {
      (*#import {sig #[ GETSK ]: 'pk N → 'sk N } as getsk ;;
      ski ← getsk pk ;;*)
      shared_key ← N.(sharedkey) pk sk ;;
      ret shared_key
    }
  ].





Definition NIKE (N : NIKE_scheme):
  game (I_NIKE_IN N) (I_NIKE_OUT N) :=
  [module no_locs ; 
    #def #[ GETSK ] (pk : 'pk N): ('sk N) {
      #import {sig #[ GETSK ]: 'pk N → 'sk N } as getsk ;;
      sk ← getsk pk ;;
      ret sk
    } ;
    
    #def #[ SHAREDKEY ] (pk : 'pk N, sk : 'sk N) : ('shared_key N) {
      shared_key ← N.(sharedkey) pk sk ;;
      ret shared_key
    }
  ].


Definition I_GNIKE (N: NIKE_scheme) :=
  [interface
    #val #[ PKGEN ]: 'unit → ('pk N × 'sk N) ;
    #val #[ SHAREDKEY ]: ('pk N × 'sk N) → 'shared_key N
].


Definition GNIKE (N: NIKE_scheme) (b : 'bool) :
  game (I_GNIKE N) := .


End NIKE_scheme.