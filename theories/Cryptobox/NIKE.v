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

    sharedkey : forall (pk : 'fin #|PK|) (sk : 'fin #|SK|), (*unsure here whether this is supposed to make the shared key from two public keys or a public and a secret, from the sender and receiver, respectively*)
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


Notation " 'SID n " := ('fin #|PK n| × 'fin #|PK n|) (in custom pack_type at level 2, n constr at level 20).
Notation " 'SID n " := ('fin #|PK n| × 'fin #|PK n|) (at level 2): package_scope.


Definition GETSK := 4%N.
Definition HONPK := 5%N.
Definition SET := 6%N.
Definition CSET := 7%N.
Definition SHAREDKEY := 8%N.

Definition I_NIKE_IN (N: NIKE_scheme) :=
  [interface
    #val #[ GETSK ]: 'pk N → 'sk N ;
    #val #[ HONPK ]: 'pk N → 'bool ;
    #val #[ SET ]:   ('SID N × 'shared_key N) → 'unit ;
(*if this is from KEY taking a SID, do we then have to define the type SID separately here?*)
    #val #[ CSET ]: ('SID N × 'shared_key N) → 'unit
].

Definition I_NIKE_OUT (N: NIKE_scheme) :=
  [interface
    #val #[ SHAREDKEY ]: ('pk N × 'pk N) → 'unit
].

Definition NIKE (N : NIKE_scheme):
  module (I_NIKE_IN N) (I_NIKE_OUT N) :=
  [module no_locs ; 
    #def #[ SHAREDKEY ] ('(pks, pkr) : 'pk N × 'pk N ) : 'unit {
      #import {sig #[ HONPK ]: 'pk N → 'bool } as honpk ;;
      #import {sig #[ GETSK ]: 'pk N → 'sk N } as getsk ;;
      #import {sig #[ SET ]: (('pk N × 'pk N) × 'shared_key N) → 'unit} as set ;;
      #import {sig #[ CSET ]: (('pk N × 'pk N) × 'shared_key N) → 'unit} as cset ;;
      hs ← honpk pks ;;
      hr ← honpk pkr ;;
      
      sks ← getsk pks ;;
       shared_key ← N.(sharedkey) pkr sks ;;
      
      if (hs && hr) then
        let sid := (pks, pkr) in
          set (sid, shared_key) ;;

        ret (Datatypes.tt : 'unit)
      else
        let sid := (pks, pkr) in
          cset (sid, shared_key) ;;
        ret (Datatypes.tt : 'unit)
      
    }
  ].

End NIKE_scheme.