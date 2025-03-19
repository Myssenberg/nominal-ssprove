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

    sharedkey : forall (pk : PK) (sk : SK),
      code fset0 [interface] ('fin #|Shared_Key|) (*;
    
    kdist : *) (*currently have no clue how to represent kdist*)
  }.

Notation " 'pk p " := ('fin #|PK p|)
  (in custom pack_type at level 2, p constr at level 20).

Notation " 'pk p " := ('fin #|PK p|)
  (at level 3) : package_scope.

Notation " 'sk p " := ('fin #|SK p|)
  (in custom pack_type at level 2, p constr at level 20).

Notation " 'sk p " := ('fin #|SK p|)
  (at level 3) : package_scope.

Notation " 'shared_key p " := ('fin #|Shared_Key p|)
  (in custom pack_type at level 2, p constr at level 20).

Notation " 'shared_key p " := ('fin #|Shared_Key p|)
  (at level 3) : package_scope.


Instance pk_posi p : Positive #|PK p|.
Proof.
apply PK_pos. Defined.

Instance sk_posi p : Positive #|SK p|.
Proof.
apply SK_pos. Defined.

Instance sharedkey_posi p : Positive #|Shared_Key p|.
Proof.
apply Shared_Key_pos. Defined.


End NIKE_scheme.