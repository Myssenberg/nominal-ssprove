(*This is a part of the implementation of the state-separated proof of security for the NaCl crypto_box public-key authenticated encryption scheme.
This file contains the specification for the NBPES scheme.*)

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

Module NBPES.

#[local] Open Scope package_scope.

Record NBPES_scheme :=
  { PK       : finType ;
    PK_pos   : Positive #|PK|;
    SK       : finType ;
    SK_pos   : Positive #|SK|;
    Nonce    : finType ;
    Nonce_pos: Positive #|Nonce|;
    M        : choice_type ;
    C        : choice_type ;
    sample_C : code fset0 [interface] C ;

    pkgen : 
      code fset0 [interface] ('fin #|PK| × 'fin #|SK|) ;

    enc : forall (sk : 'fin #|SK|) (pk : 'fin #|PK|) (m : M) (n : 'fin #|Nonce|),
      code fset0 [interface] C ;

    dec : forall (sk : 'fin #|SK|) (pk : 'fin #|PK|) (c : C) (n : 'fin #|Nonce|),
      code fset0 [interface] M 
  }.

Notation " 'pk p " := ('fin #|PK p|)
  (in custom pack_type at level 2, p constr at level 20).

Notation " 'pk p " := ('fin #|PK p|)
  (at level 3) : package_scope.

Notation " 'sk p " := ('fin #|SK p|)
  (in custom pack_type at level 2, p constr at level 20).

Notation " 'sk p " := ('fin #|SK p|)
  (at level 3) : package_scope.

Notation " 'n p " := ('fin #|Nonce p|)
  (in custom pack_type at level 2, p constr at level 20).

Notation " 'n p " := ('fin #|Nonce p|)
  (at level 3) : package_scope.


Instance pk_posi p : Positive #|PK p|.
Proof.
apply PK_pos. Defined.

Instance sk_posi p : Positive #|SK p|.
Proof.
apply SK_pos. Defined.

Instance nonce_posi p : Positive #|Nonce p|.
Proof.
apply Nonce_pos. Defined.

End NBPES.