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

Module NBSES.

Record NBSES :=
  { K        : finType ;
    K_pos    : Positive #|K|;
    Nonce    : choice_type ;
    M        : choice_type ;
    C        : choice_type ;
    sample_C : code fset0 [interface] C ; (*We might need more logs here*)

    kgen : 
      code fset0 [interface] ('fin #|K|) ;

    enc : forall (m : M) (k : K) (n : Nonce),
      code fset0 [interface] C ;

    dec : forall (c : C) (k : K) (n : Nonce),
      code fset0 [interface] M 
  }.

Notation " 'k e " := ('fin #|K e|)
  (in custom pack_type at level 2, e constr at level 20).

Notation " 'k e " := ('fin #|K e|)
  (at level 3) : package_scope.

Notation " 'm e " := (M e)
  (in custom pack_type at level 2, e constr at level 20).

Notation " 'm e " := (M e)
  (at level 3) : package_scope.

Notation " 'c e " := (C e)
  (in custom pack_type at level 2, e constr at level 20).

Notation " 'c e " := (C e)
  (at level 3) : package_scope.

Notation " 'n e " := (Nonce e)
  (in custom pack_type at level 2, e constr at level 20).

Notation " 'n e " := (Nonce e)
  (at level 3) : package_scope.

Instance k_posi e : Positive #|K e|.
Proof.
apply K_pos. Defined.