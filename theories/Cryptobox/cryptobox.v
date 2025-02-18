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


Module crypto_box_scheme.

Record crypto_box_scheme :=
  { PK       : choice_type ;
    SK       : choice_type ;
    Nonce    : choice_type ;
    M        : choice_type ;
    C        : choice_type ;
    sample_C : code fset0 [interface] C ; (*We might need more logs here*)

    gen : 
      code fset0 [interface] (SK × PK) ;

    csetpk : forall (pk : PK),
      code fset0 [interface] unit; (*Unsure of unit is the right term here*)

    pkenc : forall (m : M) (pk_s : PK) (pk_r : PK) (n : Nonce),
      code fset0 [interface] C ;

    pkdec : forall (c : C) (pk_s : PK) (pk_r : PK) (n : Nonce),
      code fset0 [interface] M 
  }.



End crypto_box_scheme.