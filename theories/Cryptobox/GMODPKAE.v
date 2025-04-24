(*This is a part of the implementation of the state-separated game-based proof of security for the NaCl crypto_box authenticated encryption scheme.
This file contains the specification for a GMODPKAE game*)

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

From NominalSSP Require Import AE KEY NBSES NIKE PKAE PKEY.
Import AE KEY NBSES NIKE_scheme NBPES_scheme PKEY.

Import PackageNotation.

#[local] Open Scope package_scope.

Module GMODPKAE.

(*Definition I_GMODPKAE_OUT (N: NIKE_scheme) (E : NBSES_scheme) :=
  [interface
    #val #[ GEN ]: 'unit → 'T 'fin #|N.(NIKE_scheme.PK)| ;
    #val #[ CSETPK ]: 'T 'fin #|N.(NIKE_scheme.PK)| → 'unit ;
    #val #[ PKENC ]: ((('T 'fin #|N.(NIKE_scheme.PK)| × 'T 'fin #|N.(NIKE_scheme.PK)|) × 'm E) × 'n E) → 'c E ;
    #val #[ PKDEC ]: ((('T 'fin #|N.(NIKE_scheme.PK)|× 'T 'fin #|N.(NIKE_scheme.PK)|) × 'c E) × 'n E) → 'm E
].*)

End GMODPKAE.