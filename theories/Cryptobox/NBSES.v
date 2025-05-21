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

#[local] Open Scope package_scope.

Module NBSES.

Record NBSES_scheme :=
  { Shared_Key        : finType ;
    Shared_Key_pos    : Positive #|Shared_Key|;
    Nonce    : finType ;
    Nonce_pos: Positive #|Nonce|;
    M        : choice_type ;
    C        : choice_type ;
    sample_K : code fset0 [interface] 'fin #|Shared_Key| ;
    sample_C : code fset0 [interface] C ;

    enc : forall (m : M) (k : 'fin #|Shared_Key|) (n : 'fin #|Nonce|),
      code fset0 [interface] C ;

    dec : forall (c : C) (k : 'fin #|Shared_Key|) (n : 'fin #|Nonce|),
      code fset0 [interface] M 
  }.


Notation " 'k e " := ('fin #|Shared_Key e|)
  (in custom pack_type at level 2, e constr at level 20).

Notation " 'k e " := ('fin #|Shared_Key e|)
  (at level 3) : package_scope.

Notation " 'n e " := ('fin #|Nonce e|)
  (in custom pack_type at level 2, e constr at level 20).

Notation " 'n e " := ('fin #|Nonce e|)
  (at level 3) : package_scope.

Instance k_posi e : Positive #|Shared_Key e|.
Proof.
apply Shared_Key_pos. Defined.

Instance Nonce_posi e : Positive #|Nonce e|.
Proof.
apply Nonce_pos. Defined.

End NBSES.