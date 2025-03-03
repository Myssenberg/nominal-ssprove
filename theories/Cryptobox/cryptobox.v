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
      code fset0 [interface] (PK) ;

    csetpk : forall (pk : PK),
      code fset0 [interface] unit; (*Unsure of unit is the right term here*)

    pkenc : forall (m : M) (pk_s : PK) (pk_r : PK) (n : Nonce),
      code fset0 [interface] C ;

    pkdec : forall (c : C) (pk_s : PK) (pk_r : PK) (n : Nonce),
      code fset0 [interface] M 
  }.

Notation " 'pk p " := (PK p)
  (in custom pack_type at level 2, p constr at level 20).

Notation " 'pk p " := (PK p)
  (at level 3) : package_scope.

Notation " 'sk p " := (SK p)
  (in custom pack_type at level 2, p constr at level 20).

Notation " 'sk p " := (SK p)
  (at level 3) : package_scope.

Notation " 'm p " := (M p)
  (in custom pack_type at level 2, p constr at level 20).

Notation " 'm p " := (M p)
  (at level 3) : package_scope.

Notation " 'c p " := (C p)
  (in custom pack_type at level 2, p constr at level 20).

Notation " 'c p " := (C p)
  (at level 3) : package_scope.


(*Definition PK_loc (P : crypto_box_scheme): Location := ('option ('pk P) ; 0).*)(*Trying to use option instead of true/false from the paper*)

Definition PK_loc (P : crypto_box_scheme): Location := ('pk P %B ; 0).

Definition SK_loc (P : crypto_box_scheme): Location := (chMap 'pk P 'sk P ; 0). 


Definition PKEY_locs_tt (P : crypto_box_scheme):= fset [:: PK_loc P ; SK_loc P]. (*If they're using the same loc, can they share then because Nom-SSP will rename or do we get into trouble?*)
Definition PKEY_locs_ff (P : crypto_box_scheme):= fset [:: PK_loc P ; SK_loc P].

Definition PKEY_tt (P : crypto_box_scheme):
  game [interface #val #[gen]: 'unit → 'pk P ]:=
  [module PKEY_locs_tt P ; 
    #def #[gen] : PK {
      '(pk) <- P.(gen) ;;
      PKLOC <- get PK_loc ;;
      #put (PK_loc P) := setm PKLOC pk True ;;
      ret pk
    }
  ].

Definition PKEY_ff :=
  True.

Definition GPKAE_tt_PKEY_tt :=
  True. (*TEMPORARY*)

Definition GPKAE_tt_PKEY_ff :=
  False. (*TEMPORARY*)




Definition GPKAE b := if b then GPKAE_PKEY_tt else GPKAE_PKEY_ff.


Lemma PK_coll_bound:
  forall (A : adversary [interface]),
  AdvFor GPKAE A <=
  AdvFor GPKAE A.
Proof.


End crypto_box_scheme.