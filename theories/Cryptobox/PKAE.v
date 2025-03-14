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

Module NBPES.

Record NBPES :=
  { PK       : finType ;
    PK_pos   : Positive #|PK|;
    SK       : finType ;
    SK_pos   : Positive #|SK|;
    Nonce    : choice_type ;
    M        : choice_type ;
    C        : choice_type ;
    sample_C : code fset0 [interface] C ; (*We might need more logs here*)

    pkgen : 
      code fset0 [interface] ('fin #|PK| × 'fin #|SK|) ;

    enc : forall (m : M) (pk_s : PK) (pk_r : PK) (n : Nonce),
      code fset0 [interface] C ;

    dec : forall (c : C) (pk_s : PK) (pk_r : PK) (n : Nonce),
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

Notation " 'm p " := (M p)
  (in custom pack_type at level 2, p constr at level 20).

Notation " 'm p " := (M p)
  (at level 3) : package_scope.

Notation " 'c p " := (C p)
  (in custom pack_type at level 2, p constr at level 20).

Notation " 'c p " := (C p)
  (at level 3) : package_scope.

Notation " 'n p " := (Nonce p)
  (in custom pack_type at level 2, p constr at level 20).

Notation " 'n p " := (Nonce p)
  (at level 3) : package_scope.



Instance pk_posi p : Positive #|PK p|.
Proof.
apply PK_pos. Defined.

Instance sk_posi p : Positive #|SK p|.
Proof.
apply SK_pos. Defined.

Definition PK_loc (E : NBPES): Location := (chMap 'pk E 'bool ; 0).


Definition SK_loc (E : NBPES): Location := (chMap 'pk E 'sk E ; 1). 


Definition PKAE_locs_tt (E : NBPES):= fset [:: PK_loc E ; SK_loc E]. (*If they're using the same loc, can they share then because Nom-SSP will rename or do we get into trouble?*)
Definition PKAE_locs_ff (E : NBPES):= fset [:: PK_loc E ; SK_loc E].


Definition GEN := 2%N.
Definition GETSK := 4%N.
Definition HONPK := 5%N.

Definition PKENC := 6%N.
Definition PKDEC := 7%N.


Definition I_PKAE_IN (E: NBPES) :=
  [interface
    #val #[ GETSK ]: 'pk E → 'sk E ;  
    #val #[ HONPK ]: 'pk E → 'bool 
   
].

Definition I_PKAE_OUT (E: NBPES) :=
  [interface
    #val #[ PKENC ]: ('sk E × 'pk E × 'm E × 'n E) → 'c E ;
    #val #[ PKDEC ]: ('sk E × 'pk E × 'c E × 'n E) → 'm E 
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



Definition PKAE (E: NBPES):
  game (I_PKAE_IN E) (I_PKAE_OUT E) :=
  [module PKEY_locs_tt E ; 
    #def #[ PKENC ] (SKs : 'sk E, PKr: 'pk E, m : 'm E, n: 'n E): ('c E) {
      True.     
    } ;

    #def #[ PKDEC ] (SKr : 'sk E, PKs : 'pk E, c : 'c E, n : 'n E) : ('m E) {
      True.

    } ;
    
  ].


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