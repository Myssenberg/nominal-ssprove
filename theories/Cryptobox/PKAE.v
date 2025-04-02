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

Module NBPES.

#[local] Open Scope package_scope.

Record NBPES :=
  { PK       : finType ;
    PK_pos   : Positive #|PK|;
    SK       : finType ;
    SK_pos   : Positive #|SK|;
    Nonce    : finType ;
    Nonce_pos: Positive #|Nonce|;
    M        : choice_type ;
    C        : choice_type ;
    sample_C : code fset0 [interface] C ; (*We might need more logs here*)

    pkgen : 
      code fset0 [interface] ('fin #|PK| × 'fin #|SK|) ;

    enc : forall (sk : SK) (pk : PK) (m : M) (n : Nonce),
      code fset0 [interface] C ;

    dec : forall (sk : SK) (pk : PK) (c : C) (n : Nonce),
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

Definition chSet t := chMap t 'unit.

Notation " 'set t " := (chSet t) (in custom pack_type at level 2).
Notation " 'set t " := (chSet t) (at level 2): package_scope.

Definition h (E: NBPES) : choice_type := ('pk E × 'pk E).


Definition PK_loc (E : NBPES): Location := (chMap 'pk E 'bool ; 0).

Definition SK_loc (E : NBPES): Location := (chMap 'pk E 'sk E ; 1).

Definition M_loc (E: NBPES): Location := (chMap (h E × 'n E) ('m E × 'c E) ; 2). 


Definition PKAE_locs_tt (E : NBPES):= fset [:: PK_loc E ; SK_loc E ; M_loc E]. (*If they're using the same loc, can they share then because Nom-SSP will rename or do we get into trouble?*)
Definition PKAE_locs_ff (E : NBPES):= fset [:: PK_loc E ; SK_loc E ; M_loc E].

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
    #val #[ PKENC ]: ('pk E × 'pk E × 'm E × 'n E) → 'c E ;
    #val #[ PKDEC ]: ('pk E × 'pk E × 'c E × 'n E) → 'm E
].

Definition I_PKAE_OUT_TEMP (E: NBPES) :=
  [interface
    #val #[ PKENC ]: (('pk E × 'pk E) × 'n E) → 'bool
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

Definition SORT (E: NBPES) (PKs PKr : 'pk E) : h E :=
  if (PKs < PKr) then (PKs, PKr) : (prod _ _) else (PKr, PKs) : (prod _ _).

Definition PKAE (b : bool) (E: NBPES):
  module (I_PKAE_IN E) (I_PKAE_OUT_TEMP E)  := 
  [module PKAE_locs_tt E ;
    #def #[ PKENC ] ('((PKs, PKr), n) : ('pk E × 'pk E) × 'n E) : 'bool {
      #import {sig #[ GETSK ]: 'pk E → 'sk E } as getsk ;;
      #import {sig #[ HONPK ]: 'pk E → 'bool } as honpk ;;
      SKs ← getsk PKs ;;
      HONpkr ← honpk PKr ;;
      let h := SORT E PKs PKr in
      MLOC ← get M_loc E ;;
      #assert MLOC (h, n) == None ;;
      (*if (b && HONpkr) then
        c ←  ? ;;
      else
        c ← E.enc SKs PKr m n ;;
      #put (M_loc E) := setm MLOC (h, n) (m, c) ;;
      return c*)
      ret HONpkr
    }(* ;
    #def #[ PKDEC ] ('(PKs, PKr) : 'pk E × 'pk E) : 'bool {
      #import {sig #[ GETSK ]: 'pk E → 'sk E } as getsk ;;
      #import {sig #[ HONPK ]: 'pk E → 'bool } as honpk ;;
      SKr ← getsk PKr ;;
      HONpks ← PKs ;;
      m ← None ;;
      if (b && HONpks) then
        let h := SORT E PKs PKr in
        m ← (*figure out how to get second value in set*)     
      else
        m ← E.dec SKr PKs c n ;;
      return m
    }*)
  ].



Definition GPKAE_tt_PKEY_tt :=
  True. (*TEMPORARY*)

Definition GPKAE_tt_PKEY_ff :=
  False. (*TEMPORARY*)




(*Definition GPKAE b := if b then GPKAE_PKEY_tt else GPKAE_PKEY_ff.*)


(*Lemma PK_coll_bound:
  forall (A : adversary [interface]),
  AdvFor GPKAE A <=
  AdvFor GPKAE A.
Proof.*)


(*End crypto_box_scheme.*)