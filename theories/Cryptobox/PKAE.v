(*This is part of an implementation of the state-separated game-based proof of security for the NaCl crypto_box authenticated encryption scheme. This file contains the NBPES scheme as well as the PKAE package.*)

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

Record NBPES_scheme :=
  { PK       : finType ;
    PK_pos   : Positive #|PK|;
    SK       : finType ;
    SK_pos   : Positive #|SK|;
    Nonce    : choice_type ;
    M        : choice_type ;
    C        : choice_type ;

    pkgen : 
      code fset0 [interface] ('fin #|PK| × 'fin #|SK|) ;

    enc : forall (m : M) (pk_s : PK) (pk_r : PK) (n : Nonce),
      code fset0 [interface] C ;

    dec : forall (c : C) (pk_s : PK) (pk_r : PK) (n : Nonce),
      code fset0 [interface] M; 

    cdist : code fset0 [interface] C ; (*We might need more logs here*)
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

Notation " 'T c " := (c) (in custom pack_type at level 2, c constr at level 20).
Notation " 'T c " := (c) (at level 2): package_scope.

(*the handle, h, aka the SessionID will be represented by a pair of sender and receiver public keys: (pks, pkr)*)

(*Definition PK_loc (pk : finType) `{Positive #|pk|}: Location := (chMap 'fin #|pk| 'bool ; 0).

Definition SK_loc (pk sk : finType) `{Positive #|pk|} `{Positive #|sk|}: Location := (chMap 'fin #|pk| 'fin #|sk| ; 1).

Definition PKAE_locs_tt (pk sk : finType) (n m c : choice_type) `{Positive #|pk|} `{Positive #|sk|}:= fset [:: PK_loc pk ; SK_loc pk sk ; M_loc pk sk n m c]. (*If they're using the same loc, can they share then because Nom-SSP will rename or do we get into trouble?*)
Definition PKAE_locs_ff (pk sk : finType) (n m c : choice_type) `{Positive #|pk|} `{Positive #|sk|}:= fset [:: PK_loc pk ; SK_loc pk sk ; M_loc pk sk n m c].
*)

Definition M_loc (pk sk : finType) (n m c : choice_type) `{Positive #|pk|} `{Positive #|sk|} : Location := (chMap (('fin #|pk| × 'fin #|sk|) × n) (m × c) ; 2).

Definition PKAE_locs_tt (pk sk : finType) (n m c : choice_type) `{Positive #|pk|} `{Positive #|sk|}:= fset [:: M_loc pk sk n m c]. (*If they're using the same loc, can they share then because Nom-SSP will rename or do we get into trouble?*)
Definition PKAE_locs_ff (pk sk : finType) (n m c : choice_type) `{Positive #|pk|} `{Positive #|sk|}:= fset [:: M_loc pk sk n m c].


Definition GEN := 2%N.
Definition GETSK := 4%N.
Definition HONPK := 5%N.

Definition PKENC := 6%N.
Definition PKDEC := 7%N.


Definition I_PKAE_IN (pk sk : choice_type) :=
  [interface
    #val #[ GETSK ]: 'T pk → 'T sk ;  
    #val #[ HONPK ]: 'T pk → 'bool 
].

Definition I_PKAE_OUT (pk m n c : choice_type) :=
  [interface
    #val #[ PKENC ]: ((('T pk × 'T pk) × 'T m) × 'T n) → 'T c ;
    #val #[ PKDEC ]: ((('T pk × 'T pk) × 'T c) × 'T n) → 'T m 
].


(*Definition SORT (pks pkr : choice_type) : (pks × pkr) :=
  if (#| pks | < #| pkr |) then (pks, pkr) else (pkr, pks).


Definition SORT (pks pkr : choice_type) : choice_type * choice_type :=
  if (#| Finite.clone pks pks | < #| Finite.clone pkr erefl |)
  then (pks, pkr)
  else (pkr, pks).

Definition SORT (pks pkr : choice_type) : choice_type * choice_type :=
  let fin_pks := [finType of pks] in
  let fin_pkr := [finType of pkr] in
  if (#|fin_pks| < #|fin_pkr|)
  then (pks, pkr)
  else (pkr, pks).

Definition SORT ('fin #|pks| 'fin #|pkr| : choice_type) : (pks × pkr) :=
  if (#|pks| < #|pkr|) then (pks, pkr) : (prod _ _) else (pkr, pks) : (prod _ _).


Definition SORT (pks pkr : finType) `{Positive #|pks|} `{Positive #|pkr|} : (choice_type * choice_type) :=
  if (#|pks| < #|pkr|) then ('fin #|pks|, 'fin #|pkr|) else ('fin #|pkr|, 'fin #|pks|). (*not sure this sorts the correct thing, if it sorts the length of the keys*)*)

Definition PKAE (b : bool) (pk sk : finType) (n m c : choice_type) `{Positive #|pk|} `{Positive #|sk|} (cdist : code fset0 [interface] c) (enc : forall (m : m) (pks : pk) (pkr : pk) (n : n),
      code fset0 [interface] c) (dec : forall (c : c) (pks : pk) (pkr : pk) (n : n),
      code fset0 [interface] m):
  module (I_PKAE_IN 'fin #|pk| 'fin #|sk|) (I_PKAE_OUT 'fin #|pk| m n c)  := 
  [module PKAE_locs_tt pk sk m n c ;
    #def #[ PKENC ] ('(((pks', pkr'), m'), n') : (('T 'fin #|pk| × 'T 'fin #|pk|) × 'T m) × 'T n) : ('T c) {
      #import {sig #[ GETSK ]: 'T 'fin #|pk|  → 'T 'fin #|sk| } as getsk ;;
      #import {sig #[ HONPK ]: 'T 'fin #|pk| → 'bool } as honpk ;;
      sks ← getsk pks' ;;
      HONpkr ← honpk pkr' ;;
      let h := (pks', pkr') (*SORT pks' pkr'*) in
      MLOC ← get M_loc pk sk n m c ;;
      #assert (getm MLOC ((pkr', sks), n')) == None ;;
      if (b && HONpkr) then
        c' ← cdist ;;        
        #put (M_loc pk sk n m c) := setm MLOC (h, n') (m', c') ;;
        ret c'
      else
        c' ← enc sks pkr' m' n' ;;
        #put (M_loc pk sk n m c) := setm MLOC (h, n') (m', c') ;;
        ret c'
    } ;
    #def #[ PKDEC ] ('(((pkr', pks'), c'), n') : (('T pk × 'T pk) × 'T c) × 'T n) : ('T m) {
      #import {sig #[ GETSK ]: 'T 'fin #|pk| → 'T sk } as getsk ;;
      #import {sig #[ HONPK ]: 'T 'fin #|pk| → 'bool } as honpk ;;
      skr ← getsk pkr' ;;
      HONpks ← honpk pks' ;;
      if (b && HONpks) then
        let h := (pks', pkr') (*SORT pks' pkr'*) in
        MLOC ← get M_loc pk sk n m c ;;        
        #assert isSome (MLOC (h, n')) as MC ;;
        let (m', c'') := getSome (MLOC (h, n')) MC in
        ret m'
      else
        m' ← dec skr pks' c' n' ;;
        ret m'
    }
  ].

End NBPES.