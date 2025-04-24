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

Module NBPES_scheme.

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
    sample_C : code fset0 [interface] C ; (*We might need more logs here*)

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

Definition h (E: NBPES_scheme) : choice_type := ('pk E × 'pk E).


Definition PK_loc (E : NBPES_scheme): Location := (chMap 'pk E 'bool ; 8).

Definition SK_loc (E : NBPES_scheme): Location := (chMap 'pk E 'sk E ; 9).

Definition M_loc (E: NBPES_scheme): Location := (chMap (h E × 'n E) ('m E × 'c E) ; 10). 


Definition PKAE_locs_tt (E : NBPES_scheme):= fset [:: PK_loc E ; SK_loc E ; M_loc E]. (*If they're using the same loc, can they share then because Nom-SSP will rename or do we get into trouble?*)
Definition PKAE_locs_ff (E : NBPES_scheme):= fset [:: PK_loc E ; SK_loc E ; M_loc E].

Definition GETSK := 4%N.
Definition HONPK := 5%N.

Definition PKENC := 14%N.
Definition PKDEC := 15%N.


Definition I_PKAE_IN (E: NBPES_scheme) :=
  [interface
    #val #[ GETSK ]: 'pk E → 'sk E ;  
    #val #[ HONPK ]: 'pk E → 'bool 
].

Definition I_PKAE_OUT (E: NBPES_scheme) :=
  [interface
    #val #[ PKENC ]: ((('pk E × 'pk E) × 'm E) × 'n E) → 'c E ;
    #val #[ PKDEC ]: ((('pk E × 'pk E) × 'c E) × 'n E) → 'm E 
].


Definition SORT (E: NBPES_scheme) (PKs PKr : 'pk E) : h E :=
  if (PKs < PKr) then (PKs, PKr) : (prod _ _) else (PKr, PKs) : (prod _ _).

Definition PKAE (E: NBPES_scheme) (b : bool):
  module (I_PKAE_IN E) (I_PKAE_OUT E)  := 
  [module PKAE_locs_tt E ;
    #def #[ PKENC ] ('(((PKs, PKr), m), n) : (('pk E × 'pk E) × 'm E) × 'n E) : ('c E) {
      #import {sig #[ GETSK ]: 'pk E → 'sk E } as getsk ;;
      #import {sig #[ HONPK ]: 'pk E → 'bool } as honpk ;;
      SKs ← getsk PKs ;;
      HONpkr ← honpk PKr ;;
      let h := SORT E PKs PKr in
      MLOC ← get M_loc E ;;
      #assert MLOC (h, n) == None ;;
      if (b && HONpkr) then
        c ← E.(sample_C) ;;        
        #put (M_loc E) := setm MLOC (h, n) (m, c) ;;
        ret c
      else
        c ← E.(enc) SKs PKr m n ;;
        #put (M_loc E) := setm MLOC (h, n) (m, c) ;;
        ret c
    } ;
    #def #[ PKDEC ] ('(((PKr, PKs), c), n) : (('pk E × 'pk E) × 'c E) × 'n E) : ('m E) {
      #import {sig #[ GETSK ]: 'pk E → 'sk E } as getsk ;;
      #import {sig #[ HONPK ]: 'pk E → 'bool } as honpk ;;
      SKr ← getsk PKr ;;
      HONpks ← honpk PKs ;;
      if (b && HONpks) then
        let h := SORT E PKs PKr in
        MLOC ← get M_loc E ;;        
        #assert isSome (MLOC (h, n)) as MC ;;
        let (m, c') := getSome (MLOC (h, n)) MC in
        ret m
      else
        m ← E.(dec) SKr PKs c n ;;
        ret m
    }
  ].


(*Definition GPKAE b := if b then GPKAE_PKEY_tt else GPKAE_PKEY_ff.*)


(*Lemma PK_coll_bound:
  forall (A : adversary [interface]),
  AdvFor GPKAE A <=
  AdvFor GPKAE A.
Proof.*)


(*End crypto_box_scheme.*)



(*

Notation " 'T c " := (c) (in custom pack_type at level 2, c constr at level 20).
Notation " 'T c " := (c) (at level 2): package_scope.

(*the handle, h, aka the SessionID will be represented by a pair of sender and receiver public keys: (pks, pkr)*)

(*Definition PK_loc (pk : finType) `{Positive #|pk|}: Location := (chMap 'fin #|pk| 'bool ; 0).

Definition SK_loc (pk sk : finType) `{Positive #|pk|} `{Positive #|sk|}: Location := (chMap 'fin #|pk| 'fin #|sk| ; 1).

Definition PKAE_locs_tt (pk sk : finType) (n m c : choice_type) `{Positive #|pk|} `{Positive #|sk|}:= fset [:: PK_loc pk ; SK_loc pk sk ; M_loc pk sk n m c]. (*If they're using the same loc, can they share then because Nom-SSP will rename or do we get into trouble?*)
Definition PKAE_locs_ff (pk sk : finType) (n m c : choice_type) `{Positive #|pk|} `{Positive #|sk|}:= fset [:: PK_loc pk ; SK_loc pk sk ; M_loc pk sk n m c].
*)

Definition M_loc (pk sk n : finType) (m c : choice_type) `{Positive #|pk|} `{Positive #|sk|} `{Positive #|n|}: Location := (chMap (('fin #|pk| × 'fin #|sk|) × 'fin #|n|) (m × c) ; 2).

Definition PKAE_locs_tt (pk sk n : finType) (m c : choice_type) `{Positive #|pk|} `{Positive #|sk|} `{Positive #|n|}:= fset [:: M_loc pk sk n m c]. (*If they're using the same loc, can they share then because Nom-SSP will rename or do we get into trouble?*)
Definition PKAE_locs_ff (pk sk n : finType) (m c : choice_type) `{Positive #|pk|} `{Positive #|sk|} `{Positive #|n|}:= fset [:: M_loc pk sk n m c].


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
  if (#|pks| < #|pkr|) then (pks, pkr) : (prod _ _) else (pkr, pks) : (prod _ _).*)


Definition SORT (PK : finType) `{Positive #|PK|} (pks pkr : PK) : (PK * PK) :=
  if (fto pks < fto pkr)%ord then (pks, pkr) else (pkr, pks). (*not sure this sorts the correct thing, if it sorts the length of the keys*)

(*Definition SORTc (pks pkr : choice_type) : (choice_type * choice_type) :=
  if ((otf (fto pks)) < (otf (fto pkr))) then (pks, pkr) : (prod _ _) else (pkr, pks) : (prod _ _).*)

Check fto.
Check otf.

Definition PKAE (b : bool) (pk sk n : finType) (m c : choice_type) `{Positive #|pk|} `{Positive #|sk|} `{Positive #|n|} (cdist : code fset0 [interface] c) (enc : forall (m : m) (pks : pk) (pkr : pk) (n : n),
      code fset0 [interface] c) (dec : forall (c : c) (pks : pk) (pkr : pk) (n : n),
      code fset0 [interface] m):
  module (I_PKAE_IN 'fin #|pk| 'fin #|sk|) (I_PKAE_OUT 'fin #|pk| m 'fin #|n| c)  := 
  [module PKAE_locs_tt pk sk n m c ;
    #def #[ PKENC ] ('(((pks', pkr'), m'), n') : (('T ('fin #|pk| × 'fin #|pk|) × 'T m) × 'T 'fin #|n|)) : ('T c) {
      #import {sig #[ GETSK ]: 'T 'fin #|pk|  → 'T 'fin #|sk| } as getsk ;;
      #import {sig #[ HONPK ]: 'T 'fin #|pk| → 'bool } as honpk ;;
      sks ← getsk pks' ;;
      HONpkr ← honpk pkr' ;;
      let '(pk_l, pk_r) := (*(pks', pkr')*) SORT pk (otf pks') (otf pkr') in
      MLOC ← get M_loc pk sk n m c ;;
      #assert (getm MLOC ((pkr', sks), n')) == None ;;
      if (b && HONpkr) then
        c' ← cdist ;;        
        #put (M_loc pk sk n m c) := setm MLOC ((fto pk_l, sks), n') (m', c') ;;
        ret c'
      else
        c' ← enc m' pkr' sks n' ;;
        #put (M_loc pk sk n m c) := setm MLOC ((fto pk_l, sks), n') (m', c') ;;
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
  ].*)

End NBPES_scheme.
