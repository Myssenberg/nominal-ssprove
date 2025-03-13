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

    csetpk : forall (pk : PK),
      code fset0 [interface] unit; (*Unsure of unit is the right term here*)

    pkenc : forall (m : M) (pk_s : PK) (pk_r : PK) (n : Nonce),
      code fset0 [interface] C ;

    pkdec : forall (c : C) (pk_s : PK) (pk_r : PK) (n : Nonce),
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


(*Definition PK_loc (P : crypto_box_scheme): Location := ('option ('pk P) ; 0%N).*)(*Trying to use option instead of true/false from the paper*)

Instance pk_posi p : Positive #|PK p|.
Proof.
apply PK_pos. Defined.

Instance sk_posi p : Positive #|SK p|.
Proof.
apply SK_pos. Defined.

Definition PK_loc (P : crypto_box_scheme): Location := (chMap 'pk P 'bool ; 0).

(*Definition PK_loc (P : crypto_box_scheme): Location := ('set ('pk P × 'bool) ; 0).*)

Definition SK_loc (P : crypto_box_scheme): Location := (chMap 'pk P 'sk P ; 1). 


Definition PKEY_locs_tt (P : crypto_box_scheme):= fset [:: PK_loc P ; SK_loc P]. (*If they're using the same loc, can they share then because Nom-SSP will rename or do we get into trouble?*)
Definition PKEY_locs_ff (P : crypto_box_scheme):= fset [:: PK_loc P ; SK_loc P].

(*Context (PKgen : crypto_box_scheme -> (PK × SK)).*)

Definition GEN := 2%N.
Definition CSETPK := 3%N.
Definition GETSK := 4%N.
Definition HONPK := 5%N.

Definition PKENC := 6%N.
Definition PKDEC := 7%N.

Definition I_PKEY (P: crypto_box_scheme) :=
  [interface
    #val #[ GEN ]: 'unit → 'pk P ;
    #val #[ CSETPK ]: 'pk P → 'unit ;
    #val #[ GETSK ]: 'pk P → 'sk P ;
    #val #[ HONPK ]: 'pk P → 'bool 
].

Definition I_PKAE_IN (P: crypto_box_scheme) :=
  [interface
    #val #[ GETSK ]: 'pk P → 'sk P ;  (*Delete the in interface?*)
    #val #[ HONPK ]: 'pk P → 'bool 
   
].

Definition I_PKAE_OUT (P: crypto_box_scheme) :=
  [interface
    #val #[ PKENC ]: ('sk P × 'pk P × 'm P × 'n P) → 'c P ;
    #val #[ PKDEC ]: ('sk P × 'pk P × 'c P × 'n P) → 'm P 
].

Check getSome.

Notation "x ← 'getSome' n ;; c" :=
  ( v ← get n ;;
    #assert (isSome v) as vSome ;;
    let x := getSome v vSome in
    c
  )
  (at level 100, n at next level, right associativity,
  format "x  ←  getSome  n  ;;  '//' c")
  : package_scope.

Definition PKEY (P : crypto_box_scheme):
  game (I_PKEY P) :=
  [module PKEY_locs_tt P ; 
    #def #[ GEN ] (_ : 'unit): ('pk P) {
      '(pk, sk) ← P.(pkgen) ;;
      PKLOC ← get PK_loc P;;
      #put (PK_loc P) := @setm ('pk P : choiceType) _ PKLOC pk true ;;

      
      SKLOC ← get SK_loc P ;;
      #put (SK_loc P) := setm SKLOC pk sk ;;
      ret pk
    } ;

    #def #[ CSETPK ] (pk : 'pk P) : 'unit {
      (*(if #assert (PKLOC pk == None) then
        #put (PK_loc P) := @setm ('pk P : choiceType) _ PKLOC pk false ;;
        ret Datatypes.tt
      else
        ret Datatypes.tt) ;;*)

      PKLOC ← get PK_loc P;;
      #assert PKLOC pk == None ;;
      #put (PK_loc P) := @setm ('pk P : choiceType) _ PKLOC pk false ;;
      ret (Datatypes.tt : 'unit)
(*I don't know what this Datatypes.tt is, so ask Markus, but it will not let me return unit without this*)
    } ;

    #def #[ GETSK ] (pk : 'pk P) : ('sk P) {
      SKLOC ← get SK_loc P ;;
      #assert isSome (SKLOC pk) as someSK;;

      let sk := getSome (SKLOC pk) someSK in
      @ret ('sk P) sk
    } ;

    #def #[ HONPK ] (pk : 'pk P) : 'bool {
      PKLOC ← get PK_loc P ;;
      #assert isSome (PKLOC pk) as someBool;;
      let b := getSome (PKLOC pk) someBool in

      @ret ('bool) b 
    }
    
  ].

Definition PKAE (E: NBPES, P : crypto_box_scheme):
  game (I_PKAE_IN P) (I_PKAE_OUT P) :=
  [module PKEY_locs_tt P ; 
    #def #[ PKENC ] (SKs : 'sk P, PKr: 'pk P, m : 'm P, n: 'n p): ('c P) {
      true.     
    } ;

    #def #[ PKDEC ] (SKr : 'sk P, PKs : 'pk P, c : 'c P, n : 'n p) : ('m P) {
      true.

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