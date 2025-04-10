(*This is an implementation of the state-separated game-based proof of security for the NaCl crypto_box authenticated encryption scheme.
This file contains the PKEY package*)

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

From NominalSSP Require Import NIKE PKAE.

#[local] Open Scope package_scope.

Module PKEY.

Import NIKE_scheme NBPES_scheme.

Record GEN_scheme :=
  { PK             : finType ;
    PK_pos         : Positive #|PK|;
    SK             : finType ;
    SK_pos         : Positive #|SK|;

    pkgen : 
      code fset0 [interface] ('fin #|PK| × 'fin #|SK|) ;
  }.

Definition NBPES_to_GEN (N : NBPES_scheme) : (GEN_scheme) :=
  {| PK := N.(NBPES_scheme.PK) ;
     PK_pos := N.(NBPES_scheme.PK_pos) ;
     SK := N.(NBPES_scheme.SK) ;
     SK_pos := N.(NBPES_scheme.SK_pos) ;
     pkgen := N.(NBPES_scheme.pkgen)
|}.

Definition NIKE_to_GEN (N : NIKE_scheme) : (GEN_scheme) :=
  {| PK := N.(NIKE_scheme.PK) ;
     PK_pos := N.(NIKE_scheme.PK_pos) ;
     SK := N.(NIKE_scheme.SK) ;
     SK_pos := N.(NIKE_scheme.SK_pos) ;
     pkgen := N.(NIKE_scheme.pkgen)
|}.

Definition chSet t := chMap t 'unit.

Notation " 'pk n " := ('fin #|PK n|)
  (in custom pack_type at level 2, n constr at level 20).

Notation " 'pk n " := ('fin #|PK n|)
  (at level 3) : package_scope.

Notation " 'sk n " := ('fin #|SK n|)
  (in custom pack_type at level 2, n constr at level 20).

Notation " 'sk n " := ('fin #|SK n|)
  (at level 3) : package_scope.

Instance pk_posi p : Positive #|PK p|.
Proof.
apply PK_pos. Defined.

Instance sk_posi p : Positive #|SK p|.
Proof.
apply SK_pos. Defined.


Definition PK_loc (G : GEN_scheme): Location := (chMap 'pk G 'bool ; 0).

Definition SK_loc (G : GEN_scheme): Location := (chMap 'pk G 'sk G ; 1). 

Definition PKEY_locs_tt (G : GEN_scheme):= fset [:: PK_loc G ; SK_loc G]. (*If they're using the same loc, can they share then because Nom-SSP will rename or do we get into trouble?*)
Definition PKEY_locs_ff (G : GEN_scheme):= fset [:: PK_loc G ; SK_loc G].

Definition GEN := 2%N.
Definition CSETPK := 3%N.
Definition GETSK := 4%N.
Definition HONPK := 5%N.

Definition I_PKEY_OUT (G: GEN_scheme) :=
  [interface
    #val #[ GEN ]: 'unit → 'pk G ;
    #val #[ CSETPK ]: 'pk G → 'unit ;
    #val #[ GETSK ]: 'pk G → 'sk G ;
    #val #[ HONPK ]: 'pk G → 'bool 
].

Definition PKEY (b : bool) (G : GEN_scheme):
  game (I_PKEY_OUT G) :=
  [module PKEY_locs_tt G ; 
    #def #[ GEN ] (_ : 'unit): ('pk G) {
      '(pk, sk) ← G.(pkgen) ;; (*in doubt whether this should be from cryptobox/NBPES scheme or just randomly sampled*)

      if negb b then (*real*)
        (*#put (PK_loc P) := @setm ('pk P : choiceType) _ PKLOC pk true ;;*) (*the easycrypt code does not register the PK as being honest, but shouldn't it do that?*)
          SKLOC ← get SK_loc G ;;
          #put (SK_loc G) := setm SKLOC pk sk ;;
          ret pk
      else (*ideal*)
        PKLOC ← get PK_loc G;;
        if (PKLOC pk != Some false) then
          #put (PK_loc G) := @setm ('pk G : choiceType) _ PKLOC pk true ;;
          SKLOC ← get SK_loc G ;;
          #put (SK_loc G) := setm SKLOC pk sk ;;
          ret pk
        else
          ret pk
    } ;

    #def #[ CSETPK ] (pk : 'pk G) : 'unit {
      PKLOC ← get PK_loc G;;
      #assert PKLOC pk == None ;;
      #put (PK_loc G) := @setm ('pk G : choiceType) _ PKLOC pk false ;;
      ret (Datatypes.tt : 'unit)
(*I don't know what this Datatypes.tt is, so ask Markus, but it will not let me return unit without this*)
    } ;

    #def #[ GETSK ] (pk : 'pk G) : ('sk G) {
      PKLOC ← get PK_loc G ;;
      SKLOC ← get SK_loc G ;;
      #assert PKLOC pk == Some true ;; (*does #assert fail or break this if it's not true?*)
      #assert isSome (SKLOC pk) as someSK;;
      let sk := getSome (SKLOC pk) someSK in
      @ret ('sk G) sk
    } ;

    #def #[ HONPK ] (pk : 'pk G) : 'bool {
      PKLOC ← get PK_loc G ;;
      #assert isSome (PKLOC pk) as someBool;;
      let b := getSome (PKLOC pk) someBool in

      @ret ('bool) b 
    }
    
  ].


(*
Definition PK_loc (pk : finType) `{Positive #|pk|}: Location := (chMap 'fin #|pk| 'bool ; 0).
Definition SK_loc (pk sk : finType) `{Positive #|pk|} `{Positive #|sk|}: Location := (chMap 'fin #|pk| 'fin #|sk| ; 1).

Definition PKEY_locs_tt (pk sk : finType) `{Positive #|pk|} `{Positive #|sk|} := fset [:: PK_loc pk ; SK_loc pk sk ]. (*If they're using the same loc, can they share then because Nom-SSP will rename or do we get into trouble?*)
Definition PKEY_locs_ff (pk sk : finType) `{Positive #|pk|} `{Positive #|sk|} := fset [:: PK_loc pk ; SK_loc pk sk ]. 

Definition GEN := 2%N.
Definition CSETPK := 3%N.
Definition GETSK := 4%N.
Definition HONPK := 5%N.

Definition PKENC := 6%N.
Definition PKDEC := 7%N.

Definition I_PKEY_OUT (pk : choice_type) (sk : choice_type) :=
  [interface
    #val #[ GEN ]: 'unit → 'T pk ;
    #val #[ CSETPK ]: 'T pk → 'unit ;
    #val #[ GETSK ]:  'T pk → 'T sk ;
    #val #[ HONPK ]: 'T pk → 'bool 
].

Definition PKEY (b : bool) (pk sk : finType) `{Positive #|pk|} `{Positive #|sk|} (pkgen : code fset0 [interface] ('fin #|pk| × 'fin #|sk|)):
  game (I_PKEY_OUT 'fin #|pk| 'fin #|sk|) :=
  [module PKEY_locs_tt pk sk ; 
    #def #[ GEN ] (_ : 'unit): ('fin #|pk|) {
      '(pk', sk') ← pkgen ;; (*in doubt whether this should be from cryptobox/NBPES scheme or just randomly sampled*)

      if negb b then (*real*)
        (*#put (PK_loc P) := @setm ('pk P : choiceType) _ PKLOC pk true ;;*) (*the easycrypt code does not register the PK as being honest, but shouldn't it do that?*)
          SKLOC ← get SK_loc pk sk ;;
          #put (SK_loc pk sk) := setm SKLOC pk' sk' ;;
          ret pk'
      else (*ideal*)
        PKLOC ← get PK_loc pk;;
        if (PKLOC pk' != Some false) then
          #put (PK_loc pk) := setm PKLOC pk' true ;;
          SKLOC ← get SK_loc pk sk ;;
          #put (SK_loc pk sk) := setm SKLOC pk' sk' ;;
          ret pk'
        else
          ret pk'
    } ;

    #def #[ CSETPK ] (pk' : 'T 'fin #|pk|): 'unit {
      PKLOC ← get PK_loc pk;;
      #assert PKLOC pk' == None ;;
      #put (PK_loc pk) := setm PKLOC pk' false ;;
      ret (Datatypes.tt : 'unit)
    } ;

    #def #[ GETSK ] (pk' : 'T 'fin #|pk|) : ('T 'fin #|sk|) {
      PKLOC ← get PK_loc pk ;;
      SKLOC ← get SK_loc pk sk ;;
      #assert PKLOC pk' == Some true ;; (*does #assert fail or break this if it's not true?*)
      #assert isSome (SKLOC pk') as someSK;;
      let sk' := getSome (SKLOC pk') someSK in
      @ret ('T 'fin #|sk|) sk'
    } ;

    #def #[ HONPK ] (pk' : 'T 'fin #|pk|) : 'bool {
      PKLOC ← get PK_loc pk ;;
      #assert isSome (PKLOC pk') as someBool;;
      let b := getSome (PKLOC pk') someBool in

      @ret ('bool) b 
    }
    
  ].*)

End PKEY.