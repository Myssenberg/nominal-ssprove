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

Import NIKE_scheme NBPES.

Definition chSet t := chMap t 'unit.

Notation " 'T c " := (c) (in custom pack_type at level 2, c constr at level 20).
Notation " 'T c " := (c) (at level 2): package_scope.


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
    
  ].

End PKEY.