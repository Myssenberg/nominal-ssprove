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

From NominalSSP Require Import cryptobox.

#[local] Open Scope package_scope.

Module PKEY.

Import crypto_box_scheme.


Definition PK_loc (P : crypto_box_scheme): Location := (chMap 'pk P 'bool ; 0).

Definition SK_loc (P : crypto_box_scheme): Location := (chMap 'pk P 'sk P ; 1). 

Definition PKEY_locs_tt (P : crypto_box_scheme):= fset [:: PK_loc P ; SK_loc P]. (*If they're using the same loc, can they share then because Nom-SSP will rename or do we get into trouble?*)
Definition PKEY_locs_ff (P : crypto_box_scheme):= fset [:: PK_loc P ; SK_loc P].

Definition GEN := 2%N.
Definition CSETPK := 3%N.
Definition GETSK := 4%N.
Definition HONPK := 5%N.

Definition PKENC := 6%N.
Definition PKDEC := 7%N.

Definition I_PKEY_OUT (P: crypto_box_scheme) :=
  [interface
    #val #[ GEN ]: 'unit → 'pk P ;
    #val #[ CSETPK ]: 'pk P → 'unit ;
    #val #[ GETSK ]: 'pk P → 'sk P ;
    #val #[ HONPK ]: 'pk P → 'bool 
].

Definition PKEY (b : bool) (P : crypto_box_scheme):
  game (I_PKEY_OUT P) :=
  [module PKEY_locs_tt P ; 
    #def #[ GEN ] (_ : 'unit): ('pk P) {
      '(pk, sk) ← P.(pkgen) ;; (*in doubt whether this should be from cryptobox/NBPES scheme or just randomly sampled*)

      if negb b then (*real*)
        (*#put (PK_loc P) := @setm ('pk P : choiceType) _ PKLOC pk true ;;*) (*the easycrypt code does not register the PK as being honest, but shouldn't it do that?*)
          SKLOC ← get SK_loc P ;;
          #put (SK_loc P) := setm SKLOC pk sk ;;
          ret pk
      else (*ideal*)
        PKLOC ← get PK_loc P;;
        if (PKLOC pk != Some false) then
          #put (PK_loc P) := @setm ('pk P : choiceType) _ PKLOC pk true ;;
          SKLOC ← get SK_loc P ;;
          #put (SK_loc P) := setm SKLOC pk sk ;;
          ret pk
        else
          ret pk
    } ;

    #def #[ CSETPK ] (pk : 'pk P) : 'unit {
      PKLOC ← get PK_loc P;;
      #assert PKLOC pk == None ;;
      #put (PK_loc P) := @setm ('pk P : choiceType) _ PKLOC pk false ;;
      ret (Datatypes.tt : 'unit)
(*I don't know what this Datatypes.tt is, so ask Markus, but it will not let me return unit without this*)
    } ;

    #def #[ GETSK ] (pk : 'pk P) : ('sk P) {
      PKLOC ← get PK_loc P ;;
      SKLOC ← get SK_loc P ;;
      #assert PKLOC pk == Some true ;; (*does #assert fail or break this if it's not true?*)
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

End PKEY.