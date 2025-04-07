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

From NominalSSP Require Import NBSES.

Import NBSES.

Module SAE.

Notation " 'T c " := (c) (in custom pack_type at level 2, c constr at level 20).
Notation " 'T c " := (c) (at level 2): package_scope.

Definition M_loc (n : finType) (m c : choice_type) `{Positive #|n|} : Location := (chMap 'fin #|n| (m × c) ; 0).
Definition K_loc (k : finType) `{Positive #|k|} : Location := ('option 'fin #|k| ; 1).

Definition SAE_locs_tt (m c : choice_type) (n k : finType) `{Positive #|n|} `{Positive #|k|} := fset [::  M_loc n m c ; K_loc k]. (*If they're using the same loc, can they share then because Nom-SSP will rename or do we get into trouble?*)
Definition SAE_locs_ff (m c : choice_type) (n k : finType) `{Positive #|n|} `{Positive #|k|} := fset [::  M_loc n m c ; K_loc k]. (*If they're using the same loc, can they share then because Nom-SSP will rename or do we get into trouble?*)

Definition GEN := 2%N.
Definition ENC := 3%N.
Definition DEC := 4%N.

Definition I_SAE_OUT (n m c: choice_type) :=
  [interface
    #val #[ GEN ]: 'unit → 'unit ;    
    #val #[ ENC ]: ('T m × 'T n) → 'T c  ;
    #val #[ DEC ]: ('T c × 'T n) → 'T m 
].

Definition SAE (b : bool) (m c : choice_type) (n k : finType) `{Positive #|n|} `{Positive #|k|} (sample_K : code fset0 [interface] 'fin #|k|) (sample_C : code fset0 [interface] c) (enc : forall (m : m) (k : 'T 'fin #|k|) (n : 'T 'fin #|n|), code fset0 [interface] c) (dec : forall (c : c) (k : 'T 'fin #|k|) (n : 'fin #|n|), code fset0 [interface] m):
  game (I_SAE_OUT 'fin #|n| m c)  := 
  [module SAE_locs_tt m c n k ;
    #def #[ GEN ] (_ : 'unit) : ('unit) {
      KLOC ← get K_loc k ;;
      match KLOC with
      | None =>
        k' ← sample_K ;;
        #put (K_loc k) := Some k' ;;
        ret (Datatypes.tt : 'unit)
      | Some k' => ret (Datatypes.tt : 'unit)
      end
    } ;
    #def #[ ENC ] ('(m', n') : ('T m × 'T 'fin #|n|)) : ('T c) {
      MLOC ← get M_loc n m c ;;
      #assert MLOC n' == None ;;
      KLOC ← get K_loc k ;;
      #assert isSome KLOC as someKey ;;
      let k' := getSome KLOC someKey in
      if (b) then
       c' ← sample_C ;;
       #put (M_loc n m c) := setm MLOC (n') (m', c') ;;
       ret c'
      else
       c' ← enc m' k' n' ;;
       #put (M_loc n m c) := setm MLOC (n') (m', c') ;;
       ret c'
    } ;
    #def #[ DEC ] ('(c', n') : ('T c × 'T 'fin #|n|)) : ('T m) {
      KLOC ← get K_loc k ;;
      #assert (isSome KLOC) as someKey ;;
      let k' := getSome KLOC someKey in
      if (b) then
       MLOC ← get M_loc n m c ;;
       #assert isSome (MLOC n') as MC ;;
       let (m', c'') := getSome (MLOC n') MC in 
       ret m'
      else
       m' ← dec c' k' n' ;;
       ret m'
    }
  ].

End SAE.