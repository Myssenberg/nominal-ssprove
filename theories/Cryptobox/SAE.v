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

(*Definition M_loc (E: NBSES_scheme): Location := (chMap 'n E ('m E × 'c E) ; 0). *)
Definition M_loc (n : choice_type) (m : choice_type) (c : choice_type) : Location := (chMap n (m × c) ; 0).
Definition K_loc (k : choice_type) : Location := ('option k ; 1).

(*Definition SAE_locs_tt (E : NBSES_scheme):= fset [::  M_loc E]. (*If they're using the same loc, can they share then because Nom-SSP will rename or do we get into trouble?*)
Definition SAE_locs_ff (E : NBSES_scheme):= fset [::  M_loc E].*)
Definition SAE_locs_tt (k : choice_type) (n : choice_type) (m : choice_type) (c : choice_type) := fset [::  M_loc n m c ; K_loc k]. (*If they're using the same loc, can they share then because Nom-SSP will rename or do we get into trouble?*)
Definition SAE_locs_ff (k : choice_type) (n : choice_type) (m : choice_type) (c : choice_type) := fset [::  M_loc n m c ; K_loc k]. (*If they're using the same loc, can they share then because Nom-SSP will rename or do we get into trouble?*)

Definition GEN := 2%N.
Definition ENC := 3%N.
Definition DEC := 4%N.

Definition I_SAE_OUT (k : choice_type) (n : choice_type) (m : choice_type) (c : choice_type) :=
  [interface
    #val #[ GEN ]: 'unit → 'unit (*;    
    #val #[ ENC ]: ('T m × 'T n) → 'T c ;
    #val #[ DEC ]: ('T c × 'T n) → 'T m*) 
].

Definition SAE (k : choice_type) (n : choice_type) (m : choice_type) (c : choice_type) (b : bool) (sample_K : code fset0 [interface] k) :
  game (I_SAE_OUT k n m c)  := 
  [module SAE_locs_tt k n m c ;
    #def #[ GEN ] (_ : 'unit) : ('unit) {
      KLOC ← get K_loc k ;;
      match KLOC with
      | None =>
        k' ← sample_K ;;
        #put (K_loc k) := Some k' ;;
        ret (Datatypes.tt : 'unit)
      | Some k' => ret (Datatypes.tt : 'unit)
      end
    }
  ].

End SAE.