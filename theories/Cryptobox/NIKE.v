(*This is a part of the implementation of the state-separated game-based proof of security for the NaCl crypto_box authenticated encryption scheme.
This file contains the specification for a NIKE scheme*)

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

Module NIKE_scheme.

Record NIKE_scheme :=
  { PK             : finType ;
    PK_pos         : Positive #|PK|;
    SK             : finType ;
    SK_pos         : Positive #|SK|;
    Shared_Key     : finType ;
    Shared_Key_pos : Positive #|Shared_Key|;

    pkgen : 
      code fset0 [interface] ('fin #|PK| × 'fin #|SK|) ;

    sharedkey : forall (pk : PK) (sk : SK),
      code fset0 [interface] ('fin #|Shared_Key|) (*;
    
    kdist : *) (*currently have no clue how to represent kdist*)
  }.

Notation " 'pk n " := ('fin #|PK n|)
  (in custom pack_type at level 2, n constr at level 20).

Notation " 'pk n " := ('fin #|PK n|)
  (at level 3) : package_scope.

Notation " 'sk n " := ('fin #|SK n|)
  (in custom pack_type at level 2, n constr at level 20).

Notation " 'sk n " := ('fin #|SK n|)
  (at level 3) : package_scope.

Notation " 'shared_key n " := ('fin #|Shared_Key n|)
  (in custom pack_type at level 2, n constr at level 20).

Notation " 'shared_key n " := ('fin #|Shared_Key n|)
  (at level 3) : package_scope.


Instance pk_posi n : Positive #|PK n|.
Proof.
apply PK_pos. Defined.

Instance sk_posi n : Positive #|SK n|.
Proof.
apply SK_pos. Defined.

Instance sharedkey_posi n : Positive #|Shared_Key n|.
Proof.
apply Shared_Key_pos. Defined.



Definition PK_loc (N : NIKE_scheme): Location := (chMap 'pk N 'bool ; 0).

Definition SK_loc (N : NIKE_scheme): Location := (chMap 'pk N 'sk N ; 1).


Definition NIKE_locs_tt (N : NIKE_scheme):= fset [:: PK_loc N ; SK_loc N]. (*If they're using the same loc, can they share then because Nom-SSP will rename or do we get into trouble?*)
Definition NIKE_locs_ff (N : NIKE_scheme):= fset [:: PK_loc N ; SK_loc N].


Definition PKGEN := 2%N.
Definition SHAREDKEY := 3%N.


Definition I_GNIKE (N: NIKE_scheme) :=
  [interface
    #val #[ PKGEN ]: 'unit → ('pk N × 'sk N) ;
    #val #[ SHAREDKEY ]: ('pk N × 'sk N) → 'shared_key N
].


Definition GNIKE (N: NIKE_scheme) (b : 'bool) :
  game (I_GNIKE N) := .


End NIKE_scheme.