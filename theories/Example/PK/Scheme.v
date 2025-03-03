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


Module PKScheme.

Record pk_scheme :=
  { Sec : choice_type
  ; Pub : choice_type
  ; Mes : choice_type
  ; Cip : choice_type
  ; sample_Cip : code fset0 [interface] Cip

  ; keygen :
      code fset0 [interface] (Sec × Pub)

  ; enc : ∀ (pk : Pub) (m : Mes),
      code fset0 [interface] Cip

  ; dec : ∀ (sk : Sec) (c : Cip),
      code fset0 [interface] Mes
  }.

Notation " 'sec p " := (Sec p)
  (in custom pack_type at level 2, p constr at level 20).

Notation " 'sec p " := (Sec p)
  (at level 3) : package_scope.

Notation " 'pub p " := (Pub p)
  (in custom pack_type at level 2, p constr at level 20).

Notation " 'pub p " := (Pub p)
  (at level 3) : package_scope.

Notation " 'mes p " := (Mes p)
  (in custom pack_type at level 2, p constr at level 20).

Notation " 'mes p " := (Mes p)
  (at level 3) : package_scope.

Notation " 'cip p " := (Cip p)
  (in custom pack_type at level 2, p constr at level 20).

Notation " 'cip p " := (Cip p)
  (at level 3) : package_scope.


Definition ENCDEC := 0%N.

Definition I_CORR (P : pk_scheme) :=
  [interface #val #[ ENCDEC ] : 'mes P → 'mes P ].

Definition CORR0 (P : pk_scheme) :
  game (I_CORR P) :=
  [module no_locs ;
    #def #[ ENCDEC ] (m : 'mes P) : ('mes P) {
      '(sk, pk) ← P.(keygen) ;;
      c ← P.(enc) pk m ;;
      m' ← P.(dec) sk c ;;
      ret m'
    }
  ].

Definition CORR1 (P : pk_scheme) :
  game (I_CORR P) :=
  [module no_locs ;
    #def #[ ENCDEC ] (m : 'mes P) : ('mes P) {
      ret m
    }
  ].

Definition CORR P b := if b then CORR0 P else CORR1 P.

Definition flag_loc : Location := ('option 'unit; 0%N).
Definition mpk_loc (P : pk_scheme) : Location := ('option ('pub P); 1%N).
Definition GET := 0%N.
Definition QUERY := 1%N.

Definition I_PK_OTSR (P : pk_scheme) :=
  [interface
    #val #[ GET ] : 'unit → 'pub P ;
    #val #[ QUERY ] : 'mes P → 'cip P
  ].

Definition PK_OTSR_loc (P : pk_scheme) :=
  fset [:: mpk_loc P ; flag_loc ].

Definition PK_OTSR0 (P : pk_scheme) :
  game (I_PK_OTSR P) :=
  [module PK_OTSR_loc P ;
    #def #[ GET ] (_ : 'unit) : ('pub P) {
      getNone (mpk_loc P) ;;
      '(_, pk) ← P.(keygen) ;;
      #put (mpk_loc P) := Some pk ;;
      ret pk
    } ;
    #def #[ QUERY ] (m : 'mes P) : ('cip P) {
      pk ← getSome (mpk_loc P) ;;
      getNone flag_loc ;;
      #put flag_loc := Some tt ;;
      P.(enc) pk m
    }
  ].

Definition PK_OTSR1 (P : pk_scheme) :
  game (I_PK_OTSR P) :=
  [module PK_OTSR_loc P ;
    #def #[ GET ] (_ : 'unit) : ('pub P) {
      getNone (mpk_loc P) ;;
      '(_, pk) ← P.(keygen) ;;
      #put (mpk_loc P) := Some pk ;;
      ret pk
    } ;
    #def #[ QUERY ] (m : 'mes P) : ('cip P) {
      pk ← getSome (mpk_loc P) ;;
      getNone flag_loc ;;
      #put flag_loc := Some tt ;;
      P.(sample_Cip)
    }
  ].
  
Definition PK_OTSR P b := if b then PK_OTSR0 P else PK_OTSR1 P.

End PKScheme.
