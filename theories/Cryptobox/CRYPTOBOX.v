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

From NominalSSP Require Import NIKE NBSES.
Import NIKE_scheme NBSES.

#[local] Open Scope package_scope.

Module crypto_box.

Record inj A B :=
  { encode  : A → B
  ; decode  : B → A
  ; cancels : cancel encode decode
  }.

Arguments encode {A} {B} _.
Arguments decode {A} {B} _.

Definition PKGEN := 31%N.
Definition PKENC := 32%N.
Definition PKDEC := 33%N.

Definition I_CRYPTOBOX_OUT (N : NIKE_scheme) (E : NBSES_scheme) :=
  [interface
    #val #[ PKGEN ]: 'unit → ('pk N × 'sk N) ;
    #val #[ PKENC ]: ((('sk N × 'pk N) × 'm E) × 'n E) → 'c E ;
    #val #[ PKDEC ]: ((('sk N × 'pk N) × 'c E) × 'n E) → 'm E 
].

Definition CRYPTOBOX (N : NIKE_scheme) (E : NBSES_scheme) (I : inj 'shared_key N 'k E):
  game (I_CRYPTOBOX_OUT N E) :=
  [module no_locs ;
    #def #[ PKGEN ] (_ : 'unit) : ('pk N × 'sk N) {
      '(PK, SK) ← N.(pkgen) ;;
      ret (PK, SK)
    } ;
    #def #[ PKENC ] ('(((SK, PK), m), n) : (('sk N × 'pk N) × 'm E) × 'n E) : ('c E) {
      K ← N.(sharedkey) PK SK ;;
      let k := I.(encode) K in
      C ← E.(enc) m k n ;;
      ret C
    } ;
    #def #[ PKDEC ] ('(((SK, PK), c), n) : (('sk N × 'pk N) × 'c E) × 'n E) : ('m E) {
      K ← N.(sharedkey) PK SK ;;
      let k := I.(encode) K in
      M ← E.(dec) c k n ;;
      ret M
    }
  ].

End crypto_box.
