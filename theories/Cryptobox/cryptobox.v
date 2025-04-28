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
    #val #[ PKENC ]: ((('sk N × 'pk N) × 'm E) × 'n E) → 'c E (*;
    #val #[ PKDEC ]: ((('sk N × 'pk N) × 'c E) × 'n E) → 'm E*) 
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
    }
  ].

(*
Definition I_CRYPTOBOX_OUT (N : NIKE_scheme) (E : NBSES_scheme) :=
  [interface
    #val #[ PKGEN ]: 'unit → ('pk N × 'sk N) ;
    #val #[ PKENC ]: ((('sk N × 'pk N) × 'm E) × 'n E) → 'c E (*;
    #val #[ PKDEC ]: ((('sk N × 'pk N) × 'c E) × 'n E) → 'm E*) 
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
      C ← E.(enc) m K n ;;
      ret C
    }
  ].
*)

(*Record crypto_box_scheme :=
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

Lemma PK_coll_bound:
  forall (A : adversary [interface]),
  AdvFor GPKAE A <=
  AdvFor GPKAE A.
Proof.

*)
End crypto_box.