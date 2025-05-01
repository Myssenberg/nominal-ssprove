(*This is a part of the implementation of the state-separated game-based proof of security for the NaCl crypto_box authenticated encryption scheme.
This file contains the specification for a MODPKAE package*)

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

From NominalSSP Require Import AE NBSES NIKE PKAE.
Import AE NBSES NIKE_scheme NBPES_scheme.

Import PackageNotation.

#[local] Open Scope package_scope.

Module MODPKAE.

Record inji A B :=
  { encode  : A → B
  ; decode  : B → A
  ; cancels : cancel encode decode
  }.

Arguments encode {A} {B} _.
Arguments decode {A} {B} _.

Definition PKENC_MOD := 69%N.
Definition PKDEC_MOD := 70%N.

Notation " 'T c " := (c) (in custom pack_type at level 2, c constr at level 20).
Notation " 'T c " := (c) (at level 2): package_scope.

Definition I_MODPKAE_IN (N : NIKE_scheme) (E : NBSES_scheme) :=
  [interface
    #val #[ SHAREDKEY ]: ('T 'fin #|N.(NIKE_scheme.PK)| × 'T 'fin #|N.(NIKE_scheme.PK)|) → 'option 'unit ; 
    #val #[ ENC ]: ((('T 'fin #|N.(NIKE_scheme.PK)| × 'T 'fin #|N.(NIKE_scheme.PK)|) × 'T E.(NBSES.M)) × 'T 'fin #|E.(NBSES.Nonce)|) → 'T E.(NBSES.C) ; 
    #val #[ DEC ]: ((('T 'fin #|N.(NIKE_scheme.PK)| × 'T 'fin #|N.(NIKE_scheme.PK)|) × 'T E.(NBSES.C)) × 'T 'fin #|E.(NBSES.Nonce)|) → 'T E.(NBSES.M)
].

Definition I_MODPKAE_OUT (N : NIKE_scheme) (E : NBSES_scheme) :=
[interface
    #val #[ PKENC_MOD ]: ((('T 'fin #|N.(NIKE_scheme.PK)| × 'T 'fin #|N.(NIKE_scheme.PK)|) × 'T E.(NBSES.M)) × 'T 'fin #|E.(NBSES.Nonce)|) → 'T E.(NBSES.C) ; (*SHOULD COME FROM NBPES?*)
    #val #[ PKDEC_MOD ]: ((('T 'fin #|N.(NIKE_scheme.PK)| × 'T 'fin #|N.(NIKE_scheme.PK)|) × 'T E.(NBSES.C)) × 'T 'fin #|E.(NBSES.Nonce)|) → 'T E.(NBSES.M) (*SHOULD COME FROM NBPES?*)
].

Definition SORT (N: NIKE_scheme) (PKs PKr : 'T 'fin #|N.(NIKE_scheme.PK)|) : ('T 'fin #|N.(NIKE_scheme.PK)| × 'T 'fin #|N.(NIKE_scheme.PK)|) :=
  if (PKs < PKr) then (PKs, PKr) : (prod _ _) else (PKr, PKs) : (prod _ _).

Definition MODPKAE (N : NIKE_scheme) (E : NBSES_scheme):
  module (I_MODPKAE_IN N E) (I_MODPKAE_OUT N E) :=
  [module no_locs ; 
    #def #[ PKENC_MOD ] ('(((PKs, PKr), m), n) : (('T 'fin #|N.(NIKE_scheme.PK)| × 'T 'fin #|N.(NIKE_scheme.PK)|) × 'T E.(NBSES.M)) × 'T 'fin #|E.(NBSES.Nonce)|) : ('T E.(NBSES.C)) {
      #import {sig #[ SHAREDKEY ]: ('T 'fin #|N.(NIKE_scheme.PK)| × 'T 'fin #|N.(NIKE_scheme.PK)|) → 'option 'unit } as sharedkey ;;
      #import {sig #[ ENC ]: ((('T 'fin #|N.(NIKE_scheme.PK)| × 'T 'fin #|N.(NIKE_scheme.PK)|) × 'T E.(NBSES.M)) × 'T 'fin #|E.(NBSES.Nonce)|) → 'T E.(NBSES.C) } as enc ;;
      #import {sig #[ DEC ]: ((('T 'fin #|N.(NIKE_scheme.PK)| × 'T 'fin #|N.(NIKE_scheme.PK)|) × 'T E.(NBSES.C)) × 'T 'fin #|E.(NBSES.Nonce)|) → 'T E.(NBSES.M) } as dec ;;      
      let '(fst, snd) := SORT N PKs PKr in
      v ← sharedkey (PKs, PKr) ;;
      #assert v != None ;;
      C ← enc (fst, snd, m, n) ;;
      ret C
    } ;
    #def #[ PKDEC_MOD ] ('(((PKs, PKr), c), n) : (('T 'fin #|N.(NIKE_scheme.PK)| × 'T 'fin #|N.(NIKE_scheme.PK)|) × 'T E.(NBSES.C)) × 'T 'fin #|E.(NBSES.Nonce)|) : ('T E.(NBSES.M)) {
      #import {sig #[ SHAREDKEY ]: ('T 'fin #|N.(NIKE_scheme.PK)| × 'T 'fin #|N.(NIKE_scheme.PK)|) → 'option 'unit } as sharedkey ;;
      #import {sig #[ ENC ]: ((('T 'fin #|N.(NIKE_scheme.PK)| × 'T 'fin #|N.(NIKE_scheme.PK)|) × 'T E.(NBSES.M)) × 'T 'fin #|E.(NBSES.Nonce)|) → 'T E.(NBSES.C) } as enc ;;
      #import {sig #[ DEC ]: ((('T 'fin #|N.(NIKE_scheme.PK)| × 'T 'fin #|N.(NIKE_scheme.PK)|) × 'T E.(NBSES.C)) × 'T 'fin #|E.(NBSES.Nonce)|) → 'T E.(NBSES.M) } as dec ;;
      let '(fst, snd) := SORT N PKs PKr in      
      v ← sharedkey (PKs, PKr) ;;
      #assert v != None ;;
      M ← dec (fst, snd, c, n) ;;
      ret M
    }
  ].

Definition I_MODPKAE_OUT_F (F : NBPES_scheme) :=
[interface
    #val #[ PKENC_MOD ]: ((('pk F × 'pk F) × 'm F) × 'n F) → 'c F ;
    #val #[ PKDEC_MOD ]: ((('pk F × 'pk F) × 'c F) × 'n F) → 'm F
].

Definition MODPKAE_F (N : NIKE_scheme) (E : NBSES_scheme) (F : NBPES_scheme) (A : inji 'pk F 'T 'fin #|N.(NIKE_scheme.PK)|) (B : inji 'm F 'T E.(NBSES.M)) (C : inji 'n F 'T 'fin #|E.(NBSES.Nonce)|) (D : inji 'c F 'T E.(NBSES.C)) :
  module (I_MODPKAE_IN N E) (I_MODPKAE_OUT_F F) :=
  [module no_locs ; 
    #def #[ PKENC_MOD ] ('(((PKs, PKr), m), n) : (('pk F × 'pk F) × 'm F) × 'n F) : ('c F) {
      #import {sig #[ SHAREDKEY ]: ('T 'fin #|N.(NIKE_scheme.PK)| × 'T 'fin #|N.(NIKE_scheme.PK)|) → 'option 'unit } as sharedkey ;;
      #import {sig #[ ENC ]: ((('T 'fin #|N.(NIKE_scheme.PK)| × 'T 'fin #|N.(NIKE_scheme.PK)|) × 'T E.(NBSES.M)) × 'T 'fin #|E.(NBSES.Nonce)|) → 'T E.(NBSES.C) } as enc ;;      
      let pks := A.(encode) PKs in
      let pkr := A.(encode) PKr in  
      let m' := B.(encode) m in   
      let n' := C.(encode) n in    
      let '(fst, snd) := SORT N pks pkr in
      v ← sharedkey (pks, pkr) ;;
      #assert v != None ;;
      C ← enc (fst, snd, m', n') ;;
      let c' := D.(decode) C in
      ret c'
    } ;
    #def #[ PKDEC_MOD ] ('(((PKs, PKr), c), n) : (('pk F × 'pk F) × 'c F) × 'n F) : ('m F) {
      #import {sig #[ SHAREDKEY ]: ('T 'fin #|N.(NIKE_scheme.PK)| × 'T 'fin #|N.(NIKE_scheme.PK)|) → 'option 'unit } as sharedkey ;;
      #import {sig #[ ENC ]: ((('T 'fin #|N.(NIKE_scheme.PK)| × 'T 'fin #|N.(NIKE_scheme.PK)|) × 'T E.(NBSES.M)) × 'T 'fin #|E.(NBSES.Nonce)|) → 'T E.(NBSES.C) } as enc ;;
      #import {sig #[ DEC ]: ((('T 'fin #|N.(NIKE_scheme.PK)| × 'T 'fin #|N.(NIKE_scheme.PK)|) × 'T E.(NBSES.C)) × 'T 'fin #|E.(NBSES.Nonce)|) → 'T E.(NBSES.M) } as dec ;;
      let pks := A.(encode) PKs in
      let pkr := A.(encode) PKr in  
      let c' := D.(encode) c in
      let n' := C.(encode) n in
      let '(fst, snd) := SORT N pks pkr in      
      v ← sharedkey (pks, pkr) ;;
      #assert v != None ;;
      M ← dec (fst, snd, c', n') ;;
      let m' := B.(decode) M in
      ret m'
    }
  ].

End MODPKAE.