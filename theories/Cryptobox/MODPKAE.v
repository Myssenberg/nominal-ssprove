(*This is a part of the implementation of the state-separated proof of security for the NaCl crypto_box public-key authenticated encryption scheme.
This file contains the specification for the MODPKAE module.*)

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

From NominalSSP Require Import Prelude Group.

From NominalSSP Require Import AE NBSES NIKE NBPES.
Import AE NBSES NIKE NBPES.

Import PackageNotation.

#[local] Open Scope package_scope.

Module MODPKAE.

Definition PKENC := 14%N.
Definition PKDEC := 15%N.


Definition I_MODPKAE_IN (N : NIKE_scheme) (E : NBSES_scheme) :=
  [interface
    [ SHAREDKEY ] : { ('F N.(NIKE.PK) × 'F N.(NIKE.PK)) ~> 'option 'unit } ; 
    [ ENC ]       : { ((('F N.(NIKE.PK) × 'F N.(NIKE.PK)) × E.(NBSES.M)) × 'F E.(NBSES.Nonce)) ~> E.(NBSES.C) } ; 
    [ DEC ]       : { ((('F N.(NIKE.PK) × 'F N.(NIKE.PK)) × E.(NBSES.C)) × 'F E.(NBSES.Nonce)) ~> E.(NBSES.M) }
].

Definition I_MODPKAE_OUT (N : NIKE_scheme) (E : NBSES_scheme) :=
[interface
    [ PKENC ]: { ((('F N.(NIKE.PK) × 'F N.(NIKE.PK)) × E.(NBSES.M)) × 'F E.(NBSES.Nonce)) ~> E.(NBSES.C) } ;
    [ PKDEC ]: { ((('F N.(NIKE.PK) × 'F N.(NIKE.PK)) × E.(NBSES.C)) × 'F E.(NBSES.Nonce)) ~> E.(NBSES.M) }
].


Definition SORT (N: NIKE_scheme) (PKs PKr : 'F N.(NIKE.PK)) : ('F N.(NIKE.PK) × 'F N.(NIKE.PK)) :=
  if (PKs < PKr) then (PKs, PKr) : (prod _ _) else (PKr, PKs) : (prod _ _).

Definition MODPKAE (N : NIKE_scheme) (E : NBSES_scheme):
  module (I_MODPKAE_IN N E) (I_MODPKAE_OUT N E) :=
  [module no_locs ; 
    [ PKENC ]: { ((('F N.(NIKE.PK) × 'F N.(NIKE.PK)) × E.(NBSES.M)) × 'F E.(NBSES.Nonce)) ~> E.(NBSES.C) } '(((PKs, PKr), m), n) {
      let sharedkey := #import [ SHAREDKEY ] : { ('F N.(NIKE.PK) × 'F N.(NIKE.PK)) ~> 'option 'unit } in
      let enc       := #import [ ENC ]       : { ((('F N.(NIKE.PK) × 'F N.(NIKE.PK)) × E.(NBSES.M)) × 'F E.(NBSES.Nonce)) ~> E.(NBSES.C) } in
      let dec       := #import [ DEC ]       : { ((('F N.(NIKE.PK) × 'F N.(NIKE.PK)) × E.(NBSES.C)) × 'F E.(NBSES.Nonce)) ~> E.(NBSES.M) } in
     
      let '(fst, snd) := SORT N PKs PKr in
      v ← sharedkey (PKs, PKr) ;;
      #assert v != None ;;
      C ← enc (fst, snd, m, n) ;;
      ret C
    } ;
    [ PKDEC ]: { ((('F N.(NIKE.PK) × 'F N.(NIKE.PK)) × E.(NBSES.C)) × 'F E.(NBSES.Nonce)) ~> E.(NBSES.M) } '(((PKs, PKr), c), n){
      let sharedkey := #import [ SHAREDKEY ] : { ('F N.(NIKE.PK) × 'F N.(NIKE.PK)) ~> 'option 'unit } in
      let enc       := #import [ ENC ]       : { ((('F N.(NIKE.PK) × 'F N.(NIKE.PK)) × E.(NBSES.M)) × 'F E.(NBSES.Nonce)) ~> E.(NBSES.C) } in
      let dec       := #import [ DEC ]       : { ((('F N.(NIKE.PK) × 'F N.(NIKE.PK)) × E.(NBSES.C)) × 'F E.(NBSES.Nonce)) ~> E.(NBSES.M) } in
      let '(fst, snd) := SORT N PKs PKr in      
      v ← sharedkey (PKs, PKr) ;;
      #assert v != None ;;
      M ← dec (fst, snd, c, n) ;;
      ret M
    }
  ].


End MODPKAE.