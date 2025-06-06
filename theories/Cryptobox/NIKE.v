(*This is a part of the implementation of the state-separated proof of security for the NaCl crypto_box public-key authenticated encryption scheme.
This file contains the specification for the NIKE scheme and the NIKE module.*)

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

Import PackageNotation.

From NominalSSP Require Import NBSES.

#[local] Open Scope package_scope.

Module NIKE.

Import NBSES.

Record NIKE_scheme :=
  { PK             : finType ;
    PK_pos         : Positive #|PK|;
    SK             : finType ;
    SK_pos         : Positive #|SK|;
    Shared_Key     : finType ; 
    Shared_Key_pos : Positive #|Shared_Key|; 

    pkgen : 
      code fset0 [interface] ('fin #|PK| × 'fin #|SK|) ;

    sharedkey : forall (pk : 'fin #|PK|) (sk : 'fin #|SK|),
      code fset0 [interface] ('fin #|Shared_Key|) ;
    
    kdist : 
      code fset0 [interface] 'fin #|Shared_Key| ;
  }.

Notation " 'F c " := 'fin #|c| (in custom pack_type at level 2, c constr at level 20).
Notation " 'F c " := 'fin #|c| (at level 2): package_scope.

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

Notation " 'SID n " := ('fin #|PK n| × 'fin #|PK n|) (in custom pack_type at level 2, n constr at level 20).
Notation " 'SID n " := ('fin #|PK n| × 'fin #|PK n|) (at level 2): package_scope.


Instance pk_posi n : Positive #|PK n|.
Proof.
apply PK_pos. Defined.

Instance sk_posi n : Positive #|SK n|.
Proof.
apply SK_pos. Defined.

Instance sharedkey_posi n : Positive #|Shared_Key n|.
Proof.
apply Shared_Key_pos. Defined.


Record inj A B :=
  { encode  : A → B
  ; decode  : B → A
  ; cancels : cancel encode decode
  }.

Arguments encode {A} {B} _.
Arguments decode {A} {B} _.


Definition GETSK := 4%N.
Definition HONPK := 5%N.
Definition SET := 27%N.
Definition CSET := 28%N.
Definition SHAREDKEY := 24%N.

Definition I_NIKE_IN (N: NIKE_scheme) :=
  [interface
    [ GETSK ] : { 'pk N ~> 'sk N } ;
    [ HONPK ] : { 'pk N ~> 'bool } ;
    [ SET ]   : { ('SID N × 'shared_key N) ~> 'nat } ;
    [ CSET ]  : { ('SID N × 'shared_key N) ~> 'unit }
].


Definition I_NIKE_OUT (N: NIKE_scheme) :=
  [interface
    [ SHAREDKEY ] : { ('pk N × 'pk N) ~> 'option 'unit }
].

Definition NIKE (N : NIKE_scheme):
  module (I_NIKE_IN N) (I_NIKE_OUT N) :=
  [module no_locs ; 
    [ SHAREDKEY ] : { ('pk N × 'pk N) ~> 'option 'unit } '(pks, pkr) { 
      let honpk := #import [ HONPK ] : { 'pk N ~> 'bool } in
      let getsk := #import [ GETSK ] : { 'pk N ~> 'sk N } in
      let set   := #import [ SET ]   : { ('SID N × 'shared_key N) ~> 'nat } in
      let cset  := #import [ CSET ]  : { ('SID N × 'shared_key N) ~> 'unit } in

      hs ← honpk pks ;;
      hr ← honpk pkr ;;
      
      sks ← getsk pks ;;
      shared_key ← N.(sharedkey) pkr sks ;;
      
      if (hs && hr) then
        let sid := (pks, pkr) in
          set (sid, shared_key) ;;

        ret (Some (Datatypes.tt : 'unit))
      else
        let sid := (pks, pkr) in
          cset (sid, shared_key) ;;
        ret (Some (Datatypes.tt : 'unit))
      
    }
  ].

End NIKE.