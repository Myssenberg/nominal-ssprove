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

Import Num.Def.
Import Num.Theory.
Import Order.POrderTheory.

From NominalSSP Require Import PK.DDH PK.Scheme.

From NominalSSP Require Import Prelude Group Misc.
Import PackageNotation.

From NominalSSP Require Import NIKE NBSES GPKAE GMODPKAE GAE MODPKAE AE GNIKE NIKE PKEY KEY PKAE Scheme.

#[local] Open Scope package_scope.
#[local] Open Scope ring_scope.

Module crypto_box.

(*Record SE_scheme :=
  { Shared_Key     : finType ;
    Shared_Key_pos : Positive #|Shared_Key|;
    M        : choice_type ;
    C        : choice_type ;
    sample_C : code fset0 [interface] C ;

   pkgen : 
      code fset0 [interface] ('fin #|PK| × 'fin #|SK|) ;

   enc : forall (sk : 'fin #|SK|) (pk : 'fin #|PK|) (m : M) (n : 'fin #|Nonce|),
      code fset0 [interface] C ;

   dec : forall (sk : 'fin #|SK|) (pk : 'fin #|PK|) (c : C) (n : 'fin #|Nonce|),
      code fset0 [interface] M 
  }.*)


Record CB_inj A B :=
  { encode  : A → B
  ; decode  : B → A
  ; cancels : cancel encode decode
  }.

Arguments encode {A} {B} _.
Arguments decode {A} {B} _.


Notation " 'T c " := (c) (in custom pack_type at level 2, c constr at level 20).
Notation " 'T c " := (c) (at level 2): package_scope.


Definition CRYPTOBOX_scheme (N: NIKE_scheme.NIKE_scheme) (E : NBSES.NBSES_scheme) (I : CB_inj ('fin #|N.(NIKE_scheme.Shared_Key)|) ('fin #|E.(NBSES.Shared_Key)|)): NBPES_scheme.NBPES_scheme := {|
    NBPES_scheme.PK       := N.(NIKE_scheme.PK) ;
    NBPES_scheme.SK       := N.(NIKE_scheme.SK) ;
    NBPES_scheme.Nonce    := E.(NBSES.Nonce) ;
    NBPES_scheme.M        := E.(NBSES.M) ;
    NBPES_scheme.C        := E.(NBSES.C) ;
    NBPES_scheme.sample_C := E.(NBSES.sample_C) ;

    NBPES_scheme.pkgen :=  
      {code
        '(pk, sk) ← N.(NIKE_scheme.pkgen) ;;
        ret (pk, sk)
      } ;

    NBPES_scheme.enc := λ sk pk m n,
      {code
        K ← N.(NIKE_scheme.sharedkey) pk sk ;;
        let k := I.(encode) K in
        C ← E.(NBSES.enc) m k n ;;
        ret C} ;


    NBPES_scheme.dec := λ sk pk c n,
      {code
        K ← N.(NIKE_scheme.sharedkey) pk sk ;;
        let k := I.(encode) K in
        M ← E.(NBSES.dec) c k n ;;
        ret M
      }
|}.

Check adv_equiv.

Definition perfect I G G' :=
  ∀ LA (A : raw_module) (VA : ValidPackage LA I A_export A), Adv G G' A = 0.

Lemma Equiv_GuPKAE_GMODPKAE (P : NBPES_scheme.NBPES_scheme) (N : NIKE_scheme.NIKE_scheme) (E : NBSES.NBSES_scheme) (I : NIKE_scheme.inj ('fin #|NIKE_scheme.Shared_Key N|) ('fin #|NBSES.Shared_Key E|)) (b : 'bool):
perfect (GPKAE.I_GPKAE_OUT P) (GPKAE.GuPKAE P b) (GMODPKAE.GMODPKAE E N I b).
Proof.
unfold perfect, GPKAE.GuPKAE, GMODPKAE.GMODPKAE.
intros.
Admitted.


Theorem Lemma4_Adv_GuPKAE_CB {P} {N} {E} (A : adversary (GPKAE.I_GPKAE_OUT P)) (I : NIKE_scheme.inj ('fin #|N.(NIKE_scheme.Shared_Key)|) ('fin #|E.(NBSES.Shared_Key)|)) (I_cb : CB_inj ('fin #|N.(NIKE_scheme.Shared_Key)|) ('fin #|E.(NBSES.Shared_Key)|)):
  AdvFor (GPKAE.GuPKAE (CRYPTOBOX_scheme N E I_cb)) A
  <= AdvFor (GNIKE.GuNIKE N) (A ∘ (ID (GMODPKAE.I_GMODPKAE_ID_COMP N) || ((MODPKAE.MODPKAE N E) ∘ ((ID (NIKE_scheme.I_NIKE_OUT N) || AE.AE E N false)))) ∘ ((ID (PKEY.I_PKEY_OUT (PKEY.NIKE_to_GEN N)) || ID (KEY.I_KEY_OUT N (KEY.NBSES_to_SGEN E)))))
     +
     AdvFor (GAE.GAE E N) (A ∘ (ID (GMODPKAE.I_GMODPKAE_ID_COMP N) || ((MODPKAE.MODPKAE N E) ∘ ((NIKE_scheme.NIKE_E N E I || ID (AE.I_AE_OUT E N))))) ∘ ((PKEY.PKEY (PKEY.NIKE_to_GEN N) true || ID (KEY.I_KEY_OUT N (KEY.NBSES_to_SGEN E))))).
Proof.
(*rewrite <- Equiv_GuPKAE_GMODPKAE.*)
unfold GPKAE.GuPKAE, GNIKE.GuNIKE, GAE.GAE, GMODPKAE.GMODPKAE, AdvFor.
Admitted.


End crypto_box.
