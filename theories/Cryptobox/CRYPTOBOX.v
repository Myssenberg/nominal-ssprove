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

From NominalSSP Require Import NIKE NBSES GPKAE GMODPKAE GAE MODPKAE AE GNIKE NIKE PKEY KEY PKAE GSAE GH HYBRID.

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

(*perfect definition from Markus' branch*)
Definition perfect I G G' :=
  ∀ LA (A : raw_module) (VA : ValidPackage LA I A_export A), Adv G G' A = 0.

Lemma Equiv_GuPKAE_GMODPKAE (P : NBPES_scheme.NBPES_scheme) (N : NIKE_scheme.NIKE_scheme) (E : NBSES.NBSES_scheme) (I : NIKE_scheme.inj ('fin #|NIKE_scheme.Shared_Key N|) ('fin #|NBSES.Shared_Key E|)) (I_cb : CB_inj ('fin #|N.(NIKE_scheme.Shared_Key)|) ('fin #|E.(NBSES.Shared_Key)|)) (b : 'bool):
perfect (GPKAE.I_GPKAE_OUT (CRYPTOBOX_scheme N E I_cb)) (GPKAE.GuPKAE (CRYPTOBOX_scheme N E I_cb) b) (GMODPKAE.GMODPKAE E N I b).
Proof.
unfold GPKAE.GuPKAE, GMODPKAE.GMODPKAE. (*nssprove_share.*) apply prove_perfect.
intros.
Admitted.

Instance sharedkey_posi n : Positive #|NIKE_scheme.Shared_Key n|.
Proof.
Admitted.

Instance k_posi e : Positive #|NBSES.Shared_Key e|.
Proof.
Admitted.

Search package.

(*
Lemma Equiv_GuPKAE_GMODPKAE_1 (N : NIKE_scheme.NIKE_scheme) (E : NBSES.NBSES_scheme) (I : NIKE_scheme.inj ('fin #|NIKE_scheme.Shared_Key N|) ('fin #|NBSES.Shared_Key E|)) (I_cb : CB_inj ('fin #|N.(NIKE_scheme.Shared_Key)|) ('fin #|E.(NBSES.Shared_Key)|)):
(GPKAE.GuPKAE (CRYPTOBOX_scheme N E I_cb) false) ≈₀ (GMODPKAE.GMODPKAE E N I false).
Proof.*)

Class Trimmed (E : Interface) (p : raw_module) := tr : trimmed E p.

Arguments tr {_ _} _.


Notation "{ 'adversary' I ; m }" :=
  (@Build_module I A_export (loc m%sep) (mkpackage m%sep _) (_))
  (only parsing) : sep_scope.

(* #[tactic=idtac] Equations? A4 (P : NBPES_scheme.NBPES_scheme) (N : NIKE_scheme.NIKE_scheme) (A : adversary (GPKAE.I_GPKAE_OUT P)) : adversary (GNIKE.I_GNIKE_OUT N) := 
A4 P N A := Build_module _ (@mkpackage _ _ _ _ _) _.
Proof.
eapply Build_module. *)

Local Obligation Tactic := idtac.
Program Definition A4 (P : NBPES_scheme.NBPES_scheme) (N : NIKE_scheme.NIKE_scheme) (E : NBSES.NBSES_scheme) (I : NIKE_scheme.inj ('fin #|N.(NIKE_scheme.Shared_Key)|) ('fin #|E.(NBSES.Shared_Key)|)) (A : adversary (GPKAE.I_GPKAE_OUT P))
  : adversary (GNIKE.I_GNIKE_OUT N) :=
  {adversary _ ; ((A ∘ (ID (GMODPKAE.I_GMODPKAE_ID_COMP N) || ((MODPKAE.MODPKAE N E) ∘ ((ID (NIKE_scheme.I_NIKE_OUT N) || AE.AE E N false)))) ∘ ((PKEY.PKEY (PKEY.NIKE_to_GEN N) true || KEY.KEY N (KEY.NBSES_to_SGEN E) false)))) }.
Obligation 1. intros. nssprove_valid. Admitted.


(* (ID (I_GMODPKAE_ID_COMP N) || ((MODPKAE N E) ∘ ((NIKE_E N E I || AE E N false)))) ∘ ((PKEY (NIKE_to_GEN N) true || KEY N (NBSES_to_SGEN E) false)) *)

Theorem Lemma4_Adv_GuPKAE_CB {P} {N} {E} (A : adversary (GPKAE.I_GPKAE_OUT P)) (I : NIKE_scheme.inj ('fin #|N.(NIKE_scheme.Shared_Key)|) ('fin #|E.(NBSES.Shared_Key)|)) (I_cb : CB_inj ('fin #|N.(NIKE_scheme.Shared_Key)|) ('fin #|E.(NBSES.Shared_Key)|)):
  AdvFor (GPKAE.GuPKAE (CRYPTOBOX_scheme N E I_cb)) A
  <= AdvFor (GNIKE.GuNIKE N) (A ∘ (ID (GMODPKAE.I_GMODPKAE_ID_COMP N) || ((MODPKAE.MODPKAE N E) ∘ ((ID (NIKE_scheme.I_NIKE_OUT N) || AE.AE E N false))))) ∘ ((PKEY (NIKE_to_GEN N) true || KEY N (NBSES_to_SGEN E) false))
     +
     AdvFor (GAE.GAE E N) (A ∘ (ID (GMODPKAE.I_GMODPKAE_ID_COMP N) || ((MODPKAE.MODPKAE N E) ∘ ((NIKE_scheme.NIKE_E N E I || ID (AE.I_AE_OUT E N))))) ∘ ((PKEY.PKEY (PKEY.NIKE_to_GEN N) true || ID (KEY.I_KEY_OUT N (KEY.NBSES_to_SGEN E))))).
Proof.
(*rewrite <- Equiv_GuPKAE_GMODPKAE.*)
unfold GPKAE.GuPKAE, GNIKE.GuNIKE, GAE.GAE, GMODPKAE.GMODPKAE, AdvFor.
Admitted.


(* Theorem Lemma4_Adv_GuPKAE_CB {P} {N} {E} (A : adversary (GPKAE.I_GPKAE_OUT P)) (I_cb : CB_inj ('fin #|N.(NIKE_scheme.Shared_Key)|) ('fin #|E.(NBSES.Shared_Key)|)):
  AdvFor (GPKAE.GuPKAE (CRYPTOBOX_scheme N E I_cb)) A
  <= AdvFor (GNIKE.GuNIKE N) A
     +
     AdvFor (GAE.GAE E N) A.
Proof.
unfold AdvFor.
(*erewrite (Adv_perf_r (Equiv_GuPKAE_GMODPKAE)).*)
unfold GPKAE.GuPKAE, GNIKE.GuNIKE, GAE.GAE, GMODPKAE.GMODPKAE, AdvFor.
Admitted. *)


Theorem Cryptobox_Security {N} {E} (I_cb : CB_inj ('fin #|N.(NIKE_scheme.Shared_Key)|) ('fin #|E.(NBSES.Shared_Key)|)) (A1 : adversary (GPKAE.I_GPKAE_OUT (CRYPTOBOX_scheme N E I_cb))) (A2 : adversary (GAE.I_GAE_OUT E N)) qset :
let P := (CRYPTOBOX_scheme N E I_cb) in
  AdvFor (GPKAE.GPKAE (CRYPTOBOX_scheme N E I_cb)) A1
  <=
  AdvFor (PKEY.PKEY (PKEY.NBPES_to_GEN P)) (A1 ∘ (NBPES_scheme.PKAE P false || ID (GPKAE.I_GPKAE_ID_COMP P)))
  +
  AdvFor (PKEY.PKEY (PKEY.NBPES_to_GEN P)) (A1 ∘ (NBPES_scheme.PKAE P true || ID (GPKAE.I_GPKAE_ID_COMP P)))
  +
  AdvFor (PKEY.PKEY (PKEY.NIKE_to_GEN N)) (A1 ∘ (NIKE_scheme.NIKE N || ID (GNIKE.I_GNIKE_ID_COMP N)) ∘ (KEY.KEY N (KEY.NIKE_to_SGEN N) false || ID (PKEY.I_PKEY_OUT (PKEY.NIKE_to_GEN N))))
  +
  AdvFor (PKEY.PKEY (PKEY.NIKE_to_GEN N)) (A1 ∘ (NIKE_scheme.NIKE N || ID (GNIKE.I_GNIKE_ID_COMP N)) ∘ (KEY.KEY N (KEY.NIKE_to_SGEN N) true || ID (PKEY.I_PKEY_OUT (PKEY.NIKE_to_GEN N))))
  +
  AdvFor (GNIKE.GNIKE N) (A1 ∘ (ID (GMODPKAE.I_GMODPKAE_ID_COMP N) || ((MODPKAE.MODPKAE N E) ∘ ((ID (NIKE_scheme.I_NIKE_OUT N) || AE.AE E N false)))) ∘ ((ID (PKEY.I_PKEY_OUT (PKEY.NIKE_to_GEN N)) || ID (KEY.I_KEY_OUT N (KEY.NBSES_to_SGEN E)))))
  +
  \sum_(1 <= i < qset)
   ( AdvFor (GSAE.GSAE E) (A2 ∘ (HYBRID.HYBRID E N i qset) ∘ (AE.AE E N true || ID (GH.I_GH_ID_COMP E N)) ∘ (KEY.KEY N (KEY.NBSES_to_SGEN E) true)) + 
     AdvFor (GSAE.GSAE E) (A2 ∘ (HYBRID.HYBRID E N i qset) ∘ (AE.AE E N false|| ID (GH.I_GH_ID_COMP E N)) ∘ (KEY.KEY N (KEY.NBSES_to_SGEN E) true))).
Proof.
eapply le_trans.
- apply GPKAE.Corollary1_Adv_GPKAE.
- repeat rewrite <- GRing.addrA. apply lerD.
--  done.
-- (*never repeat this one - it will keep switching*) rewrite -> GRing.addrC. apply lerD.
--- done.
--- rewrite GRing.addrA. eapply le_trans.
---- apply Lemma4_Adv_GuPKAE_CB.
---- rewrite GRing.addrA. apply lerD.
----- (*pose (A3 := {adversary I_GNIKE_OUT N ; _ }).*) pose (A3 := (A1
   ∘ (ID (GMODPKAE.I_GMODPKAE_ID_COMP N)
      || MODPKAE.MODPKAE N E ∘ (ID (NIKE_scheme.I_NIKE_OUT N) || AE.AE E N false))
     ∘ (ID (PKEY.I_PKEY_OUT (PKEY.NIKE_to_GEN N))
        || ID (KEY.I_KEY_OUT N (KEY.NBSES_to_SGEN E))))%sep).
      assert (ValidPackage A3.(loc) (GNIKE.I_GNIKE_OUT N) A_export A3).
------ unfold A3. nssprove_valid.
      apply GNIKE.Corollary3_Adv_GNIKE_GuNIKE.
----- About GH.Lemma3_Adv_GAE. eapply GH.Lemma3_Adv_GAE.

nssprove_eadv_trans.
apply lerD. About lerD. About GH.Lemma3_Adv_GAE.

Search "Adv".
About Order.le_trans.
apply Advantage_triangle_chain.
apply GH.Lemma3_Adv_GAE.

(*eapply (@GPKAE.Corollary1_Adv_GPKAE (CRYPTOBOX_scheme N E I_cb) A).*)

End crypto_box.
