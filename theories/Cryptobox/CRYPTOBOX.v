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

From NominalSSP Require Import Prelude Group.
Import PackageNotation.

From NominalSSP Require Import NIKE NBSES GPKAE GMODPKAE GAE MODPKAE AE GNIKE NIKE PKEY KEY PKAE GSAE GH HYBRID.

Require Import GMODPKAE.

#[local] Open Scope package_scope.
#[local] Open Scope ring_scope.

Module crypto_box.

#[export] Hint Unfold GMODPKAE.I_GMODPKAE_OUT GMODPKAE.I_GMODPKAE_ID_COMP MODPKAE.I_MODPKAE_OUT MODPKAE.I_MODPKAE_IN NIKE_scheme.I_NIKE_OUT NIKE_scheme.I_NIKE_IN AE.I_AE_OUT AE.I_AE_IN PKEY.I_PKEY_OUT KEY.I_KEY_OUT GPKAE.I_GPKAE_OUT GPKAE.I_GPKAE_ID_COMP NBPES_scheme.I_PKAE_OUT NBPES_scheme.I_PKAE_IN GNIKE.I_GNIKE_OUT: in_fset_eq.


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

Instance sharedkey_posi n : Positive #|NIKE_scheme.Shared_Key n|.
Proof.
Admitted.

Instance k_posi e : Positive #|NBSES.Shared_Key e|.
Proof.
Admitted.

Local Obligation Tactic := idtac.

Context (N : NIKE_scheme.NIKE_scheme) (E : NBSES.NBSES_scheme) (I_cb : CB_inj ('fin #|N.(NIKE_scheme.Shared_Key)|) ('fin #|E.(NBSES.Shared_Key)|)) (I : NIKE_scheme.inj ('fin #|N.(NIKE_scheme.Shared_Key)|) ('fin #|E.(NBSES.Shared_Key)|)).
Let P := (CRYPTOBOX_scheme N E I_cb).

Lemma Equiv_GuPKAE_GMODPKAE (b : 'bool):
perfect (GPKAE.I_GPKAE_OUT P) (GPKAE.GuPKAE P b) (GMODPKAE.GMODPKAE E N I b).
Proof.
unfold GPKAE.GuPKAE, GMODPKAE.GMODPKAE, P.
nssprove_share.
- eapply prove_perfect.
  apply (eq_rel_perf_ind_eq).
  simplify_eq_rel x.
  -- ssprove_code_simpl.
  simplify_linking.
  unfold par.
  ssprove_code_simpl.
  simpl.
  rewrite unionmE.
  simpl.
Admitted.


Program Definition ANIKE (A : adversary (GPKAE.I_GPKAE_OUT (CRYPTOBOX_scheme N E I_cb))) : adversary (GNIKE.I_GNIKE_OUT N) :=
  {adversary _ ; ((A ∘ (ID (GMODPKAE.I_GMODPKAE_ID_COMP N) || ((MODPKAE.MODPKAE N E) ∘ ((ID (NIKE_scheme.I_NIKE_OUT N) || AE.AE E N I false)))))) }.
Obligation 1. intros. nssprove_valid. Qed.

Program Definition A4   (A : adversary (GPKAE.I_GPKAE_OUT P)) : adversary (GNIKE.I_GNIKE_OUT N) :=
  {adversary _ ; (A ∘ (ID (GMODPKAE.I_GMODPKAE_ID_COMP N) || ((MODPKAE.MODPKAE N E) ∘ ((ID (NIKE_scheme.I_NIKE_OUT N) || AE.AE E N I false))))) }.
Obligation 1. intros. unfold P in A. nssprove_valid. Qed.

(* Program Definition A5   (A : adversary (GPKAE.I_GPKAE_OUT P)) : adversary (GAE.I_GAE_OUT E N) :=
  {adversary _ ; (A ∘ (ID (GMODPKAE.I_GMODPKAE_ID_COMP N) || ((MODPKAE.MODPKAE N E) ∘ ((NIKE_scheme.NIKE N || ID (AE.I_AE_OUT E N))))) ∘ ((PKEY.PKEY (PKEY.NIKE_to_GEN N) true || ID (KEY.I_KEY_OUT N)))) }.
Obligation 1. intros. unfold P in A. nssprove_valid. - fset_solve. Qed. *)

Theorem Lemma4_Adv_GuPKAE_CB (* {P} *) (* {N} {E} *) (A : adversary (GPKAE.I_GPKAE_OUT P)):
  AdvFor (GPKAE.GuPKAE P) A
  <= AdvFor (GNIKE.GuNIKE N) (A ∘ (ID (GMODPKAE.I_GMODPKAE_ID_COMP N) || ((MODPKAE.MODPKAE N E) ∘ ((ID (NIKE_scheme.I_NIKE_OUT N) || AE.AE E N I false)))))
     +
     AdvFor (GAE.GAE E N I) (A ∘ (ID (GMODPKAE.I_GMODPKAE_ID_COMP N) || ((MODPKAE.MODPKAE N E) ∘ ((NIKE_scheme.NIKE N || ID (AE.I_AE_OUT E N))))) ∘ ((PKEY.PKEY (PKEY.NIKE_to_GEN N) true || ID (KEY.I_KEY_OUT N)))).
Proof.
unfold P.
unfold P in A.
erewrite (AdvFor_perfect (Equiv_GuPKAE_GMODPKAE)).
unfold GPKAE.GuPKAE, GNIKE.GuNIKE, GAE.GAE, GMODPKAE.GMODPKAE, AdvFor.
Admitted.

Theorem Cryptobox_Security (* {N} {E} *) (A1 : adversary (GPKAE.I_GPKAE_OUT P)) qset :
(* let P := (CRYPTOBOX_scheme N E I_cb) in *)
  AdvFor (GPKAE.GPKAE P) A1
  <=
  AdvFor (PKEY.PKEY (PKEY.NBPES_to_GEN P)) (A1 ∘ (NBPES_scheme.PKAE P false || ID (GPKAE.I_GPKAE_ID_COMP P)))
  +
  AdvFor (PKEY.PKEY (PKEY.NBPES_to_GEN P)) (A1 ∘ (NBPES_scheme.PKAE P true || ID (GPKAE.I_GPKAE_ID_COMP P)))
  +
  AdvFor (PKEY.PKEY (PKEY.NIKE_to_GEN N)) (((A4 A1) ∘ (NIKE_scheme.NIKE N || ID (GNIKE.I_GNIKE_ID_COMP N))) ∘ (KEY.KEY N false || ID (PKEY.I_PKEY_OUT (PKEY.NIKE_to_GEN N))))
  +
  AdvFor (GNIKE.GNIKE N) (A4 A1)
  +
  AdvFor (PKEY.PKEY (PKEY.NIKE_to_GEN N)) (((A4 A1) ∘ (NIKE_scheme.NIKE N || ID (GNIKE.I_GNIKE_ID_COMP N))) ∘ (KEY.KEY N true || ID (PKEY.I_PKEY_OUT (PKEY.NIKE_to_GEN N))))
  +
  \sum_(1 <= i < qset)
   ( AdvFor (GSAE.GSAE E) (A1 ∘ (HYBRID.HYBRID E N I i qset) ∘ (AE.AE E N I true || ID (GH.I_GH_ID_COMP N)) ∘ (KEY.KEY N true)) + 
     AdvFor (GSAE.GSAE E) (A1 ∘ (HYBRID.HYBRID E N I i qset) ∘ (AE.AE E N I false|| ID (GH.I_GH_ID_COMP N)) ∘ (KEY.KEY N true))).
Proof.
unfold P in A1.
unfold P.
eapply le_trans.
- apply GPKAE.Corollary1_Adv_GPKAE.
- repeat rewrite <- GRing.addrA. apply lerD.
--  done.
-- (*never repeat this one - it will keep switching*) rewrite -> GRing.addrC. apply lerD.
--- done.
--- rewrite GRing.addrA. eapply le_trans.
---- apply Lemma4_Adv_GuPKAE_CB.
---- rewrite GRing.addrA. apply lerD.
------ 1: apply (GNIKE.Corollary3_Adv_GNIKE_GuNIKE (A4 A1)).
------ (* eapply (@GNIKE.Corollary3_Adv_GNIKE_GuNIKE (N) (A4 A1)). *)

End crypto_box.
