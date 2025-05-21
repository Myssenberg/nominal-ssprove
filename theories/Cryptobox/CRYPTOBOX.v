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

From NominalSSP Require Import NIKE NBSES NBPES GPKAE GMODPKAE GAE MODPKAE AE GNIKE NIKE PKEY KEY PKAE GSAE GH HYBRID.

Require Import GMODPKAE.
Import NIKE NBSES NBPES GPKAE GMODPKAE GAE MODPKAE AE GNIKE NIKE PKEY KEY PKAE GSAE GH HYBRID.

#[local] Open Scope package_scope.
#[local] Open Scope ring_scope.

Module crypto_box.

#[export] Hint Unfold I_GMODPKAE_OUT I_GMODPKAE_ID_COMP I_MODPKAE_OUT I_MODPKAE_IN I_NIKE_OUT I_NIKE_IN I_AE_OUT I_AE_IN I_PKEY_OUT I_KEY_OUT I_GPKAE_OUT I_GPKAE_ID_COMP I_PKAE_OUT I_PKAE_IN I_GNIKE_OUT I_GNIKE_ID_COMP I_GAE_OUT I_GAE_ID_COMP : in_fset_eq.


Definition CRYPTOBOX_scheme (N: NIKE_scheme) (E : NBSES_scheme) (I : inj ('F N.(NIKE.Shared_Key)) ('F E.(NBSES.Shared_Key))): NBPES_scheme := {|
    NBPES.PK       := N.(NIKE.PK) ;
    NBPES.SK       := N.(NIKE.SK) ;
    NBPES.Nonce    := E.(NBSES.Nonce) ;
    NBPES.M        := E.(NBSES.M) ;
    NBPES.C        := E.(NBSES.C) ;
    NBPES.sample_C := E.(NBSES.sample_C) ;

    NBPES.pkgen :=  
      {code
        '(pk, sk) ← N.(NIKE.pkgen) ;;
        ret (pk, sk)
      } ;

    NBPES.enc := λ sk pk m n,
      {code
        K ← N.(NIKE.sharedkey) pk sk ;;
        let k := I.(encode) K in
        C ← E.(NBSES.enc) m k n ;;
        ret C} ;


    NBPES.dec := λ sk pk c n,
      {code
        K ← N.(NIKE.sharedkey) pk sk ;;
        let k := I.(encode) K in
        M ← E.(NBSES.dec) c k n ;;
        ret M
      }
|}.


Local Obligation Tactic := idtac.

Context (N : NIKE_scheme) (E : NBSES_scheme) (I : inj ('F N.(NIKE.Shared_Key)) ('F E.(NBSES.Shared_Key))).
Let P := (CRYPTOBOX_scheme N E I).


Lemma Equiv_GuPKAE_GMODPKAE qset (b : 'bool):
perfect (GPKAE.I_GPKAE_OUT (CRYPTOBOX_scheme N E I)) (GPKAE.GuPKAE (CRYPTOBOX_scheme N E I) b) (GMODPKAE.GMODPKAE E N qset I b).
Proof.
(*unfold GPKAE.GuPKAE, GMODPKAE.GMODPKAE.
nssprove_share.
eapply prove_perfect.
apply (eq_rel_perf_ind_eq).
simplify_eq_rel x.
- ssprove_code_simpl.
  simplify_linking.
  unfold par.
  ssprove_code_simpl.
  simpl.
  rewrite unionmE.
  simpl.*)
Admitted.


Theorem Lemma4_Adv_GuPKAE_CB (A : adversary (I_GPKAE_OUT P)) qset:
  AdvFor (GuPKAE (CRYPTOBOX_scheme N E I)) A
  <= AdvFor (GuNIKE N qset) (A ∘ (ID (I_GMODPKAE_ID_COMP N) || ((MODPKAE N E) ∘ ((ID (I_NIKE_OUT N) || AE E N I false)))))
     +
     AdvFor (GAE E N qset I) (A ∘ (ID (I_GMODPKAE_ID_COMP N) || ((MODPKAE N E) ∘ ((NIKE N || ID (I_AE_OUT E N))))) ∘ ((PKEY (NIKE_to_GEN N) true || ID (I_GAE_OUT E N)))).
Proof.
erewrite (AdvFor_perfect (Equiv_GuPKAE_GMODPKAE qset)).
unfold GuPKAE, GuNIKE, GAE, GMODPKAE, AdvFor.
erewrite Adv_sym.
nssprove_adv_trans ((ID (I_GMODPKAE_ID_COMP N) || (MODPKAE N E ∘ (NIKE N || AE E N I false))) ∘ (PKEY (NIKE_to_GEN N) true || KEY N qset true))%sep.
erewrite Adv_sym.
apply lerD.

- erewrite Adv_sep_link.
  erewrite Adv_par_r by nssprove_valid.
  rewrite Adv_sep_link. erewrite Adv_par_l by nssprove_valid.
  erewrite (sep_par_commut (ID (I_KEY_OUT N))) by nssprove_valid.
  apply eq_ler.
  apply Adv_mor. 
    1, 2: reflexivity.
  apply sep_link_mor.
    2: reflexivity.
  rewrite -sep_link_assoc.
  apply sep_link_mor.
    1: reflexivity.
  erewrite (sep_par_commut _ (ID (I_GNIKE_ID_COMP N))) by nssprove_valid.
  unfold I_GNIKE_ID_COMP.
  rewrite <- id_sep_par by nssprove_valid.
  rewrite -sep_par_assoc.
  erewrite <- sep_interchange by nssprove_valid.
  rewrite -> sep_link_id by nssprove_valid.
  apply sep_par_mor.
    1: reflexivity.
  rewrite -sep_link_assoc.
  apply sep_link_mor.
    1: reflexivity.
  erewrite (sep_par_commut  (ID (I_AE_IN N))) by nssprove_valid.
  erewrite <- swash by nssprove_valid.
  reflexivity.

- erewrite <- Adv_sep_link.
  apply eq_ler.
  rewrite Adv_sym.
  apply Adv_mor.
    3: reflexivity.
    
  + rewrite <- (@sep_par_empty_l ((ID (I_GAE_ID_COMP N) || AE E N I true) ∘ KEY N qset true)%sep).
    rewrite -sep_link_assoc.
    unfold I_GAE_OUT.
    erewrite <- (sep_interchange (PKEY (NIKE_to_GEN N) true)) by nssprove_valid. 
    rewrite -> sep_link_id by nssprove_valid.
    erewrite -> id_sep_link by nssprove_valid.
    erewrite <- (id_sep_link (PKEY (NIKE_to_GEN N) true)) by nssprove_valid.
    erewrite sep_interchange by nssprove_valid.
    erewrite sep_link_assoc.
    erewrite id_sep_link by nssprove_valid.
    apply sep_link_mor.
      2: reflexivity.
    erewrite -> (@swish _ _ _ _ _ _ (NIKE.NIKE N)) by nssprove_valid.
    rewrite sep_link_assoc.
    erewrite <- (id_sep_link (ID (I_GMODPKAE_ID_COMP N))) by nssprove_valid.
    erewrite sep_interchange by nssprove_valid.
    apply sep_link_mor.
      1: erewrite id_sep_link by nssprove_valid ; reflexivity.
    rewrite sep_par_assoc.
    rewrite sep_par_assoc.
    apply sep_par_mor.
      2: reflexivity.
    do 2 rewrite -> id_sep_par by nssprove_valid.
    apply alpha_eq.
    f_equal.
    fset_solve.

  + rewrite <- (@sep_par_empty_l ((ID (I_GAE_ID_COMP N) || AE E N I false) ∘ KEY N qset true)%sep).
    rewrite -sep_link_assoc.
    unfold I_GAE_OUT.
    erewrite <- (sep_interchange (PKEY (NIKE_to_GEN N) true)) by nssprove_valid. 
    rewrite -> sep_link_id by nssprove_valid.
    erewrite -> id_sep_link by nssprove_valid.
    erewrite <- (id_sep_link (PKEY (NIKE_to_GEN N) true)) by nssprove_valid.
    erewrite sep_interchange by nssprove_valid.
    erewrite sep_link_assoc.
    erewrite id_sep_link by nssprove_valid.
    apply sep_link_mor.
      2: reflexivity.
    erewrite -> (@swish _ _ _ _ _ _ (NIKE.NIKE N)) by nssprove_valid.
    rewrite sep_link_assoc.
    erewrite <- (id_sep_link (ID (I_GMODPKAE_ID_COMP N))) by nssprove_valid.
    erewrite sep_interchange by nssprove_valid.
    apply sep_link_mor.
      1: erewrite id_sep_link by nssprove_valid ; reflexivity.
    rewrite sep_par_assoc.
    rewrite sep_par_assoc.
    apply sep_par_mor.
      2: reflexivity.
    do 2 rewrite -> id_sep_par by nssprove_valid.
    apply alpha_eq.
    f_equal.
    fset_solve.
Qed.


Program Definition A_GNIKE_OUT (A : adversary (I_GPKAE_OUT P)) : adversary (I_GNIKE_OUT N) :=
  {adversary _ ; (A ∘ (ID (I_GMODPKAE_ID_COMP N) || ((MODPKAE N E) ∘ ((ID (I_NIKE_OUT N) || AE E N I false))))) }.
Obligation 1. intros. unfold P in A. nssprove_valid. Qed.

Program Definition A_GAE_OUT (A : adversary (I_GPKAE_OUT P)) : adversary (I_GAE_OUT E N) :=
  {adversary _ ; ((A ∘ (ID (I_GMODPKAE_ID_COMP N) || ((MODPKAE N E) ∘ ((NIKE N || ID (I_AE_OUT E N))))) ∘ ((PKEY (NIKE_to_GEN N) true || ID (I_GAE_OUT E N))))) }.
Obligation 1. intros. unfold P in A. unfold I_GAE_OUT. nssprove_valid. Qed.


Theorem Cryptobox_Security (A : adversary (I_GPKAE_OUT P)) qset :
  AdvFor (GPKAE P) A
  <=
  AdvFor (PKEY (NBPES_to_GEN P)) (A ∘ (PKAE P false || ID (I_GPKAE_ID_COMP P)))
  +
  AdvFor (PKEY (NBPES_to_GEN P)) (A ∘ (PKAE P true || ID (I_GPKAE_ID_COMP P)))
  +
  AdvFor (PKEY (NIKE_to_GEN N)) (((A_GNIKE_OUT A) ∘ (NIKE N || ID (I_GNIKE_ID_COMP N))) ∘ (KEY N qset false || ID (I_PKEY_OUT (NIKE_to_GEN N))))
  +
  AdvFor (GNIKE N qset) (A_GNIKE_OUT A)
  +
  AdvFor (PKEY (NIKE_to_GEN N)) (((A_GNIKE_OUT A) ∘ (NIKE N || ID (I_GNIKE_ID_COMP N))) ∘ (KEY N qset true || ID (I_PKEY_OUT (NIKE_to_GEN N))))
  +
  \sum_(0 <= i < qset) AdvFor (GSAE E) ((A_GAE_OUT A) ∘ HYBRID E N I i qset ∘ ((ID (I_GSAE_OUT E)) || (KEY N qset true))).
Proof.
unfold P in A.
unfold P.
eapply le_trans.
- apply Corollary1_Adv_GPKAE.
- repeat rewrite <- GRing.addrA.
  apply lerD.
  + done.
  + rewrite -> GRing.addrC.
    apply lerD.
    * done.
    * rewrite GRing.addrA.
      eapply le_trans.
      -- apply Lemma4_Adv_GuPKAE_CB.
      -- rewrite GRing.addrA.
         apply lerD.
         ++ apply (Corollary3_Adv_GNIKE_GuNIKE (A_GNIKE_OUT A)).
         ++ apply (Lemma3_Adv_GAE qset I (A_GAE_OUT A)).
Qed.

End crypto_box.
