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

#[export] Hint Unfold GMODPKAE.I_GMODPKAE_OUT GMODPKAE.I_GMODPKAE_ID_COMP MODPKAE.I_MODPKAE_OUT MODPKAE.I_MODPKAE_IN NIKE_scheme.I_NIKE_OUT NIKE_scheme.I_NIKE_IN AE.I_AE_OUT AE.I_AE_IN PKEY.I_PKEY_OUT KEY.I_KEY_OUT GPKAE.I_GPKAE_OUT GPKAE.I_GPKAE_ID_COMP NBPES_scheme.I_PKAE_OUT NBPES_scheme.I_PKAE_IN GNIKE.I_GNIKE_OUT GAE.I_GAE_OUT GAE.I_GAE_ID_COMP : in_fset_eq.


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


Lemma Equiv_GuPKAE_GMODPKAE (N : NIKE_scheme.NIKE_scheme) (E : NBSES.NBSES_scheme) (I : NIKE_scheme.inj ('fin #|NIKE_scheme.Shared_Key N|) ('fin #|NBSES.Shared_Key E|)) (I_cb : CB_inj ('fin #|N.(NIKE_scheme.Shared_Key)|) ('fin #|E.(NBSES.Shared_Key)|)) (b : 'bool):
perfect (GPKAE.I_GPKAE_OUT (CRYPTOBOX_scheme N E I_cb)) (GPKAE.GuPKAE (CRYPTOBOX_scheme N E I_cb) b) (GMODPKAE.GMODPKAE E N I b).
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


Instance sharedkey_posi n : Positive #|NIKE_scheme.Shared_Key n|.
Proof.
Admitted.

Instance k_posi e : Positive #|NBSES.Shared_Key e|.
Proof.
Admitted.

Local Obligation Tactic := idtac.

Context (N : NIKE_scheme.NIKE_scheme) (E : NBSES.NBSES_scheme) (I_cb : CB_inj ('fin #|N.(NIKE_scheme.Shared_Key)|) ('fin #|E.(NBSES.Shared_Key)|)) (I : NIKE_scheme.inj ('fin #|N.(NIKE_scheme.Shared_Key)|) ('fin #|E.(NBSES.Shared_Key)|)).
Let P := (CRYPTOBOX_scheme N E I_cb).

Program Definition A5   (A : adversary (GPKAE.I_GPKAE_OUT P)) : adversary (GAE.I_GAE_OUT E N) :=
  {adversary _ ; ((A ∘ (ID (GMODPKAE.I_GMODPKAE_ID_COMP N) || ((MODPKAE.MODPKAE N E) ∘ ((NIKE_scheme.NIKE N || ID (AE.I_AE_OUT E N))))) ∘ ((PKEY.PKEY (PKEY.NIKE_to_GEN N) true || ID (KEY.I_KEY_OUT N) || ID (AE.I_AE_OUT E N))))) }.
Obligation 1. intros. unfold P in A. nssprove_valid. Admitted.

Program Definition A_GAE   (A : adversary (GPKAE.I_GPKAE_OUT P)) : adversary (GAE.I_GAE_OUT E N) :=
  {adversary _ ; ((A ∘ (ID (GMODPKAE.I_GMODPKAE_ID_COMP N) || ((MODPKAE.MODPKAE N E) ∘ ((NIKE_scheme.NIKE N || ID (AE.I_AE_OUT E N))))) ∘ ((PKEY.PKEY (PKEY.NIKE_to_GEN N) true || ID (GAE.I_GAE_OUT E N))))) }.
Obligation 1. intros. unfold P in A. nssprove_valid. Qed.


Program Definition A_GAE2 (A : adversary (GPKAE.I_GPKAE_OUT P)) : adversary (GAE.I_GAE_OUT E N) :=
  {adversary _ ; ((A ∘ ((ID (GMODPKAE.I_GMODPKAE_ID_COMP N)
  || MODPKAE.MODPKAE N E ∘ (NIKE_scheme.NIKE N || AE.AE E N I true))
 ∘ (PKEY.PKEY (PKEY.NIKE_to_GEN N) true || KEY.KEY N true)))) }.
Obligation 1. intros. unfold P in A. nssprove_valid. Qed.


Program Definition A4_A   (A : adversary (GPKAE.I_GPKAE_OUT P)) : adversary (GNIKE.I_GNIKE_OUT N) :=
  {adversary _ ; ((A ∘ (ID (GMODPKAE.I_GMODPKAE_ID_COMP N) || ((MODPKAE.MODPKAE N E) ∘ ((ID (NIKE_scheme.I_NIKE_OUT N) || AE.AE E N I false)))))) }.
Obligation 1. intros. unfold P in A. nssprove_valid. Qed.

(* fset_solve. - rewrite fsubUset. apply /andP. split. + fset_solve. Admitted.


Program Definition A4 (A : adversary (GPKAE.I_GPKAE_OUT P)) : adversary (GNIKE.I_GNIKE_OUT N) :=
  {adversary _ ; (A ∘ (ID (GMODPKAE.I_GMODPKAE_ID_COMP N) || ((MODPKAE.MODPKAE N E) ∘ ((ID (NIKE_scheme.I_NIKE_OUT N) || AE.AE E N I false))))) }.
Obligation 1. intros. unfold P in A. nssprove_valid. Qed.

Program Definition A5 (A : adversary (GPKAE.I_GPKAE_OUT P)) : adversary (GAE.I_GAE_OUT E N) :=
  {adversary _ ; ((A ∘ (ID (GMODPKAE.I_GMODPKAE_ID_COMP N) || ((MODPKAE.MODPKAE N E) ∘ ((NIKE_scheme.NIKE N || ID (AE.I_AE_OUT E N))))) ∘ ((PKEY.PKEY (PKEY.NIKE_to_GEN N) true || ID (GAE.I_GAE_OUT E N))))) }.
Obligation 1. intros. unfold P in A. nssprove_valid. Qed.

(* Program Definition A5   (A : adversary (GPKAE.I_GPKAE_OUT P)) : adversary (GAE.I_GAE_OUT E N) :=
  {adversary _ ; (A ∘ (ID (GMODPKAE.I_GMODPKAE_ID_COMP N) || ((MODPKAE.MODPKAE N E) ∘ ((NIKE_scheme.NIKE N || ID (AE.I_AE_OUT E N))))) ∘ ((PKEY.PKEY (PKEY.NIKE_to_GEN N) true || ID (KEY.I_KEY_OUT N)))) }.
Obligation 1. intros. unfold P in A. nssprove_valid. 2: fset_solve. Qed. *)


(*Lemma move_AE (b : 'bool) :
ID (GMODPKAE.I_GMODPKAE_ID_COMP N) || ((MODPKAE.MODPKAE N E) ∘ (NIKE_scheme.NIKE N || AE.AE E N I b)) ≡ (ID (GMODPKAE.I_GMODPKAE_ID_COMP N) || ((MODPKAE.MODPKAE N E) ∘ (NIKE_scheme.NIKE N || (ID (AE.I_AE_OUT E N))))). ∘ (ID ?? || AE.AE N).*)

Lemma ID_sep_par I I' :
ID I || ID I' = ID (I :|: I').
Admitted.

Lemma eq_ID I I':
I = I' -> ID I = ID I'.
Admitted.

Theorem Lemma4_Adv_GuPKAE_CB (A : adversary (GPKAE.I_GPKAE_OUT P)):
  AdvFor (GPKAE.GuPKAE (CRYPTOBOX_scheme N E I_cb)) A
  <= AdvFor (GNIKE.GuNIKE N) (A ∘ (ID (GMODPKAE.I_GMODPKAE_ID_COMP N) || ((MODPKAE.MODPKAE N E) ∘ ((ID (NIKE_scheme.I_NIKE_OUT N) || AE.AE E N I false)))))
     +
     AdvFor (GAE.GAE E N I) (A ∘ (ID (GMODPKAE.I_GMODPKAE_ID_COMP N) || ((MODPKAE.MODPKAE N E) ∘ ((NIKE_scheme.NIKE N || ID (AE.I_AE_OUT E N))))) ∘ ((PKEY.PKEY (PKEY.NIKE_to_GEN N) true || ID (GAE.I_GAE_OUT E N)))).
Proof.
erewrite (AdvFor_perfect (Equiv_GuPKAE_GMODPKAE N E I I_cb)).
unfold GPKAE.GuPKAE, GNIKE.GuNIKE, GAE.GAE, GMODPKAE.GMODPKAE, AdvFor.
erewrite Adv_sym.
nssprove_adv_trans ((ID (GMODPKAE.I_GMODPKAE_ID_COMP N) || (MODPKAE.MODPKAE N E ∘ (NIKE_scheme.NIKE N || AE.AE E N I false))) ∘ (PKEY.PKEY (PKEY.NIKE_to_GEN N) true || KEY.KEY N true))%sep.
erewrite Adv_sym.
apply lerD.
- rewrite Adv_sep_link. erewrite Adv_par_r by nssprove_valid. rewrite Adv_sep_link. erewrite Adv_par_l by nssprove_valid. erewrite (sep_par_commut (ID (KEY.I_KEY_OUT N))) by nssprove_valid. apply eq_ler. apply Adv_mor. 
1, 2: reflexivity.
apply sep_link_mor. 2: reflexivity. rewrite -sep_link_assoc. apply sep_link_mor. 1: reflexivity.
erewrite (sep_par_commut _ (ID (GNIKE.I_GNIKE_ID_COMP N))) by nssprove_valid.
replace (ID (GNIKE.I_GNIKE_ID_COMP N)) with (ID (GMODPKAE.I_GMODPKAE_ID_COMP N) || ID (AE.I_AE_IN N)).
2:{ admit. } (*redefine I_GNIKE_ID_COMP*)
rewrite -sep_par_assoc.
erewrite <- sep_interchange by nssprove_valid.
rewrite -> sep_link_id by nssprove_valid.
apply sep_par_mor. 1: reflexivity.
rewrite -sep_link_assoc.
apply sep_link_mor. 1: reflexivity.
erewrite (sep_par_commut  (ID (AE.I_AE_IN N))) by nssprove_valid.
erewrite <- swash by nssprove_valid.
reflexivity.

- rewrite -Adv_sep_link.
  apply eq_ler. rewrite Adv_sym.
  apply Adv_mor. 3: reflexivity.
+ rewrite -(@sep_par_empty_l ((AE.AE E N I true || ID (GAE.I_GAE_ID_COMP N)) ∘ KEY.KEY N true)%sep). rewrite -sep_link_assoc. erewrite <- (sep_interchange (PKEY.PKEY (PKEY.NIKE_to_GEN N) true)) by nssprove_valid. rewrite -> sep_link_id by nssprove_valid.
erewrite -> id_sep_link.
2: nssprove_valid.
2: { admit. } (*par combination*)
erewrite <- (id_sep_link (PKEY.PKEY (PKEY.NIKE_to_GEN N) true)) by nssprove_valid.
erewrite sep_interchange.
2, 3, 4, 5, 6, 8 : nssprove_valid.
2: { admit. } (*par combination*)
erewrite sep_link_assoc. erewrite id_sep_link by nssprove_valid. apply sep_link_mor.
2: reflexivity.
erewrite (sep_par_commut (AE.AE E N I true)) by nssprove_valid.
About swish.
erewrite -> (@swish _ _ _ _ _ _ (NIKE_scheme.NIKE N)) by nssprove_valid.
rewrite sep_link_assoc.
erewrite <- (id_sep_link (ID (GMODPKAE.I_GMODPKAE_ID_COMP N))) by nssprove_valid.
erewrite sep_interchange by nssprove_valid.
apply sep_link_mor.
1: erewrite id_sep_link by nssprove_valid ; reflexivity.
rewrite sep_par_assoc. rewrite sep_par_assoc. apply sep_par_mor.
2: reflexivity.
replace ((ID (GMODPKAE.I_GMODPKAE_ID_COMP N) || ID (NIKE_scheme.I_NIKE_IN N))) with (ID (PKEY.I_PKEY_OUT (PKEY.NIKE_to_GEN N)) || ID (GAE.I_GAE_ID_COMP N)). (*to get equality instead of equivalence*)
1: reflexivity.
rewrite ID_sep_par. rewrite ID_sep_par.
apply eq_ID. apply /eqP. rewrite eqEfsubset. apply /andP. split.
1,2 : fset_solve.
+ rewrite -(@sep_par_empty_l ((AE.AE E N I false || ID (GAE.I_GAE_ID_COMP N)) ∘ KEY.KEY N true)%sep). rewrite -sep_link_assoc. erewrite <- (sep_interchange (PKEY.PKEY (PKEY.NIKE_to_GEN N) true)) by nssprove_valid. rewrite -> sep_link_id by nssprove_valid.
erewrite -> id_sep_link.
2: nssprove_valid.
2: { admit. } (*par combination*)
erewrite <- (id_sep_link (PKEY.PKEY (PKEY.NIKE_to_GEN N) true)) by nssprove_valid.
erewrite sep_interchange.
2, 3, 4, 5, 6, 8 : nssprove_valid.
2: { admit. } (*par combination*)
erewrite sep_link_assoc. erewrite id_sep_link by nssprove_valid. apply sep_link_mor.
2: reflexivity.
erewrite (sep_par_commut (AE.AE E N I false)) by nssprove_valid.
About swish.
erewrite -> (@swish _ _ _ _ _ _ (NIKE_scheme.NIKE N)) by nssprove_valid.
rewrite sep_link_assoc.
erewrite <- (id_sep_link (ID (GMODPKAE.I_GMODPKAE_ID_COMP N))) by nssprove_valid.
erewrite sep_interchange by nssprove_valid.
apply sep_link_mor.
1: erewrite id_sep_link by nssprove_valid ; reflexivity.
rewrite sep_par_assoc. rewrite sep_par_assoc. apply sep_par_mor.
2: reflexivity.
replace ((ID (GMODPKAE.I_GMODPKAE_ID_COMP N) || ID (NIKE_scheme.I_NIKE_IN N))) with (ID (PKEY.I_PKEY_OUT (PKEY.NIKE_to_GEN N)) || ID (GAE.I_GAE_ID_COMP N)). (*to get equality instead of equivalence*)
1: reflexivity.
rewrite ID_sep_par. rewrite ID_sep_par.
apply eq_ID. apply /eqP. rewrite eqEfsubset. apply /andP. split.
1,2 : fset_solve.
Admitted.

Unshelve. 2: nssprove_valid. fset_solve.






Search eq fsubset. fset_solve.


apply eq_raw_module.
1: reflexivity.
apply eq_fmap. (*equal on every function we look up*)
intros x.


Search ID sep_par.

GEN
CSETPK
GETSK
HONPK
SET
CSET

GEN
CSETPK
GETSK
HONPK
SET
SCET

rewrite sep_par_assoc. erewrite (sep_par_commut (ID (PKEY.I_PKEY_OUT (PKEY.NIKE_to_GEN N)))) by nssprove_valid.
rewrite swish.

erewrite <- sep_interchange.
2, 3, 4, 5: nssprove_valid.



 rewrite sep_link_assoc.

Check swish.

erewrite -> (@swish _ _ _ _ _ _ (PKEY.PKEY (PKEY.NIKE_to_GEN N) true) (ID (KEY.I_KEY_OUT N) || ID (AE.I_AE_OUT E N))%sep).
2, 3, 5, 6: nssprove_valid.
2, 3: admit.
rewrite sep_par_empty_l.
erewrite <- (sep_par_commut  (ID (AE.I_AE_OUT E N))) by nssprove_valid.
erewrite sep_link_assoc.
erewrite <- (sep_link_assoc _ (ID (KEY.I_KEY_OUT N) || ID (AE.I_AE_OUT E N))).
erewrite <- sep_interchange.

apply sep_par_mor. rewrite sep_link_assoc. apply sep_link_mor.   (*nssprove_valid.*) admit.
- Search link. (*rewrite link_sep_link.*) erewrite Adv_sep_link.

(* Theorem Lemma4_Adv_GuPKAE_CB {P} {N} {E} (A : adversary (GPKAE.I_GPKAE_OUT P)) (I : NIKE_scheme.inj ('fin #|N.(NIKE_scheme.Shared_Key)|) ('fin #|E.(NBSES.Shared_Key)|)) (I_cb : CB_inj ('fin #|N.(NIKE_scheme.Shared_Key)|) ('fin #|E.(NBSES.Shared_Key)|)):
  AdvFor (GPKAE.GuPKAE (CRYPTOBOX_scheme N E I_cb)) A
  <= AdvFor (GNIKE.GuNIKE N) (A ∘ (ID (GMODPKAE.I_GMODPKAE_ID_COMP N) || ((MODPKAE.MODPKAE N E) ∘ ((ID (NIKE_scheme.I_NIKE_OUT N) || AE.AE E N I false)))))
     +
     AdvFor (GAE.GAE E N I) (A ∘ (ID (GMODPKAE.I_GMODPKAE_ID_COMP N) || ((MODPKAE.MODPKAE N E) ∘ ((NIKE_scheme.NIKE N || ID (AE.I_AE_OUT E N))))) ∘ ((PKEY.PKEY (PKEY.NIKE_to_GEN N) true || ID (KEY.I_KEY_OUT N) || ID (AE.I_AE_OUT E N)))).
Proof.
erewrite (AdvFor_perfect (Equiv_GuPKAE_GMODPKAE N E I I_cb)).
unfold GPKAE.GuPKAE, GNIKE.GuNIKE, GAE.GAE, GMODPKAE.GMODPKAE, AdvFor.
erewrite Adv_sym.
nssprove_adv_trans ((ID (GMODPKAE.I_GMODPKAE_ID_COMP N) || (MODPKAE.MODPKAE N E ∘ (NIKE_scheme.NIKE N || AE.AE E N I false))) ∘ (PKEY.PKEY (PKEY.NIKE_to_GEN N) true || KEY.KEY N true))%sep.
erewrite Adv_sym.
apply lerD.
- rewrite Adv_sep_link. erewrite Adv_par_r by nssprove_valid. rewrite Adv_sep_link. erewrite Adv_par_l by nssprove_valid. erewrite (sep_par_commut (ID (KEY.I_KEY_OUT N))) by nssprove_valid. apply eq_ler. apply Adv_mor. 
1, 2: reflexivity.
apply sep_link_mor. 2: reflexivity. rewrite -sep_link_assoc. apply sep_link_mor. 1: reflexivity.
erewrite (sep_par_commut _ (ID (GNIKE.I_GNIKE_ID_COMP N))) by nssprove_valid.
replace (ID (GNIKE.I_GNIKE_ID_COMP N)) with (ID (GMODPKAE.I_GMODPKAE_ID_COMP N) || ID (AE.I_AE_IN N)).
2: admit. (*redefine I_GNIKE_ID_COMP*)
rewrite -sep_par_assoc.
erewrite <- sep_interchange by nssprove_valid.
rewrite -> sep_link_id by nssprove_valid.
apply sep_par_mor. 1: reflexivity.
rewrite -sep_link_assoc.
apply sep_link_mor. 1: reflexivity.
erewrite (sep_par_commut  (ID (AE.I_AE_IN N))) by nssprove_valid.
erewrite <- swash by nssprove_valid.
reflexivity.


- rewrite -Adv_sep_link.
  apply eq_ler. rewrite Adv_sym.
  apply Adv_mor. 3: reflexivity.
+ rewrite sep_link_assoc.
rewrite -sep_par_assoc.
erewrite -> (@swish _ _ _ _ _ _ (PKEY.PKEY (PKEY.NIKE_to_GEN N) true) (ID (KEY.I_KEY_OUT N)
                                                                            || ID (AE.I_AE_OUT E N))%sep).
2, 3, 5, 6: nssprove_valid.
2, 3: admit.
rewrite sep_par_empty_l.
erewrite <- (sep_par_commut  (ID (AE.I_AE_OUT E N))) by nssprove_valid.
erewrite sep_link_assoc.
erewrite <- (sep_link_assoc _ (ID (KEY.I_KEY_OUT N) || ID (AE.I_AE_OUT E N))).
erewrite <- sep_interchange.

apply sep_par_mor. rewrite sep_link_assoc. apply sep_link_mor.   (*nssprove_valid.*) admit.
- Search link. (*rewrite link_sep_link.*) erewrite Adv_sep_link. *)

(* Theorem Lemma4_Adv_GuPKAE_CB {P} {N} {E} (A : adversary (GPKAE.I_GPKAE_OUT P)) (I : NIKE_scheme.inj ('fin #|N.(NIKE_scheme.Shared_Key)|) ('fin #|E.(NBSES.Shared_Key)|)) (I_cb : CB_inj ('fin #|N.(NIKE_scheme.Shared_Key)|) ('fin #|E.(NBSES.Shared_Key)|)):
  AdvFor (GPKAE.GuPKAE (CRYPTOBOX_scheme N E I_cb)) A
  <= AdvFor (GNIKE.GuNIKE N) (A ∘ (ID (GMODPKAE.I_GMODPKAE_ID_COMP N) || ((MODPKAE.MODPKAE N E) ∘ ((ID (NIKE_scheme.I_NIKE_OUT N) || AE.AE E N I false)))))
     +
     AdvFor (GAE.GAE E N I) (A ∘ (ID (GMODPKAE.I_GMODPKAE_ID_COMP N) || ((MODPKAE.MODPKAE N E) ∘ ((NIKE_scheme.NIKE N || ID (AE.I_AE_OUT E N))))) ∘ ((PKEY.PKEY (PKEY.NIKE_to_GEN N) true || ID (GAE.I_GAE_OUT E N)))).
Proof.
unfold P.
unfold P in A.
erewrite (AdvFor_perfect (Equiv_GuPKAE_GMODPKAE)).
unfold GPKAE.GuPKAE, GNIKE.GuNIKE, GAE.GAE, GMODPKAE.GMODPKAE, AdvFor.
rewrite Adv_sym.
nssprove_adv_trans ((ID (GMODPKAE.I_GMODPKAE_ID_COMP N) || MODPKAE.MODPKAE N E ∘ (NIKE_scheme.NIKE N || AE.AE E N I false)) ∘ (PKEY.PKEY (PKEY.NIKE_to_GEN N) true || KEY.KEY N true))%sep.
rewrite Adv_sym.
apply lerD.
- rewrite Adv_sep_link. rewrite Adv_sep_link. erewrite Adv_par_r by nssprove_valid. erewrite Adv_par_l by nssprove_valid. erewrite (sep_par_commut  (ID (KEY.I_KEY_OUT N))) by nssprove_valid. apply eq_ler. apply Adv_mor. 
1, 2: reflexivity.
apply sep_link_mor. 2: reflexivity. rewrite -sep_link_assoc. apply sep_link_mor. 1: reflexivity.r
rewrite sep_link_assoc. apply sep_link_mor.   (*nssprove_valid.*) admit.
- Search link. (*rewrite link_sep_link.*) erewrite Adv_sep_link. *)


interchange, swish, swash
 erewrite sep_par_commut in ((PKEY.PKEY (PKEY.NIKE_to_GEN N) true || KEY.KEY N false)). erewrite -> Adv_par_r by nssprove_valid.
+ rewrite Adv_par_r. rewrite sep_par_commut. (*Search "||". nssprove_valid.*) admit.
- rewrite Adv_sep_link.
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
   ( AdvFor (GSAE.GSAE E) ((A5 A1) ∘ (HYBRID.HYBRID E N I i qset) ∘ (AE.AE E N I true || ID (GH.I_GH_ID_COMP N)) ∘ (KEY.KEY N true)) + 
     AdvFor (GSAE.GSAE E) ((A5 A1) ∘ (HYBRID.HYBRID E N I i qset) ∘ (AE.AE E N I false|| ID (GH.I_GH_ID_COMP N)) ∘ (KEY.KEY N true))).
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
------ apply (GH.Lemma3_Adv_GAE (A5 A1)). Qed.

End crypto_box.
