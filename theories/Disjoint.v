Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_ssreflect all_algebra reals distr realsum
  fingroup.fingroup solvable.cyclic prime ssrnat ssreflect ssrfun ssrbool ssrnum
  eqtype choice seq.
Set Warnings "notation-overridden,ambiguous-paths".

From Mon Require Import SPropBase.

From Crypt Require Import Axioms ChoiceAsOrd SubDistr Couplings
  UniformDistrLemmas FreeProbProg Theta_dens RulesStateProb UniformStateProb
  pkg_core_definition choice_type pkg_composition pkg_rhl Package Prelude
  SigmaProtocol.

From Coq Require Import Utf8.
From extructures Require Import ord fset fmap.

From Equations Require Import Equations.
Require Equations.Prop.DepElim.

Set Equations With UIP.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".
Set Primitive Projections.



Local Open Scope ring_scope.
Import GroupScope GRing.Theory.


Import Num.Def.
Import Num.Theory.
Import Order.POrderTheory.
Require Import Btauto.

Import PackageNotation.

From extructures Require Import ffun fperm.

From NominalSSP Require Import
  Nominal Fresh FsetSolve Pr NomPackage.

Import FsetSolve.

(* dlink Section *)

Definition dlink (P P' : nom_package)
  := nom_link P (move P P').

Notation " P  ⊛  P' " :=
  (dlink P P')
  (at level 35, right associativity)
  : package_scope.
  

Lemma rename_alpha {X : actionType} {O : X} {π} : π ∙ O ≡ O.
Proof.
  exists (π^-1)%fperm.
  rewrite renameK //.
Qed.

Lemma rename_alpha_both {X : actionType} {O : X} {π π'} : π ∙ O ≡ π' ∙ O.
Proof.
  setoid_rewrite rename_alpha.
  setoid_reflexivity.
Qed.

Add Parametric Morphism : dlink with
  signature alpha ==> alpha ==> alpha as dlink_mor.
Proof.
  intros P P' EP Q Q' EQ.
  unfold dlink.
  apply nom_link_congr.
  1: apply (move_disj P Q).
  1: apply (move_disj P' Q').
  1: assumption.
  by setoid_rewrite rename_alpha.
Qed.

Lemma disj_rename {X Y : nomType} {x : X} {y : Y} {π} :
  disj x y → disj (π ∙ x) (π ∙ y).
Proof.
  intros H.
  rewrite -(equi2_use _ disj_equi) H //.
Qed.

Lemma equi_fresh_disj {X Y Z W : nomType} {x : X} {y : Y} :
  ∀ {f : X → Z} {g : Y → W},
  equivariant f →
  equivariant g →
  disj (fresh y x ∙ (f x)) (g y).
Proof.
  intros f g Ef Eg.
  rewrite Ef.
  rewrite equi_disj //.
  rewrite disjC equi_disj //.
  apply: fresh_disjoint.
Qed.

Lemma fsetUl : ∀ [T : ordType] (s1 s2 s3 : {fset T}),
  fsubset s1 s2 → fsubset s1 (s2 :|: s3).
Proof.
  intros T s1 s2 s3 H.
  eapply fsubset_trans.
  + apply fsubsetUl.
  + by apply fsetSU.
Qed.

Lemma fsetUr : ∀ [T : ordType] (s1 s2 s3 : {fset T}),
  fsubset s1 s3 → fsubset s1 (s2 :|: s3).
Proof.
  intros T s1 s2 s3 H.
  eapply fsubset_trans.
  + apply fsubsetUr.
  + by apply fsetUS.
Qed.


Lemma subs_equi {X Y : nomType} {x : X} {f : X → Y} :
  equivariant f → subs (f x) x.
Proof.
  intros E.
  by apply supp_fsubset.
Qed.

Lemma subs_equi_eq {X Y : nomType} {x : X} {y : Y} {f : X → Y} :
  equivariant f → y = f x → subs y x.
Proof.
  intros Ef eq.
  rewrite eq.
  by apply subs_equi.
Qed.

Lemma subs_fresh_disj {X Y Z W : nomType} {x : X} {x' : Z} {y : Y} {y' : W} :
  subs x' x →
  subs y' y →
  disj (fresh y x ∙ x') y'.
Proof.
  intros subsx subsy.
  erewrite <- absorb in subsx.
  rewrite -> equi2_use in subsx.
  2: apply subsE.
  eapply fdisjoint_trans.
  1: apply subsx.
  rewrite fdisjointC.
  eapply fdisjoint_trans.
  1: apply subsy.
  apply fresh_disjoint.
Qed.

Lemma subs_fresh_disj_2 {X Y Z W : nomType} {x : X} {x' : Z} {y : Y} {y' : W} :
  subs x' x →
  subs y' y →
  disj y' (fresh y x ∙ x').
Proof.
  rewrite disjC.
  apply subs_fresh_disj.
Qed.

Create HintDb alpha_db.
#[export] Hint Resolve subs_fresh_disj subs_fresh_disj_2 : alpha_db.
#[export] Hint Resolve disj_rename : alpha_db.

Lemma subs_supp_fsetUl {X Y Z W : nomType} {x : X} {y z} {f : Y → Z → W}
  : supp (f y z) = supp y :|: supp z → subs x y → subs x (f y z).
Proof.
  intros H H'.
  rewrite /subs H.
  apply (fsubset_trans H').
  apply fsubsetUl.
Qed.

Lemma subs_supp_fsetUr {X Y Z W : nomType} {x : X} {y z} {f : Y → Z → W}
  : supp (f y z) = supp y :|: supp z → subs x z → subs x (f y z).
Proof.
  intros H H'.
  rewrite /subs H.
  apply (fsubset_trans H').
  apply fsubsetUr.
Qed.

#[export] Hint Resolve subs_supp_fsetUl subs_supp_fsetUr : alpha_db.

Lemma supp_pair {X Y : nomType} {x : X} {y : Y}
  : supp (pair x y) = supp x :|: supp y.
Proof. done. Qed.

#[export] Hint Resolve s_nom_link s_nom_par supp_pair : alpha_db.


Lemma subs_refl {X : nomType} {x : X} : subs x x.
Proof.
  apply fsubsetxx.
Qed.

#[export] Hint Resolve subs_refl : alpha_db.

Lemma disj_nom_link {X : nomType} {x : X} {P Q}
  : disj x P → disj x Q → disj x (nom_link P Q).
Proof.
  intros dP dQ.
  unfold disj.
  rewrite s_nom_link.
  rewrite fdisjointUr.
  apply /andP.
  by split.
Qed.

Lemma disj_nom_link2 {X : nomType} {x : X} {P Q}
  : disj P x → disj Q x → disj (nom_link P Q) x.
Proof.
  intros dP dQ.
  rewrite disjC.
  rewrite disj_nom_link //; rewrite disjC //.
Qed.

Lemma disj_equi2 {X Y Z W : nomType} {x : X} {y : Y} {z : Z} {f}
  : equivariant (f : Y → Z → W) → disj x y → disj x z → disj x (f y z).
Proof.
  intros E D1 D2.
  rewrite disjC.
  change (f y z) with (uncurry f (y, z)).
  eapply fdisjoint_trans.
  + eapply supp_fsubset.
    intros π [x' y'].
    rewrite //= (equi2_use _ E) //.
  + rewrite fdisjointUl.
    apply /andP.
    split; rewrite fdisjointC //.
Qed.

Lemma disj_equi2' {X Y Z W : nomType} {x : X} {y : Y} {z : Z} {f}
  : equivariant (f : Y → Z → W) → disj x y → disj x z → disj (f y z) x.
Proof.
  intros E D1 D2.
  rewrite disjC.
  by apply disj_equi2.
Qed.

Lemma equi_nom_link : equivariant nom_link.
Proof.
  apply equi2_prove => π x y.
  apply rename_nom_link.
Qed.

Lemma equi_nom_par : equivariant nom_par.
Proof.
  apply equi2_prove => π x y.
  apply rename_nom_par.
Qed.

Lemma supp0 {X : nomOrdType} : supp (@fset0 X) = fset0.
Proof.
  rewrite /supp //= fsetSupp0 //.
Qed.

Lemma disj_nom_ID_l {X : nomType} {x : X} {I} : disj (nom_ID I) x.
Proof.
  rewrite /disj /supp //= supp0.
  apply fdisjoint0s.
Qed.

Lemma disj_nom_ID_r {X : nomType} {x : X} {I} : disj x (nom_ID I).
Proof.
  rewrite /disj /supp //= supp0.
  apply fdisjoints0.
Qed.

#[export] Hint Resolve disj_nom_ID_l disj_nom_ID_r : alpha_db.

(* #[export] Hint Resolve disj_nom_link disj_nom_link2 : alpha_db. *)
#[export] Hint Resolve disj_equi2 disj_equi2' : alpha_db.
#[export] Hint Resolve equi_nom_link equi_nom_par : alpha_db.

#[export] Hint Resolve nom_link_congr nom_par_congr : alpha_db.

#[export] Hint Extern 1 (alpha (rename _ _) _) =>
  rewrite rename_alpha : alpha_db.

#[export] Hint Extern 1 (alpha _ (rename _ _)) =>
  rewrite rename_alpha : alpha_db.

#[export] Hint Extern 10 (alpha _ _) =>
  reflexivity : alpha_db.

Lemma dlink_assoc (p1 p2 p3 : nom_package)
  : dlink p1 (dlink p2 p3) ≡ dlink (dlink p1 p2) p3.
Proof.
  rewrite /dlink /move rename_nom_link nom_link_assoc.
  auto with alpha_db nocore.
Qed.


(* ID *)

Lemma nom_link_adj {P P'} {π} : nom_link P (π ∙ P') ≡ nom_link (π^-1 ∙ P)%fperm P'.
Proof.
  exists (π^-1)%fperm.
  rewrite rename_nom_link.
  rewrite renameK //.
Qed.

Lemma rename_trimmed {E π p} : trimmed E p → trimmed E (π ∙ p).
Proof.
  unfold rename; simpl.
  intros tr0.
  unfold trimmed in tr0 |- *.
  rewrite -{2}tr0.
  unfold trim.
  apply eq_fmap => n.
  rewrite filtermE 2!mapmE filtermE.
  destruct (p n).
  2: done.
  destruct t as [S [T m]].
  unfold rename; simpl.
  destruct ((n, (S, T)) \in E) eqn:eq; rewrite eq //.
Qed.

Lemma dlink_id {L I E} (P : nom_package) :
  ValidPackage L I E P → flat I → trimmed E P → dlink P (nom_ID I) ≡ P.
Proof.
  intros V F T.
  rewrite /dlink /move -{3}(nom_link_id F T).
  auto with alpha_db nocore.
Qed.

Lemma id_dlink {L I E} (P : nom_package) (V : ValidPackage L I E P)
  : trimmed E P → dlink (nom_ID E) P ≡ P.
Proof.
  intros T.
  rewrite /dlink /move -{3}(id_nom_link T).
  auto with alpha_db nocore.
Qed.


(* dpar *)

Definition dpar (P P' : nom_package)
  := nom_par P (move P P').

Add Parametric Morphism : dpar with
  signature alpha ==> alpha ==> alpha as dpar_mor.
Proof.
  intros P P' EP Q Q' EQ.
  unfold dpar, move.
  auto with alpha_db nocore.
Qed.

#[export]
Instance Parable_rename_l {p1 p2 π} : Parable p1 p2 → Parable (π ∙ p1) p2.
Proof.
  unfold Parable, domm, unzip1.
  unfold rename; simpl.
  unfold rename; simpl.
  rewrite -map_comp.
  replace (fst \o (λ p,  (p.1, mtyped π p.2)))
    with (@fst nat typed_raw_function).
  { done. }
  apply functional_extensionality => x.
  destruct x as [n T]; done.
Qed.

#[export]
Instance Parable_rename_r {p1 p2 π} : Parable p1 p2 → Parable p1 (π ∙ p2).
Proof.
  unfold Parable, domm, unzip1.
  unfold rename; simpl.
  unfold rename; simpl.
  rewrite -map_comp.
  replace (fst \o (λ p,  (p.1, mtyped π p.2)))
    with (@fst nat typed_raw_function).
  { done. }
  apply functional_extensionality => x.
  destruct x as [n T]; done.
Qed.

Lemma dpar_commut (p1 p2 : nom_package) (P : Parable p1 p2) : dpar p1 p2 ≡ dpar p2 p1.
Proof.
  unfold dpar, move.
  rewrite nom_par_commut.
  auto with alpha_db nocore.
Qed.

Lemma dpar_assoc {P1 P2 P3 : nom_package}
  : dpar P1 (dpar P2 P3) ≡ dpar (dpar P1 P2) P3.
Proof.
  rewrite /dpar /move rename_nom_par nom_par_assoc.
  auto with alpha_db nocore.
Qed.

Lemma dinterchange {A B C D E F} {L1 L2 L3 L4} (p1 p2 p3 p4 : nom_package) :
  ValidPackage L1 B A p1 → ValidPackage L2 E D p2 →
  ValidPackage L3 C B p3 → ValidPackage L4 F E p4 →
  trimmed A p1 → trimmed D p2 → Parable p3 p4 → 
  dpar (dlink p1 p3) (dlink p2 p4) ≡ dlink (dpar p1 p2) (dpar p3 p4).
Proof.
  intros V1 V2 V3 V4 tr1 tr2 P34.
  rewrite /dpar /dlink /move rename_nom_par rename_nom_link nom_interchange.
  2: assumption.
  2: by apply rename_trimmed.
  auto 10 with alpha_db nocore.
Qed.


(* AdvantageD *)

Definition Pr' : nom_package → R := λ P, Pr P true.

Definition AdvantageD (G G' A : nom_package)
  := `| Pr' (dlink A G) - Pr' (dlink A G')|.

Add Parametric Morphism : val with
  signature alpha ==> alpha as val_mor.
Proof.
  intros x y [π E].
  rewrite -E.
  exists π.
  reflexivity.
Qed.

Add Parametric Morphism : Pr' with
  signature alpha ==> eq as Pr'_mor.
Proof.
  intros x y [π' H0].
  unfold Pr'.
  rewrite -H0.
  apply Pr_rename.
Qed.

Lemma Pr'_def {P} : Pr' P = Pr (val P) true.
Proof. done. Qed.

Add Parametric Morphism : AdvantageD with
  signature alpha ==> alpha ==> alpha ==> eq as AdvantageD_mor.
Proof.
  intros.
  unfold AdvantageD.
  rewrite H H0 H1 //.
Qed.

(*
Add Parametric Morphism : (@GRing.add R) with
  signature ler ++> ler ++> ler as add_mor.
Proof.
  intros.
  by apply ler_add.
Qed.
 *)


Lemma alpha_equi {X Y : actionType} {P P'} {f : X → Y}
: equivariant f → P ≡ P' → f P ≡ f P'.
Proof.
  intros equif [π eq].
  exists π.
  rewrite equif.
  f_equal.
  apply eq.
Qed.

#[export]
Instance nom_link_valid {L L' I M E} {P P' : nom_package} :
  ValidPackage L M E P → ValidPackage L' I M P' →
  ValidPackage (L :|: L') I E (nom_link P P').
Proof. by apply valid_link. Qed.

#[export]
Instance dlink_valid {L L' I M E} {P P' : nom_package} :
  ValidPackage L M E P → ValidPackage L' I M P' →
  ValidPackage (L :|: fresh P P' ∙ L') I E (dlink P P').
Proof.
  intros V1 V2.
  eapply (valid_link _ _ _ _ _ _ _ V1).
  apply rename_valid.
  apply V2.
Qed.

#[export]
Instance nom_par_valid {L L' I I' E E'} {P P' : nom_package} :
  Parable P P' →
  ValidPackage L I E P → ValidPackage L' I' E' P' →
  ValidPackage (L :|: L') (I :|: I') (E :|: E') (nom_par P P').
Proof. by apply valid_par. Qed.

#[export]
Instance nom_par_valid_same_import {L L' I E E'} {P P' : nom_package} :
  Parable P P' →
  ValidPackage L I E P → ValidPackage L' I E' P' →
  ValidPackage (L :|: L') I (E :|: E') (nom_par P P').
Proof.
  intros Par V1 V2.
  rewrite -(fsetUid I).
  by apply nom_par_valid.
Qed.

#[export]
Instance dpar_valid {L L' I I' E E'} {P P' : nom_package} :
  Parable P P' → 
  ValidPackage L I E P → ValidPackage L' I' E' P' →
  ValidPackage (L :|: fresh P P' ∙ L') (I :|: I') (E :|: E') (dpar P P').
Proof.
  intros Par V1 V2.
  simpl.
  eapply valid_par.
  + apply Parable_rename_r, Par.
  + apply V1.
  + apply rename_valid, V2.
Qed.

#[export]
Instance dpar_valid_r {L L' I I' E E'} {P P' : nom_package} :
  Parable P' P → 
  ValidPackage L I E P → ValidPackage L' I' E' P' →
  ValidPackage (L :|: fresh P P' ∙ L') (I' :|: I) (E' :|: E) (dpar P P').
Proof.
  intros Par V1 V2.
  rewrite (fsetUC I') (fsetUC E').
  apply dpar_valid; try assumption.
  rewrite /Parable fdisjointC //.
Qed.

#[export]
Instance dpar_valid_same_import {L L' I E E'} {P P' : nom_package} :
  Parable P P' → 
  ValidPackage L I E P → ValidPackage L' I E' P' →
  ValidPackage (L :|: fresh P P' ∙ L') I (E :|: E') (dpar P P').
Proof.
  intros Par V1 V2.
  rewrite -(fsetUid I).
  by apply dpar_valid.
Qed.

Lemma AdvantageD_triangle {G1 G2 G3 : nom_package} A
  : AdvantageD G1 G3 A <= AdvantageD G1 G2 A + AdvantageD G2 G3 A.
Proof. unfold AdvantageD, Pr'. apply Advantage_triangle. Qed.

Ltac eadvantage_trans :=
  eapply le_trans;
    [ eapply AdvantageD_triangle |].

Ltac advantage_trans M :=
  eapply le_trans;
    [ eapply (@AdvantageD_triangle _ M) |].

Lemma AdvantageD_same (G A : nom_package) :
  AdvantageD G G A = 0.
Proof. rewrite /AdvantageD addrN. apply normr0. Qed.

Lemma AdvantageD_sym (G G' A : nom_package) :
  AdvantageD G G' A = AdvantageD G' G A.
Proof. apply distrC. Qed.

Lemma AdvantageD_alpha (G G' A : nom_package)
  : G ≡ G' → AdvantageD G G' A = 0.
Proof.
  intros Eq.
  rewrite Eq.
  apply AdvantageD_same.
Qed.

Lemma AdvantageD_dlink (G G' D A : nom_package) :
  AdvantageD (dlink D G) (dlink D G') A = AdvantageD G G' (dlink A D).
Proof.
  unfold AdvantageD.
  erewrite dlink_assoc.
  erewrite dlink_assoc.
  done.
Qed.

Lemma nom_link_dlink {P P' : nom_package} :
  disj P P' →
  nom_link P P' ≡ dlink P P'.
Proof.
  intros D.
  unfold dlink, move.
  auto with alpha_db nocore.
Qed.

Lemma link_dlink {P P' : nom_package} :
  disj P P' →
  link P P' ≡ val (dlink P P').
Proof.
  intros D.
  change (link P P') with (val (nom_link P P')).
  apply alpha_equi; [ done |].
  apply nom_link_dlink, D.
Qed.

Lemma nom_par_dpar {P P' : nom_package} :
  disj P P' →
  nom_par P P' ≡ dpar P P'.
Proof.
  intros D.
  unfold dpar, move.
  auto with alpha_db nocore.
Qed.

Lemma par_dpar {P P' : nom_package} :
  disj P P' →
  (par P P' : raw_package) ≡ val (dpar P P').
Proof.
  intros D.
  change (par P P') with (val (nom_par P P')).
  apply alpha_equi; [ done |].
  apply nom_par_dpar, D.
Qed.

Lemma AdvantageD_AdvantageE (G G' A : nom_package) :
  disj A G ->
  disj A G' ->
  AdvantageD G G' A = AdvantageE G G' A.
Proof.
  intros D1 D2.
  unfold AdvantageD, AdvantageE.
  rewrite link_dlink ?link_dlink //.
Qed.

Lemma equi_pair {X Y : actionType} : equivariant (@pair X Y).
Proof.
  by apply equi2_prove => π x y.
Qed.

#[export] Hint Resolve equi_pair : alpha_db.

(* simple apply @subs_equi2_l fails when used near {fset Location}, so this
   is registered as a workaround *)

#[export] Hint Extern 7 (is_true (subs _ (_ _ _))) =>
  simple apply subs_supp_fsetUl : alpha_db.

#[export] Hint Extern 7 (is_true (subs _ (_ _ _))) =>
  simple apply subs_supp_fsetUr : alpha_db.

Lemma imfset_fdisjoint {T S : ordType} {A B : {fset T}} (f : T → S) : f @: A :#: f @: B → A :#: B.
Proof.
  move => /fdisjointP H.
  apply /fdisjointP => x H'.
  specialize (H (f x)).
  rewrite mem_imfset // in H.
  specialize (H Logic.eq_refl).
  move: H => /negP H.
  apply /negP => H''.
  apply H.
  by apply mem_imfset.
Qed.

(*
Lemma supp_imfset_Locations {S} {X : SuppOrd.type S} {A : {fset X}} {f : X → atom}
  : (∀ x, supp x = fset1 (f x)) → supp @: A = supp A.
Proof.
 *)

Lemma supp_fdisjoint {A B : {fset Location}} : disj A B → A :#: B.
Proof.
  intros D.
  rewrite /disj /supp //= in D.
  move: D => /fdisjointP D.
  apply /fdisjointP => x H.
  destruct x as [c n].
  apply /negP => H'.
  specialize (D (atomize n)).
  assert (atomize n \in fsetSupp A).
  { unfold fsetSupp.
    apply /bigcupP.
    eapply BigCupSpec.
    + apply H.
    + done.
    + rewrite in_fset1 //.
  }
  specialize (D H0).
  move: D => /negP D.
  apply D.
  unfold fsetSupp.
  apply /bigcupP.
  eapply BigCupSpec.
  + apply H'.
  + done.
  + rewrite in_fset1 //.
Qed.


Lemma AdvantageD_adv_equiv {L L' E} {G G' : nom_package} {ε : raw_package → R}
  {V1 : ValidPackage L Game_import E G} {V2 : ValidPackage L' Game_import E G'} :
  equivariant ε →
  G ≈[ ε ] G' →
  ∀ {LA} (A : nom_package), ValidPackage LA E A_export A → AdvantageD G G' A = ε A.
Proof.
  intros equieps adv LA A VA.
  pose (π := fresh ((L, G), (L', G')) (LA, A)).
  setoid_rewrite <- (@rename_alpha _ A π).
  rewrite AdvantageD_AdvantageE.
  1: rewrite -(absorb π (ε A)).
  1: rewrite equieps.
  1: rewrite adv //.
  all: unfold π => {π}.
  1,2: apply supp_fdisjoint.
  1-4: auto with alpha_db nocore.
Qed.

Lemma AdvantageD_perf {L L' E} {G G' : nom_package}
  {V1 : ValidPackage L Game_import E G} {V2 : ValidPackage L' Game_import E G'} :
  G ≈₀ G' →
  ∀ {LA} (A : nom_package), ValidPackage LA E A_export A → AdvantageD G G' A = 0.
Proof.
  intros adv LA A VA.
  eapply (AdvantageD_adv_equiv (ε := λ _, 0)).
  1: done.
  1: apply adv.
  apply VA.
Qed.

Lemma AdvantageD_perf_l {P P' Q A : nom_package} {LP LP' LA E}
  {V1 : ValidPackage LP Game_import E P}
  {V2 : ValidPackage LP' Game_import E P'}
  {V3 : ValidPackage LA E A_export A} :
  P ≈₀ P' → AdvantageD P Q A = AdvantageD P' Q A.
Proof.
  intros Indish.
  apply le_anti.
  apply /andP; split.
  - eadvantage_trans.
    erewrite (AdvantageD_perf Indish).
    + rewrite GRing.add0r //.
    + eassumption.
  - eadvantage_trans.
    erewrite (AdvantageD_perf (adv_equiv_sym _ _ _ _ _ _ _ _ Indish)).
    + rewrite GRing.add0r //.
    + eassumption.
Qed.

Lemma AdvantageD_perf_r {P P' Q A : nom_package} {LP LP' LA E}
  {V1 : ValidPackage LP Game_import E P}
  {V2 : ValidPackage LP' Game_import E P'}
  {V3 : ValidPackage LA E A_export A} :
  P ≈₀ P' → AdvantageD Q P A = AdvantageD Q P' A.
Proof.
  intros Indish.
  rewrite AdvantageD_sym.
  erewrite AdvantageD_perf_l; [| done].
  rewrite AdvantageD_sym //.
Qed.


(* NOM and automation *)

Definition exports : raw_package → Interface :=
  λ p, codomm (mapim (λ n '(X; Y; _), (n, (X, Y))) p).

Lemma exports_trimmed {p} : trimmed (exports p) p.
Proof.
  apply eq_fmap => n.
  unfold trimmed, trim, exports.
  rewrite filtermE.
  destruct (p n) eqn:eq; rewrite eq; [ simpl | done ].
  destruct t as [X [Y k]].
  rewrite (introT codommP); [ done |].
  exists n.
  rewrite mapimE eq //.
Qed.

Definition nom {L I} p {V : ValidPackage L I (exports p) p} : nom_package
  := nom_from_trimmed p exports_trimmed.


Lemma s_nom {L I p} {V : ValidPackage L I (exports p) p} : supp (nom p) = supp L.
Proof. done. Qed.
#[export] Hint Rewrite @s_nom : in_fset_eq.


#[export]
Instance nom_valid {L I p} (V : ValidPackage L I (exports p) p)
  : ValidPackage L I (exports p) (nom p).
Proof. apply V. Qed.

#[export]
Instance nom_ID_valid {I} : flat I → ValidPackage fset0 I I (nom_ID I).
Proof.
  apply valid_ID.
Qed.

Lemma val_nom {L I} p {V : ValidPackage L I (exports p) p}
  : val (nom p) = p.
Proof. done. Qed.

Lemma val_nom_link {P P'} : val (nom_link P P') = link (val P) (val P').
Proof. done. Qed.

Lemma val_nom_par {P P'} : val (nom_par P P') = par (val P) (val P').
Proof. done. Qed.


Lemma Game_import_flat : flat Game_import.
Proof.
  unfold Game_import, flat.
  rewrite -fset0E.
  intros n u v H.
  rewrite in_fset0 // in H.
Qed.

Lemma Parable_commut {P1 P2} : Parable P2 P1 → Parable P1 P2.
Proof. rewrite /Parable fdisjointC //. Qed.

Lemma Parable_nom_l {L I p' p} {V : ValidPackage L I (exports p) p}
  : Parable p p' → Parable (nom p) p'.
Proof. rewrite val_nom //. Qed.

Lemma Parable_nom_r {L I p p'} {V : ValidPackage L I (exports p') p'}
  : Parable p p' → Parable p (nom p').
Proof. rewrite val_nom //. Qed.

Lemma Parable_nom_ID_l {E p}
  : Parable (ID E) p → Parable (nom_ID E) p.
Proof. done. Qed.

Lemma Parable_nom_ID_r {E p}
  : Parable p (ID E) → Parable p (nom_ID E).
Proof. done. Qed.

Ltac dprove_rec :=
  lazymatch goal with
  | |- (ValidPackage ?L ?I ?E (val ?P)) =>
      tryif assert_fails (is_evar I)
        then (eapply valid_package_inject_import; dprove_rec) else
      tryif assert_fails (is_evar E)
        then (eapply valid_package_inject_export; dprove_rec) else
      lazymatch P with
      | (nom_link ?P1 ?P2) => eapply valid_link; dprove_rec
      | (nom_par ?P1 ?P2) => eapply valid_par; dprove_rec
      | (dlink ?P1 ?P2) => eapply dlink_valid; dprove_rec
      | (dpar ?P1 ?P2) => eapply dpar_valid; dprove_rec
      | (nom_ID ?I1) => eapply nom_ID_valid; dprove_rec
      | (rename ?pi ?P1) => eapply rename_valid; dprove_rec
      | (trimmed_nom ?P1) => eapply trimmed_valid
          (* | (nom (pack ?P1)) => apply pack_valid
      | (nom ?P1) => apply nom_valid
          (* apply valid_trim; apply (pack_valid P1) *)
           *)
      | _ => try eassumption
      end
    (*
  | |- (ValidPackage ?L ?I ?E (val (dlink ?P1 ?P2))) =>
      eapply dlink_valid;
      [ eapply valid_package_inject_export |];
      dprove_rec
  | |- (ValidPackage ?L ?I ?E (val (dpar ?P1 ?P2))) =>
      eapply dpar_valid_same_import;
      [ | eapply valid_package_inject_import
        | eapply valid_package_inject_import ] ;
            dprove_rec
  | |- (ValidPackage ?L ?I ?E (val (nom_ID ?M))) =>
      eapply nom_ID_valid; dprove_rec
  | |- (ValidPackage ?L ?I ?E (val (nom ?M))) =>
      apply valid_trim; apply (pack_valid M)
  | |- (ValidPackage ?L ?I ?E (val ?P)) =>
      try eassumption
     *)

  | |- is_true ( fsubset ?A ?B ) =>
      try assumption
  | |- (Parable (val (nom ?P1)) ?P2) =>
      apply Parable_nom_l ; dprove_rec
  | |- (Parable ?P1 (val (nom ?P2))) =>
      apply Parable_nom_r ; dprove_rec
  | |- (Parable (val (nom_ID ?E1)) ?P2) =>
      apply Parable_nom_ID_l ; dprove_rec
  | |- (Parable ?P1 (val (nom_ID ?E2))) =>
      apply Parable_nom_ID_r ; dprove_rec
  | |- (Parable ?P1 ?P2) =>
      try (assumption || (apply Parable_commut ; assumption)) ;
      try (unfold Parable; simpl; fset_solve)
      (* try ssprove_valid *)
  | |- (flat Game_import) =>
      apply Game_import_flat
  | |- (flat ?E) =>
      assumption || (eapply flat_valid_package; eassumption) || (try ssprove_valid)
  | |- (trimmed ?E1 (val (nom_ID ?E2))) =>
      apply trimmed_ID
  | |- (trimmed ?E ?P) =>
      (try assumption) || (try apply tr_trimmed) || dprove_trimmed
  | |- ?x =>
      done ||
      (* idtac x ; *)
      fail "What do I do with this?"
  end.
    
Ltac dprove_valid :=
  (* try unfold Game_import ; *)
  dprove_rec ;
  try (fset_solve; fail).


Lemma valid_idents {L I E} P {V : ValidPackage L I E P} : fsubset (idents E) (domm P).
Proof.
  destruct V.
  apply /fsubsetP.
  move => n /imfsetP H'.
  destruct H'.
  specialize (H x H0).
  destruct x as [m [S T]].
  destruct H as [f [H _]].
  subst; simpl in *.
  apply /dommP.
  exists (S; T; f).
  apply H.
Qed.

Lemma swish {L L' : {fset Location}} {I I' E E' : Interface} {P P' : nom_package} :
  ValidPackage L I E P → ValidPackage L' I' E' P' → Parable (nom_ID I) P' →
  flat I → trimmed E P → trimmed E' P' →
  dpar P P' ≡ dlink (dpar P (nom_ID E')) (dpar (nom_ID I) P').
Proof.
  intros V1 V2 V3.
  intros fl tr tr'.
  erewrite <- dinterchange; try dprove_valid.
  rewrite id_dlink //.
  rewrite dlink_id //.
  setoid_reflexivity.
Qed.

Lemma swash {L L' I I' E E'} {P P' : nom_package} :
  ValidPackage L I E P → ValidPackage L' I' E' P' → Parable P (nom_ID I') →
  flat I' → trimmed E P → trimmed E' P' →
  dpar P P' ≡ dlink (dpar (nom_ID E) P') (dpar P (nom_ID I')).
Proof.
  intros V1 V2 V3.
  intros fl tr tr'.
  erewrite <- dinterchange; try dprove_valid.
  rewrite id_dlink //.
  rewrite dlink_id //.
  reflexivity.
Qed.

Lemma Game_import_empty : ID (Game_import) = emptym.
Proof. rewrite /ID /Game_import -fset0E //. Qed.

Lemma dpar_empty_l {P} : dpar (nom_ID (Game_import)) P ≡ P.
Proof.
  exists (fresh (nom_ID Game_import) P)^-1%fperm.
  unfold dpar.
  rewrite rename_nom_par renameK.
  apply eq_nom_package.
  1,2: unfold rename; simpl.
  + unfold rename; simpl.
    rewrite imfset0 fset0U //.
  + rewrite Game_import_empty.
    unfold rename, par; simpl.
    apply eq_fmap => n.
    rewrite unionmE //.
Qed.

Lemma dpar_empty_r {P} : dpar P (nom_ID (Game_import)) ≡ P.
Proof.
  rewrite -> dpar_commut.
  + apply dpar_empty_l.
  + apply Parable_nom_ID_r.
    rewrite Game_import_empty.
    rewrite /Parable /domm //= -fset0E.
    apply fdisjoints0.
Qed.

#[export]
Hint Unfold Game_import : in_fset_eq.

#[export]
Hint Rewrite <- fset0E : in_fset_eq.

Lemma domm_ID {E} : domm (ID E) = idents E.
Proof. rewrite //= domm_ID //. Qed.

#[export] Instance Parable_Game_import_l {P} : Parable (ID Game_import) P.
Proof.
  unfold Parable, Game_import.
  rewrite /Parable domm_ID /idents -fset0E imfset0 fdisjoint0s //.
Qed.

#[export] Instance Parable_Game_import_r {P} : Parable P (ID Game_import).
Proof.
  unfold Parable, Game_import.
  rewrite /Parable domm_ID /idents -fset0E imfset0 fdisjoints0 //.
Qed.

Lemma dpar_game_l {LP LQ LR EP EQ ER IQ} {P Q R : nom_package}
  {VP : ValidPackage LP EQ EP P}
  {VQ : ValidPackage LQ IQ EQ Q}
  {VR : ValidPackage LR Game_import ER R}
  {trP : trimmed EP P}
  {trR : trimmed ER R} :
  (dpar (dlink P Q) R) ≡ dlink (dpar P R) Q.
Proof.
  rewrite -{2}(@dpar_empty_r Q).
  erewrite <- dinterchange.
  2-7: dprove_valid.
  2: apply Parable_Game_import_r.
  rewrite dlink_id; [ reflexivity | | assumption ].
  apply Game_import_flat.
Qed.

Lemma dpar_game_r {LP LQ LR EP EQ ER IQ} {P Q R : nom_package}
  {VP : ValidPackage LP EQ EP P}
  {VQ : ValidPackage LQ IQ EQ Q}
  {VR : ValidPackage LR Game_import ER R}
  {trP : trimmed EP P}
  {trR : trimmed ER R} :
  (dpar R (dlink P Q)) ≡ dlink (dpar R P) Q.
Proof.
  rewrite -{2}(@dpar_empty_l Q).
  erewrite <- dinterchange.
  2-7: dprove_valid.
  2: apply Parable_Game_import_l.
  rewrite dlink_id; [ reflexivity | | assumption ].
  apply Game_import_flat.
Qed.

Lemma AdvantageD_dpar_dlink_r (P₀ P₁ P₁' G G' A : nom_package)
  {LP₀ LP₁ LP₁'} {I₀ I₁ E₀ E₁}
  {V1 : ValidPackage LP₀ I₀ E₀ P₀}
  {V2 : ValidPackage LP₁ I₁ E₁ P₁}
  {V3 : ValidPackage LP₁' I₁ E₁ P₁'}
  {P1 : Parable (nom_ID I₀) P₁}
  {P2 : Parable (nom_ID I₀) P₁'} :
  flat I₀ → trimmed E₀ P₀ → trimmed E₁ P₁ → trimmed E₁ P₁' →
  AdvantageD (dlink (dpar P₀ P₁) G) (dlink (dpar P₀ P₁') G') A
    = AdvantageD (dlink (dpar (nom_ID I₀) P₁) G) (dlink (dpar (nom_ID I₀) P₁') G') (dlink A (dpar P₀ (nom_ID E₁))).
Proof.
  intros fl0 tr0 tr1 tr2.
  rewrite <- AdvantageD_dlink.
  erewrite dlink_assoc.
  erewrite dlink_assoc.
  erewrite <- @swish, <- @swish.
  all: dprove_valid.
Qed.

Lemma AdvantageD_dpar_r (G₀ G₁ G₁' A : nom_package) {L₀ L₁ L₁' : {fset Location}} {E₀ E₁}
  {V1 : ValidPackage L₀ Game_import E₀ G₀}
  {V2 : ValidPackage L₁ Game_import E₁ G₁}
  {V3 : ValidPackage L₁' Game_import E₁ G₁'} :
  trimmed E₀ G₀ → trimmed E₁ G₁ → trimmed E₁ G₁' →
  AdvantageD (dpar G₀ G₁) (dpar G₀ G₁') A = AdvantageD G₁ G₁' (dlink A (dpar G₀ (nom_ID E₁))).
Proof.
  intros tr0 tr1 tr2.
  rewrite -AdvantageD_dlink.
  rewrite swish.
  2-4: try dprove_valid.
  rewrite dpar_empty_l.
  rewrite swish.
  2-4: try dprove_valid.
  rewrite dpar_empty_l.
  reflexivity.
Qed.

Lemma domm_idents {L I E P} {V : ValidPackage L I E P} : trimmed E P → domm P = idents E.
Proof.
  intros tr.
  apply reflection_nonsense.
  rewrite eqEfsubset.
  rewrite valid_idents.
  rewrite domm_trimmed //.
Qed.

Lemma AdvantageD_dpar_dlink_l (P₀ P₀' P₁ G G' A : nom_package)
  {LP₀ LP₀' LP₁} {I₀ I₁ E₀ E₁}
  {V1 : ValidPackage LP₀ I₀ E₀ P₀}
  {V2 : ValidPackage LP₀' I₀ E₀ P₀'}
  {V3 : ValidPackage LP₁ I₁ E₁ P₁}
  {P1 : Parable P₀ (nom_ID I₁)}
  {P2 : Parable P₀' (nom_ID I₁)} :
  flat I₁ → trimmed E₀ P₀ → trimmed E₀ P₀' → trimmed E₁ P₁ →
  AdvantageD (dlink (dpar P₀ P₁) G) (dlink (dpar P₀' P₁) G') A
    = AdvantageD (dlink (dpar P₀ (nom_ID I₁)) G) (dlink (dpar P₀' (nom_ID I₁)) G')
      (dlink A (dpar (nom_ID E₀) P₁)).
Proof.
  intros fl1 tr0 tr1 tr2.
  (* Why do these have to be erewrite? And other places *)
  erewrite <- AdvantageD_dlink.
  erewrite dlink_assoc, dlink_assoc.
  erewrite <- @swash, <- @swash.
  all: dprove_valid.
Qed.

Lemma AdvantageD_dpar_l (G₀ G₀' G₁ A : nom_package) {L₀ L₀'  L₁} {E₀ E₁}
  {V1 : ValidPackage L₀ Game_import E₀ G₀}
  {V2 : ValidPackage L₀' Game_import E₀ G₀'}
  {V3 : ValidPackage L₁ Game_import E₁ G₁}
  {P : Parable (nom_ID E₀) G₁} :
  trimmed E₀ G₀ → trimmed E₁ G₁ → trimmed E₀ G₀' →
  AdvantageD (dpar G₀ G₁) (dpar G₀' G₁) A = AdvantageD G₀ G₀' (dlink A (dpar (nom_ID E₀) G₁)).
Proof.
  intros tr0 tr1 tr2.
  rewrite -AdvantageD_dlink.
  rewrite swash.
  2-4: try dprove_valid.
  rewrite dpar_empty_r.
  rewrite swash.
  2-4: try dprove_valid.
  rewrite dpar_empty_r.
  reflexivity.
Qed.


Definition AdvantageP GG A := AdvantageD (GG true) (GG false) A.
