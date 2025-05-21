(*This is a part of the implementation of the state-separated game-based proof of security for the NaCl crypto_box authenticated encryption scheme.
This file contains the specification for the GAE game and following lemmas*)

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

Import Num.Def.
Import Num.Theory.
Import Order.POrderTheory.

#[local] Open Scope package_scope.
#[local] Open Scope ring_scope.

From NominalSSP Require Import AE HYBRID KEY NBSES NIKE SAE GAE GSAE Reductions.

Import AE HYBRID KEY NBSES NIKE SAE GAE GSAE Reductions.

Module GH.


Definition I_GH_ID_COMP (N : NIKE_scheme) :=
  [interface
    [ SET ]  : { (('pk N × 'pk N) × 'shared_key N) ~> 'unit } ;
    [ CSET ] : { (('pk N × 'pk N) × 'shared_key N) ~> 'unit } ;
    [ GET ]  : { ('pk N × 'pk N) ~> 'shared_key N }
].


#[export] Hint Unfold I_GH_ID_COMP I_HYBRID_IN I_HYBRID_OUT I_AE_IN I_AE_OUT I_KEY_OUT I_SAE_OUT I_GSAE_OUT: in_fset_eq.

Definition GH (E : NBSES_scheme) (N : NIKE_scheme) (I : inj ('shared_key N) ('k E)) i qset (b : 'bool):
  raw_module := (HYBRID E N I i qset) ∘ ((ID (I_GH_ID_COMP N) || SAE E b) ∘ KEY N qset true).

Lemma GH_valid (E : NBSES_scheme) (N: NIKE_scheme) (I : inj ('shared_key N) ('k E)) i qset (b : 'bool) :
  ValidPackage (GH E N I i qset b).(loc) [interface] (I_GAE_OUT E N) (GH E N I i qset b).
Proof.
unfold GH. nssprove_valid. Qed.

 Definition R (i : 'nat) (c : 'nat) (f : 'option 'unit)
  := ((c > i)%N = isSome f).

Notation inv i N E := (
  heap_ignore (fset [:: ])
  (*⋊ couple_rhs (HC_loc N) (M_loc E N) (λ c f , R i c f)*)
).
 
Lemma GAE_HYBRID_perfect {E N} qset {I : inj ('shared_key N) ('k E)} b :
perfect (I_GAE_OUT E N)
  (GAE E N qset I b)
  (HYBRID E N I (if b then 0 else qset) qset ∘ (ID (I_GSAE_OUT E) || (KEY N qset true) ) ∘ GSAE E true).
Proof.
(*unfold GAE, GSAE.
nssprove_share.
- eapply prove_perfect.
Check eq_rel_perf_ind.
eapply (eq_rel_perf_ind _ _ (inv (if b then 0 else qset) N E)). Unshelve.
5, 6 : nssprove_valid.
1: ssprove_invariant ; fset_solve.
simplify_eq_rel arg.
+ ssprove_code_simpl. simplify_linking. simpl. erewrite par_commut.
2: admit. simpl. 
ssprove_code_simpl. simplify_linking. *)
Admitted.

Lemma HYBRID_succ_perfect {E N i} qset {I : inj ('shared_key N) ('k E)} :
perfect (I_GAE_OUT E N)
  (HYBRID E N I i qset ∘ (ID (I_GSAE_OUT E) || (KEY N qset true)) ∘ GSAE E false)
  (HYBRID E N I i.+1 qset ∘ (ID (I_GSAE_OUT E) || (KEY N qset true)) ∘ GSAE E true).
Proof.
Admitted.


Theorem Lemma3_Adv_GAE {E N} qset (I : inj ('shared_key N) ('k E)) (A : adversary (I_GAE_OUT E N)) :
  AdvFor (GAE E N qset I) A <=
  \sum_(0 <= i < qset) AdvFor (GSAE E) (A ∘ HYBRID E N I i qset ∘ ((ID (I_GSAE_OUT E)) || (KEY N qset true))).
Proof.
rewrite (AdvFor_perfect (GAE_HYBRID_perfect qset)).
elim: {+ 3 6}qset => [| j IH ].
- rewrite Adv_same big_nil //.
- rewrite big_nat_recr //=.
  nssprove_adv_trans ( HYBRID E N I j qset ∘ ((ID (I_GSAE_OUT E)) || (KEY N qset true)) ∘ GSAE E true)%sep.
  apply lerD.
    1: apply IH.
  erewrite <- (Adv_perfect_r (HYBRID_succ_perfect qset)).
  unfold AdvFor.
  rewrite Adv_sep_link.
  rewrite Adv_sep_link.
  rewrite sep_link_assoc.
  done.
Qed.


End GH.