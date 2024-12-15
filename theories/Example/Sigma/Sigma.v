
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

From NominalSSP Require Import Prelude.
Import Num.Def Num.Theory Order.POrderTheory.
Import PackageNotation.

#[local] Open Scope ring_scope.

Record raw_sigma :=
  { Statement : choice_type
  ; Witness : choice_type
  ; Message : choice_type
  ; Challenge : choice_type
  ; Response : choice_type

  ; locs : {fset Location}

  ; R : Statement → Witness → bool

  ; commit :
    ∀ (h : Statement) (w : Witness),
      code locs [interface] Message

  ; response :
    ∀ (h : Statement) (w : Witness)
      (a : Message) (e : Challenge),
      code locs [interface] Response

  ; verify :
    ∀ (h : Statement) (a : Message) (e : Challenge)
      (z : Response),
      bool

  ; simulate :
    ∀ (h : Statement) (e : Challenge),
      code fset0 [interface] (Message × Response)

  ; extractor :
    ∀ (h : Statement) (a : Message)
      (e : Challenge) (e' : Challenge)
      (z : Response) (z' : Response),
      'option Witness
  }.

#[local] Open Scope package_scope.

Notation " 'statement p " := (Statement p)
  (in custom pack_type at level 2, p constr at level 20).

Notation " 'witness p " := (Witness p)
  (in custom pack_type at level 2, p constr at level 20).

Notation " 'message p " := (Message p)
  (in custom pack_type at level 2, p constr at level 20).

Notation " 'challenge p " := (Challenge p)
  (in custom pack_type at level 2, p constr at level 20).

Notation " 'response p " := (Response p)
  (in custom pack_type at level 2, p constr at level 20).

Notation " 'statement p " := (Statement p)
  (at level 3) : package_scope.

Notation " 'witness p " := (Witness p)
  (at level 3) : package_scope.

Notation " 'message p " := (Message p)
  (at level 3) : package_scope.

Notation " 'challenge p " := (Challenge p)
  (at level 3) : package_scope.

Notation " 'response p " := (Response p)
  (at level 3) : package_scope.


(* Section: Correct *)

Definition chInput p := ('statement p × 'witness p) × 'challenge p.
Notation " 'input p " :=
  (chInput p)
  (in custom pack_type at level 2, p constr).

Definition RUN : nat := 1.

Definition ICorrect p :=
  [interface #val #[ RUN ] : ('input p) → 'bool ].

Definition Correct_real p :
  trimmed_package p.(locs) Game_import (ICorrect p) :=
  [trimmed_package
    #def #[ RUN ] ('(h, w, e) : 'input p) : 'bool {
      #assert p.(R) h w ;;
      a ← p.(commit) h w ;;
      z ← p.(response) h w a e ;;
      @ret 'bool (p.(verify) h a e z)
    }
  ].

Definition Correct_ideal p :
  trimmed_package fset0 Game_import (ICorrect p) :=
  [trimmed_package
    #def #[ RUN ] ('(h, w, e) : 'input p) : 'bool {
      #assert p.(R) h w ;;
      @ret 'bool true
    }
  ].

Definition Correct p b :=
  if b then Correct_real p : nom_package else Correct_ideal p.

(* Main security statement for Special Honest-Verifier Zero-Knowledge. *)
Definition Adv_Correct p ε :=
  ∀ (A : nom_package),
  ValidPackage (loc A) (ICorrect p) A_export A →
  AdvantageP (Correct p) A <= ε A.


(* Section: SHVZK *)

Definition TRANSCRIPT : nat := 0.

Definition chTranscript (p : raw_sigma) :=
  (('statement p × 'message p) × 'challenge p) × 'response p.
Notation " 'transcript p " :=
  (chTranscript p) (in custom pack_type at level 2, p constr).

Notation Transcript p := 
  [interface #val #[ TRANSCRIPT ] : ('input p) → 'transcript p ].

Definition SHVZK_real p :
  trimmed_package p.(locs) Game_import (Transcript p) :=
  [trimmed_package
    #def #[ TRANSCRIPT ] ('(h, w, e) : 'input p) : ('transcript p) {
      #assert p.(R) h w ;;
      a ← p.(commit) h w ;;
      z ← p.(response) h w a e ;;
      @ret (chTranscript p) (h, a, e, z)
    }
  ].

Definition SHVZK_ideal p :
  trimmed_package fset0 Game_import (Transcript p) :=
  [trimmed_package
    #def #[ TRANSCRIPT ] ('(h, w, e) : 'input p) : ('transcript p) {
      #assert p.(R) h w ;;
      '(a, z) ← p.(simulate) h e ;;
      @ret (chTranscript p) (h, a, e, z)
    }
  ].

Definition SHVZK p b :=
  if b then SHVZK_real p : nom_package else SHVZK_ideal p.

Definition Adv_SHVZK p ε :=
  ∀ (A : nom_package),
  ValidPackage (loc A) (Transcript p) A_export A →
  AdvantageP (SHVZK p) A <= ε A.


(* Section: Relating SHVZK and correctness *)

Definition Verify_call p :
  trimmed_package fset0 (Transcript p) (ICorrect p) :=
  [trimmed_package
    #def #[ RUN ] ('(h, w, e) : 'input p) : 'bool {
      #import {sig #[ TRANSCRIPT ] : ('input p) → 'transcript p} as Transcript ;;
      '(h, a, e, z) ← Transcript (h, w, e) ;;
      @ret 'bool (p.(verify) h a e z)
    }
  ].

Lemma Verify_SHVZK_Correct_perf {LA} p (A : nom_package)
  (VA : ValidPackage LA (ICorrect p) A_export A)
  : AdvantageD (dlink (Verify_call p) (SHVZK_real p)) (Correct_real p) A = 0.
Proof.
  rewrite -nom_link_dlink; [| dprove_convert_solve ].
  eapply AdvantageD_perf; [| exact VA ].
  eapply eq_rel_perf_ind_eq.
  simplify_eq_rel hwe.
  ssprove_code_simpl; rewrite cast_fun_K.
  destruct hwe as [[h w] e].
  ssprove_code_simpl_more.
  ssprove_sync_eq => _.
  ssprove_code_simpl.
  eapply rsame_head => a.
  eapply rsame_head => z.
  eapply r_ret; auto.
Qed.

Definition Correct_sim p := dlink (Verify_call p) (SHVZK_ideal p).

Lemma Adv_Correct_sim p A (VA : ValidPackage (loc A) (ICorrect p) A_export A) :
  AdvantageD (Correct_sim p) (Correct_ideal p) A
    <= AdvantageP (SHVZK p) (dlink A (Verify_call p)) + AdvantageP (Correct p) A.
Proof.
  advantage_trans (dlink (Verify_call p) (SHVZK_real p)).
  apply lerD.
  + rewrite AdvantageD_dlink.
    rewrite AdvantageD_sym.
    apply le_refl.
  + advantage_trans (Correct_real p).
    rewrite Verify_SHVZK_Correct_perf.
    rewrite GRing.add0r.
    apply le_refl.
Qed.


(* Section: 2-special-soundness *)

Definition SOUNDNESS : nat := 4.

Definition chOpening p := 'challenge p × 'response p.
Notation " 'soundness p " :=
  (chProd (chProd ('statement p) ('message p)) (chProd (chOpening p) (chOpening p)))
  (in custom pack_type at level 2, p constr).

Notation Soundness p :=
  [interface #val #[ SOUNDNESS ] : ('soundness p) → 'bool ].

Definition Special_Soundness_f p :
  trimmed_package fset0 Game_import (Soundness p) :=
  [trimmed_package
    #def #[ SOUNDNESS ] ('((h, a), ((e, z), (e', z'))) : 'soundness p) : 'bool {
      #assert p.(verify) h a e z ;;
      #assert p.(verify) h a e' z' ;;
      #assert (e != e') ;;
      let ow := p.(extractor) h a e e' z z' in
      @ret 'bool (if ow is Some w then p.(R) h w else false)
    }
  ].

Definition Special_Soundness_t p :
  trimmed_package fset0 Game_import (Soundness p) :=
  [trimmed_package
    #def #[ SOUNDNESS ] ('((h, a), ((e, z), (e', z'))) : 'soundness p) : 'bool {
      #assert p.(verify) h a e z ;;
      #assert p.(verify) h a e' z' ;;
      #assert (e != e') ;;
      @ret 'bool true
    }
  ].

Definition Special_Soundness p b :=
  if b then Special_Soundness_t p : nom_package else Special_Soundness_f p.

Definition Adv_Special_Soundness p ε :=
  ∀ (A : nom_package),
  ValidPackage (loc A) (Soundness p) A_export A →
  AdvantageP (Special_Soundness p) A <= ε A.
