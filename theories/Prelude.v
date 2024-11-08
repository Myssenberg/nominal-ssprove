Set Warnings "-notation-overridden,-ambiguous-paths,-notation-incompatible-format".
From mathcomp Require Import all_ssreflect all_algebra reals distr
  fingroup.fingroup realsum ssrnat ssreflect ssrfun ssrbool ssrnum eqtype choice
  seq.
Set Warnings "notation-overridden,ambiguous-paths,notation-incompatible-format".

From Coq Require Import Utf8 Lia.
From Equations Require Import Equations.
Require Equations.Prop.DepElim.

Set Equations With UIP.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".
Set Primitive Projections.

Import Num.Def.
Import Num.Theory.
Import Order.POrderTheory.

From extructures Require Import ord fset fmap.

From Crypt Require Export pkg_composition Prelude Package.

From NominalSSP Require Export FsetSolve Nominal Fresh Pr NomPackage Disjoint SSProve.
Export FsetSolve.


Import PackageNotation.
#[local] Open Scope ring_scope.
#[local] Open Scope package_scope.


Hint Extern 10 (ValidCode ?L ?I ?c.(prog)) =>
  eapply valid_injectLocations;
    [| eapply valid_injectMap;
      [| eapply prog_valid ]]; fset_solve
  : typeclass_instances ssprove_valid_db.

Hint Extern 10 (ValidCode ?L ?I (?p ∙ ?c.(prog))) =>
  eapply valid_injectLocations;
    [| eapply valid_injectMap;
      [| eapply mcode_valid, prog_valid ]]; fset_solve
  : typeclass_instances ssprove_valid_db.

Hint Extern 10 (is_true (_ \in _)) =>
  fset_solve : typeclass_insatnces ssprove_valid_db.


Lemma idents_cons {n a b}
  : idents (fset (cons (n, a) b)) = n |: idents (fset b).
Proof. 
  unfold idents.
  rewrite 2!imfset_fset //=.
  rewrite fset_cons //.
Qed.

(* add rule based on idents fset0? *)
Lemma idents0 : idents fset0 = fset0.
Proof. by rewrite /idents imfset0. Qed.

#[export] Hint Rewrite @idents_cons @idents0 : in_fset_eq.

#[export] Hint Rewrite @domm_set @domm0 @domm_ID : in_fset_eq.

Lemma domm_link {P Q} : domm (link P Q) = domm P.
Proof. apply domm_map. Qed.

Lemma domm_par {P Q} : domm (par P Q) = domm P :|: domm Q.
Proof. apply domm_union. Qed.

#[export] Hint Rewrite @domm_link @domm_par : in_fset_eq.

#[export] Hint Unfold Location : in_fset_eq.


(* Location disjointness hints *)

Lemma supp1 {X : nomOrdType} {x : X} : supp (fset1 x) = supp x.
Proof. apply fsetSupp1. Qed.

Lemma supp_cons {X : nomOrdType} {x : X} {xs}
  : supp (fset (cons x xs)) = supp x :|: supp (fset xs).
Proof. by rewrite fset_cons supp_fsetU supp1. Qed.

Lemma supp_nil {X : nomOrdType}
  : supp (fset (@nil X)) = fset0.
Proof. by rewrite -fset0E supp0. Qed.

Lemma supp_Location (l : Location) : supp l = fset1 (atomize l.π2).
Proof. destruct l. rewrite /supp //. Qed.

#[export] Hint Rewrite @supp_cons @supp_nil @supp_Location : in_fset_eq.

Lemma rename_fset0 {X : actionOrdType} {π} : π ∙ fset0 = @fset0 X.
Proof. rewrite /rename /= imfset0 //. Qed.

#[export] Hint Rewrite <- @supp_equi : in_fset_eq.
#[export] Hint Rewrite @rename_fset0 @supp0 : in_fset_eq.

Lemma supp_trimmed_package {L I E} (P : trimmed_package L I E)
  : supp (trimmed_nom P) = supp L.
Proof.
  done.
Qed.

#[export] Hint Rewrite @supp_trimmed_package : in_fset_eq.

Lemma supp_nom_package (P : nom_package) : supp P = supp (loc P).
Proof. done. Qed.
(* this hint does not reduce nicely with fset_solve
#[export] Hint Rewrite @supp_nom_package : in_fset_eq.
 *)

#[export] Hint Rewrite @s_nom_par @s_nom_link : in_fset_eq.

Ltac dprove_convert_solve :=
  match goal with
  | [ H : is_true (disj _ _) |- _ ] => move: H; dprove_convert_solve
  | _ => unfold disj; fset_solve
  end.

Ltac dprove_convert_once :=
  (rewrite -> nom_link_dlink by dprove_convert_solve)
  || (rewrite -> nom_par_dpar by dprove_convert_solve)
  || (rewrite -> rename_alpha)
  || reflexivity.

Ltac dprove_convert :=
  repeat dprove_convert_once.


(* rename simplification *)

Lemma rename_bind {A B} {π} {c : raw_code A} {k : A → raw_code B}
  : π ∙ bind c k = bind (π ∙ c) (λ a, π ∙ k a).
Proof.
  rewrite /rename //=.
  induction c => //=.
  all: f_equal => //=.
  all: apply functional_extensionality => y //=.
Qed.

Lemma rename_ret {A : choiceType} {π} (a : A) :
  π ∙ ret a = ret a.
Proof. done. Qed.

Lemma rename_assert {A} {π b k}
  : π ∙ @assertD A b k = assertD b (λ x, π ∙ (k x)).
Proof.
  destruct b; done.
Qed.

Lemma rename_let {A B C : choiceType} {π} (ab : prod A B) (f : A → B → raw_code C) :
  π ∙ (let '(a, b) := ab in f a b) = let '(a, b) := ab in π ∙ f a b.
Proof. by destruct ab. Qed.

Lemma rename_code {π} {A L I} {c : code L I A} : π ∙ prog c = {code π ∙ c}.
Proof. done. Qed.

Lemma rename_scheme {I A} (c : code fset0 I A) π
  : π ∙ prog c = prog c.
Proof.
  destruct c as [c V].
  simpl.
  induction V => //=.
  - etransitivity.
    2: apply f_equal.
    2: apply functional_extensionality, H1.
    done.
  - etransitivity.
    2: apply f_equal.
    2: apply functional_extensionality, H0.
    done.
Qed.


#[export] Hint Extern 50 (_ = code_link _ _) =>
  rewrite code_link_scheme
  : ssprove_code_simpl.

#[export] Hint Extern 50 (_ = rename _ (@assertD ?A _ _)) =>
  rewrite (@rename_assert A)
  : ssprove_code_simpl.

#[export] Hint Extern 50 (_ = rename _ (bind _ _)) =>
  rewrite rename_bind
  : ssprove_code_simpl.

#[export] Hint Extern 50 (_ = rename _ (ret _)) =>
  rewrite rename_ret
  : ssprove_code_simpl.

#[export] Hint Extern 50 (_ = rename _ (let '(_, _) := _ in _)) =>
  rewrite rename_let
  : ssprove_code_simpl.
