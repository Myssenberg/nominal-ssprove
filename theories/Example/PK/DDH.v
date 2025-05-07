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
Import Num.Def Num.Theory Order.POrderTheory.
Import PackageNotation.
#[local] Open Scope ring_scope.
#[local] Open Scope package_scope.
Import GroupScope GRing.Theory.


Module DDH (GP : GroupParam).

Module GT := GroupTheorems GP.
Import GP GT.


#[export] Instance Positive_el : Positive #|el|.
Proof. apply /card_gt0P. by exists g. Qed.

#[export] Instance Positive_exp : Positive #|exp|.
Proof. apply /card_gt0P. by exists 0. Qed.

Notation " 'el " := 'fin #|el|
  (in custom pack_type at level 2).

Notation " 'el " := 'fin #|el|
  (at level 3) : package_scope.

Notation " 'exp " := 'fin #|exp|
  (in custom pack_type at level 2).

Notation " 'exp " := 'fin #|exp|
  (at level 3) : package_scope.

Definition op_g : 'el := fto g.

Definition op_mul (x y : 'el) : 'el :=
   fto (otf x * otf y).

Definition op_exp (x : 'el) (a : 'exp) : 'el :=
  fto (otf x ^+ otf a).

Definition op_expn (x : 'el) (a : 'exp) : 'el :=
  fto (otf x ^- otf a).


Lemma bij_op_exp : bijective (op_exp op_g).
Proof.
  eexists (λ a, fto (log (otf a))).
  + intros x.
    rewrite /op_exp /op_g 2!otf_fto.
    rewrite -{2}(fto_otf x).
    f_equal.
    by apply expg_log.
  + intros x.
    rewrite /op_exp /op_g 2!otf_fto.
    rewrite -{2}(fto_otf x).
    f_equal.
    by apply log_expg.
Qed.

Lemma bij_op_mult_op_exp m : bijective (λ x, op_mul m (op_exp op_g x)).
Proof.
  eexists (λ a, fto (log ((otf m)^-1 * otf a))).
  + intros x.
    rewrite /op_exp /op_g 3!otf_fto.
    rewrite -{2}(fto_otf x).
    f_equal.
    rewrite mulKg.
    by apply expg_log.
  + intros x.
    rewrite /op_mul /op_exp /op_g 3!otf_fto.
    rewrite -{2}(fto_otf x).
    f_equal.
    rewrite -{2}(mulKVg (otf m) (otf x)).
    f_equal.
    by apply log_expg.
Qed.


Definition GETA := 0%N.
Definition GETBC := 1%N.

Definition I_DDH :=
  [interface
    #val #[ GETA ] : 'unit → 'el ;
    #val #[ GETBC ] : 'unit → 'el × 'el
  ].

Definition mga_loc : Location := ('option 'el; 3%N).

Definition DDH bit :
  game I_DDH :=
  [module fset [:: mga_loc ] ;
    #def #[ GETA ] ('tt : 'unit) : 'el {
      a ← sample uniform #|exp| ;;
      #put mga_loc := Some (op_exp op_g a) ;;
      ret (op_exp op_g a)
    } ;
    #def #[ GETBC ] ('tt : 'unit) : 'el × 'el {
      ga ← getSome mga_loc ;;
      #put mga_loc := None ;;
      b ← sample uniform #|exp| ;;
      if bit then
        @ret ('el × 'el) (op_exp op_g b, op_exp ga b)
      else
        c ← sample uniform #|exp| ;;
        @ret ('el × 'el) (op_exp op_g b, op_exp op_g c)
    }
  ].

End DDH.
