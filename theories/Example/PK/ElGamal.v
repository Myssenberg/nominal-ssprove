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

From NominalSSP Require Import DDH Misc Scheme.


Module ElGamal (GP : GroupParam).

Module DDH' := DDH GP.
Import PKScheme DDH'.

Module GT := GroupTheorems GP.
Import GP GT.

Definition elgamal : pk_scheme := {|
    Sec := 'fin #|exp|
  ; Pub := 'fin #|el|
  ; Mes := 'fin #|el|
  ; Cip := 'fin #|el| × 'fin #|el|
  ; sample_Cip :=
    {code
      c₁ ← sample uniform #|el| ;;
      c₂ ← sample uniform #|el| ;;
      ret (c₁, c₂)
    }
  ; keygen :=
    {code
      sk ← sample uniform #|exp| ;;
      ret (sk, op_exp op_g sk)
    }
  ; enc := λ pk m,
    {code
      r ← sample uniform #|exp| ;;
      ret (op_exp op_g r, op_mul m (op_exp pk r))
    }
  ; dec := λ sk c,
    {code
      ret (op_mul (snd c) (op_expn (fst c) sk))
    }
  |}.


Theorem correct_elgamal : CORR0 elgamal ≈₀ CORR1 elgamal.
Proof.
  apply eq_rel_perf_ind_eq.
  simplify_eq_rel m.
  apply r_const_sample_L.
  1: apply LosslessOp_uniform.
  intros sk.
  apply r_const_sample_L.
  1: apply LosslessOp_uniform.
  intros r.
  apply r_ret => s0 s1.
  split; subst; [| done ].
  unfold op_mul, op_exp, op_g, op_expn.
  rewrite !otf_fto expgAC -mulgA mulgV mulg1 fto_otf //.
Qed.


Definition stop_loc : Location := ('option 'unit; 4%N).

Definition RED_loc :=
  fset [:: stop_loc ].

Definition RED :
  trimmed_package RED_loc I_DDH (I_PK_OTSR elgamal) :=
  [trimmed_package
    #def #[ GET ] (_ : 'unit) : 'el {
      #import {sig #[ GETA ] : 'unit → 'el } as GETA ;;
      getNone stop_loc ;;
      #put stop_loc := Some tt ;;
      pk ← GETA tt ;;
      @ret 'el pk
    } ;
    #def #[ QUERY ] (m : 'el) : 'el × 'el {
      #import {sig #[ GETBC ] : 'unit → 'el × 'el } as GETBC ;;
      _ ← getSome stop_loc ;;
      '(r, sh) ← GETBC tt ;;
      @ret ('el × 'el) (r, op_mul m sh)
    }
  ].

#[export] Instance valid_RED_DDH0
  : ValidPackage (RED_loc :|: DDH0_loc)
      Game_import (I_PK_OTSR elgamal) (nom_link RED DDH0).
Proof. dprove_valid. Qed.

#[export] Instance valid_RED_DDH1
  : ValidPackage (RED_loc :|: DDH1_loc)
      Game_import (I_PK_OTSR elgamal) (nom_link RED DDH1).
Proof. dprove_valid. Qed.

#[local] Hint Unfold DDH0_loc DDH1_loc PK_OTSR_loc RED_loc : in_fset_eq.

Definition Rel0
  (flag : flag_loc) (mpk : mpk_loc elgamal)
  (stop : stop_loc) (mga : mga_loc) : Prop
  := (isSome mpk == isSome stop)%B &&
      if flag then stop && ~~ mga else
        (if stop then (mpk == mga)%B else ~~ mpk).

Notation inv0 := (
  heap_ignore (PK_OTSR_loc elgamal :|: (RED_loc :|: DDH0_loc))
  ⋊ quad flag_loc (mpk_loc elgamal) stop_loc mga_loc Rel0
).

Lemma inv0_Invariant :
  Invariant (PK_OTSR_loc elgamal) (RED_loc :|: DDH0_loc) inv0.
Proof.
  ssprove_invariant; [ apply fsubsetxx | done ].
Qed.

Lemma pk_ots0_perf : PK_OTSR0 elgamal ≈₀ nom_link RED DDH0.
Proof.
  apply (eq_rel_perf_ind _ _ inv0).
  1: exact inv0_Invariant.
  simplify_eq_rel m.
  1,2: ssprove_code_simpl.
  + eapply r_get_remember_lhs => mpk.
    eapply r_get_remember_rhs => stop.
    eapply (rpre_learn). {
      intros s0 s1 [[[_ I1] I2] I3].
      rewrite /quad I2 I3 /Rel0 in I1.
      move: I1 => /andP [I1 _].
      apply I1.
    }
    move=> /eqP ?.
    destruct mpk, stop => //=.
    1: apply r_fail.
    ssprove_swap_rhs 0%N.
    ssprove_sync => sk.
    eapply r_put_lhs, r_put_rhs, r_put_rhs.
    ssprove_restore_mem.
    2: by eapply r_ret.

    ssprove_invariant. {
      apply preserve_update_r_ignored_heap_ignore.
      1: fset_solve.
      apply preserve_update_r_ignored_heap_ignore.
      1: fset_solve.
      apply preserve_update_l_ignored_heap_ignore.
      1: fset_solve.
      intros h0 h1 H.
      apply H.
    }
    intros s0 s1 [[I1 I2] I3].
    rewrite /quad /Rel0 //= in I1 |- *.
    get_heap_simpl.
    simpl.
    move: I1.
    elim: (get_heap s0 flag_loc) => //= _ H.
    rewrite /quad I2 I3 /Rel0 in H.
    done.

  + eapply r_get_remember_lhs => mpk.
    eapply r_get_remember_rhs => stop.
    eapply (rpre_learn). {
      intros s0 s1 [[[_ I1] I2] I3].
      rewrite /quad I2 I3 /Rel0 in I1.
      move: I1 => /andP [I1 _].
      apply I1.
    }
    move=> /eqP ?.
    destruct mpk, stop => //=.
    2: apply r_fail.
    ssprove_code_simpl_more.
    eapply r_get_remember_lhs => flag.
    eapply r_get_remember_rhs => mga.
    eapply (rpre_learn). {
      intros h0 h1 [[[[[_ I1] I2] I3] I4] I5].
      rewrite /quad I2 I3 I4 I5 /Rel0 in I1.
      apply I1.
    }
    destruct flag, mga.
    1,4: done.
    1: intros _; apply r_fail.
    move=> //= /eqP E.
    injection E => {}E.
    subst.
    eapply r_put_lhs, r_put_rhs.
    ssprove_sync => r.

    ssprove_restore_mem.
    2: by eapply r_ret.

    ssprove_invariant. {
      unfold PK_OTSR_loc, RED_loc, DDH0_loc.
      apply preserve_update_r_ignored_heap_ignore.
      1: fset_solve.
      apply preserve_update_l_ignored_heap_ignore.
      1: fset_solve.
      intros h0 h1 H.
      apply H.
    }
    intros h0 h1 [[[[I1 I2] I3] I4] I5].
    simpl.
    unfold quad, Rel0.
    get_heap_simpl.
    rewrite //= I2 I3 //.
Qed.

Definition Rel1
  (flag : flag_loc) (mpk : mpk_loc elgamal)
  (stop : stop_loc) (mga : init_loc) : Prop
  := (isSome mpk == isSome stop)%B &&
      if flag then stop && ~~ mga else
        (if stop then (isSome mpk == isSome mga)%B else ~~ mpk).

Notation inv1 := (
  heap_ignore (PK_OTSR_loc elgamal :|: (RED_loc :|: DDH1_loc))
  ⋊ quad flag_loc (mpk_loc elgamal) stop_loc init_loc Rel1
).

Lemma inv1_Invariant :
  Invariant (PK_OTSR_loc elgamal) (RED_loc :|: DDH1_loc) inv1.
Proof.
  ssprove_invariant; [ apply fsubsetxx | done ].
Qed.

Lemma pk_ots1_perf : PK_OTSR1 elgamal ≈₀ nom_link RED DDH1.
Proof.
  apply (eq_rel_perf_ind _ _ inv1).
  1: exact inv1_Invariant.
  simplify_eq_rel m.
  1,2: ssprove_code_simpl.
  + eapply r_get_remember_lhs => mpk.
    eapply r_get_remember_rhs => stop.
    eapply (rpre_learn). {
      intros s0 s1 [[[_ I1] I2] I3].
      rewrite /quad I2 I3 /Rel0 in I1.
      move: I1 => /andP [I1 _].
      apply I1.
    }
    move=> /eqP ?.
    destruct mpk, stop => //=.
    1: apply r_fail.
    ssprove_swap_rhs 0%N.
    ssprove_sync => sk.
    eapply r_put_lhs, r_put_rhs, r_put_rhs.
    ssprove_restore_mem.
    2: by eapply r_ret.

    ssprove_invariant. {
      apply preserve_update_r_ignored_heap_ignore.
      1: fset_solve.
      apply preserve_update_r_ignored_heap_ignore.
      1: fset_solve.
      apply preserve_update_l_ignored_heap_ignore.
      1: fset_solve.
      intros h0 h1 H.
      apply H.
    }
    intros s0 s1 [[I1 I2] I3].
    rewrite /quad /Rel1 //= in I1 |- *.
    get_heap_simpl.
    simpl.
    move: I1.
    elim: (get_heap s0 flag_loc) => //= _ H.
    rewrite /quad I2 I3 in H.
    done.

  + eapply r_get_remember_lhs => mpk.
    eapply r_get_remember_rhs => stop.
    eapply (rpre_learn). {
      intros s0 s1 [[[_ I1] I2] I3].
      rewrite /quad I2 I3 /Rel1 in I1.
      move: I1 => /andP [I1 _].
      apply I1.
    }
    move=> /eqP ?.
    destruct mpk, stop => //=.
    2: apply r_fail.
    ssprove_code_simpl_more.
    eapply r_get_remember_lhs => flag.
    eapply r_get_remember_rhs => mga.
    eapply (rpre_learn). {
      intros h0 h1 [[[[[_ I1] I2] I3] I4] I5].
      rewrite /quad I2 I3 I4 I5 /Rel1 in I1.
      apply I1.
    }
    destruct flag, mga.
    1,4: done.
    1: intros _; apply r_fail.
    move=> //= /eqP E.
    eapply r_put_lhs, r_put_rhs.

    ssprove_restore_mem.

    2: {
      eapply rsymmetry.
      eapply (r_uniform_bij _ _ _ _ _ _ _ bij_op_exp) => c1.
      eapply (r_uniform_bij _ _ _ _ _ _ _ (bij_op_mult_op_exp m)) => c2.
      by eapply r_ret.
    }

    ssprove_invariant. {
      unfold PK_OTSR_loc, RED_loc, DDH0_loc.
      apply preserve_update_r_ignored_heap_ignore.
      1: fset_solve.
      apply preserve_update_l_ignored_heap_ignore.
      1: fset_solve.
      intros h0 h1 H.
      apply H.
    }
    intros h0 h1 [[[[I1 I2] I3] I4] I5].
    simpl.
    unfold quad, Rel1.
    get_heap_simpl.
    rewrite //= I2 I3 //.
Qed.

Theorem elgamal_sound {LA : {fset Location}}
  : ∀ (A : trimmed_package LA (I_PK_OTSR elgamal) A_export),
  AdvantageP (PK_OTSR elgamal) A = AdvantageP DDH (dlink A RED).
Proof.
  intros A.
  unfold AdvantageP.
  rewrite (AdvantageD_perf_l pk_ots0_perf).
  rewrite (AdvantageD_perf_r pk_ots1_perf).
  rewrite -AdvantageD_dlink.
  dprove_convert.
Qed.

End ElGamal.
