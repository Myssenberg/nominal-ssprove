From Coq Require Import Utf8.

From mathcomp Require Import all_ssreflect all_algebra 
  fingroup.fingroup solvable.cyclic prime.

Local Open Scope ring_scope.
Import GroupScope GRing.Theory.


Module Type GroupParam.
  Parameter gT : finGroupType.
  (* Definition ζ : {set gT} := [set : gT]. *)
  Parameter g :  gT.
  Parameter g_gen : <[g]> = [set : gT].
  Parameter prime_order : prime #[g].
End GroupParam.


Module GroupTheorems (GP : GroupParam).
  Import GP.

  Definition q : nat := #[g].

  Definition el : finType := gT.
  Definition exp : finType := Finite.clone _ 'Z_q.

  Lemma el_in_g {x : el} : x \in <[g]>.
  Proof. rewrite g_gen. apply in_setT. Qed.

  Lemma expgE (x : el) : ∃ a, x = g ^+ a.
  Proof.
    apply /cycleP. apply el_in_g.
  Qed.

  Lemma expgq (x : el) : x ^+ q = 1.
  Proof.
    destruct (expgE x).
    rewrite H.
    rewrite expgAC.
    rewrite expg_order.
    by rewrite expg1n.
  Qed.

  Lemma trunc_q : (Zp_trunc q).+2 = q.
  Proof.
    apply Zp_cast, prime_gt1, prime_order.
  Qed.

  Lemma expg_modq (x : el) (k : nat) : x ^+ (k %% ((Zp_trunc q).+2)) = x ^+ k.
  Proof.
    rewrite expg_mod //.
    rewrite trunc_q.
    apply expgq.
  Qed.

  Lemma expg_frac (x : el) (a b : exp) : x ^+ (a / b) = x ^+ a ^+ (b^-1)%R.
  Proof.
    rewrite expg_modq expgM //.
  Qed.

  Lemma expg_fracgg (x : el) (a : exp) : (a != 0) → x ^+ (a / a) = x.
  Proof.
    intros H.
    replace (nat_of_ord (a / a))
      with (nat_of_ord (Zp_mul a (Zp_inv a)))
      by easy.
    rewrite Zp_mulzV.
    2: {
      rewrite prime_coprime.
      2: rewrite trunc_q; apply prime_order.
      rewrite gtnNdvd.
      - done.
      - by rewrite lt0n.
      - simpl.
        rewrite -modZp.
        apply ltn_mod.
    }
    rewrite expg_modq expg1 //.
  Qed.

  Lemma expg_sub (x : el) (a b : exp) : x ^+ (a - b)%R = x ^+ a * x ^- b.
  Proof.
    rewrite expg_modq expgD expg_zneg //=.
    destruct (expgE x); subst.
    apply mem_cycle.
  Qed.

  Lemma mulgC (x y : el) : x * y = y * x.
  Proof.
    destruct (expgE x), (expgE y).
    subst.
    by rewrite -expgD -expgD addnC.
  Qed.

  Lemma mulgA (x y z : el) : x * (y * z) = (x * y) * z.
  Proof.
    destruct (expgE x), (expgE y), (expgE z).
    subst.
    by rewrite -!expgD addnA.
  Qed.

  Definition log (x : el) : exp :=
    inord (sval (@cyclePmin el g x el_in_g)).

  Lemma log_expg (x : el) (a : exp) : log x = a → g ^+ a = x.
  Proof.
    unfold log.
    destruct cyclePmin => H.
    subst; simpl.
    f_equal.
    apply inordK.
    rewrite trunc_q //.
  Qed.

  Lemma expg_log (x : el) (a : exp) : g ^+ a = x → log x = a.
  Proof.
    intros H.
    unfold log.
    destruct cyclePmin.
    subst; simpl.
    move: e => /eqP.
    rewrite eq_expg_mod_order => /eqP.
    rewrite (modn_small i) => e.
    rewrite -e.
    rewrite modn_small.
    1: apply inord_val.
    rewrite -modZp.
    rewrite {2}trunc_q.
    rewrite ltn_mod.
    apply order_gt0.
  Qed.

  Lemma expgn_bij : bijective (λ n : exp, g ^+ n : el).
  Proof.
    eexists log => [a|x].
    - by apply expg_log.
    - by apply log_expg.
  Qed.
End GroupTheorems.


Module GP_Z3 <: GroupParam.
  Definition gT : finGroupType := 'Z_3.
  Definition g :  gT := Zp1.

  Lemma g_gen : <[g]> = [set : gT].
  Proof.
    unfold g. symmetry. apply Zp_cycle.
  Qed.

  Lemma prime_order : prime #[g].
  Proof.
    unfold g.
    rewrite order_Zp1.
    reflexivity.
  Qed.
End GP_Z3.
