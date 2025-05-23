(*This is a part of the implementation of the state-separated game-based proof of security for the NaCl crypto_box authenticated encryption scheme.
This file contains the specification for the GNIKE and GuNIKE games and following lemmas*)

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

From NominalSSP Require Import Prelude Group.

From NominalSSP Require Import NIKE KEY PKEY PKAE.
Import NIKE_scheme NBPES_scheme KEY PKEY.

Import PackageNotation.

#[local] Open Scope package_scope.
#[local] Open Scope ring_scope.

Module GNIKE.

Definition GEN := 2%N.
Definition HON := 30%N.
Definition CSETPK := 3%N.
Definition GET := 29%N. (*tal skal være forskellige across filer*)

Notation " 'T c " := (c) (in custom pack_type at level 2, c constr at level 20).
Notation " 'T c " := (c) (at level 2): package_scope.



Definition I_GNIKE_OUT (N: NIKE_scheme) :=
  [interface
    #val #[ SHAREDKEY ]: (('fin #|N.(NIKE_scheme.PK)|) × ('fin #|N.(NIKE_scheme.PK)|)) → 'option 'unit ;
    #val #[ GEN ]: 'unit → 'T 'fin #|N.(NIKE_scheme.PK)| ;
    #val #[ CSETPK ]: 'T 'fin #|N.(NIKE_scheme.PK)| → 'unit ;
    #val #[ GET ]:  (('fin #|N.(NIKE_scheme.PK)|) × ('fin #|N.(NIKE_scheme.PK)|)) → 'fin #|N.(NIKE_scheme.Shared_Key)| ;
    #val #[ HON ]:  (('fin #|N.(NIKE_scheme.PK)|) × ('fin #|N.(NIKE_scheme.PK)|)) → 'option 'bool
].

Definition I_GNIKE_ID_COMP (N: NIKE_scheme) :=
  [interface
    #val #[ GEN ]: 'unit → 'T 'fin #|N.(NIKE_scheme.PK)| ;
    #val #[ CSETPK ]: 'T 'fin #|N.(NIKE_scheme.PK)| → 'unit ;
    #val #[ GET ]:  (('fin #|N.(NIKE_scheme.PK)|) × ('fin #|N.(NIKE_scheme.PK)|)) → 'fin #|N.(NIKE_scheme.Shared_Key)| ;
    #val #[ HON ]:  (('fin #|N.(NIKE_scheme.PK)|) × ('fin #|N.(NIKE_scheme.PK)|)) → 'option 'bool
].

Definition I_R_PKEY_OUT (N: NIKE_scheme) := I_NIKE_OUT N :|: I_KEY_OUT N .

#[export] Hint Unfold I_GNIKE_OUT I_GNIKE_ID_COMP I_NIKE_OUT I_NIKE_IN I_PKEY_OUT I_KEY_OUT I_R_PKEY_OUT : in_fset_eq.

Definition GNIKE (N: NIKE_scheme) (b : 'bool) :
  raw_module := (NIKE N || ID (I_GNIKE_ID_COMP N)) ∘ (KEY N b || PKEY (NIKE_to_GEN N) false).

Definition GuNIKE (N: NIKE_scheme) (b : 'bool) :
  raw_module := (NIKE N || ID (I_GNIKE_ID_COMP N)) ∘ (KEY N b || PKEY (NIKE_to_GEN N) true).

Lemma GuNIKE_valid (N: NIKE_scheme) (b : 'bool) : ValidPackage (GuNIKE N b).(loc) [interface] (I_GNIKE_OUT N) (GuNIKE N b).
Proof.
unfold GuNIKE. nssprove_valid. Qed.


Lemma GNIKE_valid (N: NIKE_scheme) (b : 'bool) : ValidPackage (GNIKE N b).(loc) [interface] (I_GNIKE_OUT N) (GNIKE N b).
Proof.
unfold GNIKE. nssprove_valid. Qed.


(*Theorem Corollary3_Adv_GNIKE_GuNIKE {N} (A : adversary (I_GNIKE_OUT N)) :
let A' := (A ∘ (NIKE N || ID (I_GNIKE_ID_COMP N)))%sep in
  AdvFor (GNIKE N) A
  <= AdvFor (PKEY (NIKE_to_GEN N)) (A' ∘ (KEY N (NIKE_to_SGEN N) false || ID (I_PKEY_OUT (NIKE_to_GEN N)))) +
     AdvFor (GuNIKE N) A +
     AdvFor (PKEY (NIKE_to_GEN N)) (A' ∘ (KEY N (NIKE_to_SGEN N) true || ID (I_PKEY_OUT (NIKE_to_GEN N)))).
Proof.
unfold AdvFor, GNIKE, GuNIKE.
repeat rewrite Adv_sep_link.
erewrite Adv_sym.
nssprove_adv_trans (KEY N (NIKE_to_SGEN N) false || PKEY (NIKE_to_GEN N) true).
erewrite -> Adv_par_r by nssprove_valid.
erewrite Adv_sym.
rewrite -GRing.addrA. (*puts in paranthesis, so lerD parts correctly*)
apply lerD.
- apply lexx.
- nssprove_adv_trans (KEY N (NIKE_to_SGEN N) true || PKEY (NIKE_to_GEN N) true).
apply lerD.
-- erewrite Adv_sym. apply lexx.
-- erewrite -> Adv_par_r by nssprove_valid. apply lexx. Qed.*)


Theorem Corollary3_Adv_GNIKE_GuNIKE {N} (A : adversary (I_GNIKE_OUT N)) :
let A' := (A ∘ (NIKE N || ID (I_GNIKE_ID_COMP N)))%sep in
  AdvFor (GuNIKE N) A
  <= AdvFor (PKEY (NIKE_to_GEN N)) (A' ∘ (KEY N false || ID (I_PKEY_OUT (NIKE_to_GEN N)))) +
     AdvFor (GNIKE N) A +
     AdvFor (PKEY (NIKE_to_GEN N)) (A' ∘ (KEY N true || ID (I_PKEY_OUT (NIKE_to_GEN N)))).
Proof.
unfold AdvFor, GNIKE, GuNIKE.
repeat rewrite Adv_sep_link.
erewrite Adv_sym.
nssprove_adv_trans (KEY N false || PKEY (NIKE_to_GEN N) false).
erewrite -> Adv_par_r by nssprove_valid.
rewrite Adv_sym.
rewrite -GRing.addrA. (*puts in paranthesis, so lerD parts correctly*)
apply lerD.
- apply lexx.
- nssprove_adv_trans (KEY N true || PKEY (NIKE_to_GEN N) false).
apply lerD.
-- erewrite Adv_sym. apply lexx.
-- erewrite -> Adv_par_r by nssprove_valid. rewrite Adv_sym. apply lexx. Qed.


End GNIKE.