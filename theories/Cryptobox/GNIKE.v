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

From NominalSSP Require Import Prelude Group Misc.

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


(*
Definition I_GNIKE_OUT (N: NIKE_scheme) :=
  [interface
    #val #[ SHAREDKEY ]: (('fin #|N.(NIKE_scheme.PK)|) × ('fin #|N.(NIKE_scheme.PK)|)) → 'unit ;
    #val #[ GEN ]: 'unit → 'T 'fin #|N.(NIKE_scheme.PK)| ;
    #val #[ CSETPK ]: 'T 'fin #|N.(NIKE_scheme.PK)| → 'unit ;
    #val #[ GET ]:  ('SID N) → 'shared_key N ;
    #val #[ HON ]:  ('SID N) → 'bool
].

Definition I_GNIKE_ID_COMP (N: NIKE_scheme) :=
  [interface
    #val #[ GEN ]: 'unit → 'T 'fin #|N.(NIKE_scheme.PK)| ;
    #val #[ CSETPK ]: 'T 'fin #|N.(NIKE_scheme.PK)| → 'unit ;
    #val #[ GET ]:  ('SID N) → 'shared_key N ;
    #val #[ HON ]:  ('SID N) → 'bool
].*)

Definition I_GNIKE_OUT (N: NIKE_scheme) :=
  [interface
    #val #[ SHAREDKEY ]: (('fin #|N.(NIKE_scheme.PK)|) × ('fin #|N.(NIKE_scheme.PK)|)) → 'unit ;
    #val #[ GEN ]: 'unit → 'T 'fin #|N.(NIKE_scheme.PK)| ;
    #val #[ CSETPK ]: 'T 'fin #|N.(NIKE_scheme.PK)| → 'unit ;
    #val #[ GET ]:  (('fin #|N.(NIKE_scheme.PK)|) × ('fin #|N.(NIKE_scheme.PK)|)) → 'fin #|N.(NIKE_scheme.Shared_Key)| ;
    #val #[ HON ]:  (('fin #|N.(NIKE_scheme.PK)|) × ('fin #|N.(NIKE_scheme.PK)|)) → 'bool
].

Definition I_GNIKE_ID_COMP (N: NIKE_scheme) :=
  [interface
    #val #[ GEN ]: 'unit → 'T 'fin #|N.(NIKE_scheme.PK)| ;
    #val #[ CSETPK ]: 'T 'fin #|N.(NIKE_scheme.PK)| → 'unit ;
    #val #[ GET ]:  (('fin #|N.(NIKE_scheme.PK)|) × ('fin #|N.(NIKE_scheme.PK)|)) → 'fin #|N.(NIKE_scheme.Shared_Key)| ;
    #val #[ HON ]:  (('fin #|N.(NIKE_scheme.PK)|) × ('fin #|N.(NIKE_scheme.PK)|)) → 'bool
].

Definition I_R_PKEY_OUT (N: NIKE_scheme) := I_NIKE_OUT N :|: I_KEY_OUT N (NIKE_to_SGEN N).

#[export] Hint Unfold I_GNIKE_OUT I_GNIKE_ID_COMP I_NIKE_OUT I_NIKE_IN I_PKEY_OUT I_KEY_OUT I_R_PKEY_OUT : in_fset_eq.

Definition GNIKE (N: NIKE_scheme) (b : 'bool) :
  raw_module := (NIKE N || ID (I_GNIKE_ID_COMP N)) ∘ (KEY N (NIKE_to_SGEN N) b || PKEY (NIKE_to_GEN N) false).

Definition GuNIKE (N: NIKE_scheme) (b : 'bool) :
  raw_module := (NIKE N || ID (I_GNIKE_ID_COMP N)) ∘ (KEY N (NIKE_to_SGEN N) b || PKEY (NIKE_to_GEN N) true).

Lemma GuNIKE_valid (N: NIKE_scheme) (b : 'bool) : ValidPackage (GuNIKE N b).(loc) [interface] (I_GNIKE_OUT N) (GuNIKE N b).
Proof.
unfold GuNIKE. nssprove_valid. Qed.


Definition R_PKEY (N: NIKE_scheme) (b : 'bool) :
  raw_module := (NIKE N || KEY N (NIKE_to_SGEN N) b).

Lemma R_PKEY_valid (N: NIKE_scheme) (b : bool) : ValidPackage (R_PKEY N b).(loc) (I_NIKE_IN N) (I_R_PKEY_OUT N) (R_PKEY N b).
Proof.
unfold R_PKEY. nssprove_valid. Qed.

Lemma GNIKE_valid (N: NIKE_scheme) (b : 'bool) : ValidPackage (GNIKE N b).(loc) [interface] (I_GNIKE_OUT N) (GNIKE N b).
Proof.
unfold GNIKE. nssprove_valid. Qed.

Check Adv.

Check AdvFor.

Check swish.

Check swash.

Check Adv_sep_link.

Search Adv.

Search sep_link.

Search sep_par.


(*

(NIKE N || ID (I_GNIKE_ID_COMP N)) ∘ (KEY N (NIKE_to_SGEN N) b || PKEY (NIKE_to_GEN N) b)

*)

(*Theorem Corollary_Adv_GNIKE_GuNIKE {N} (A : adversary (I_GNIKE_OUT N)) :
  let GNike := GNIKE N in
  let PKey := PKEY (NIKE_to_GEN N) in
  let Key := KEY N (NIKE_to_SGEN N) in
  let GuNike := GuNIKE N in
  AdvFor GNike A <= AdvFor PKey A.
Proof.
unfold GNIKE.*)

Theorem Corollary3_Adv_GNIKE_GuNIKE {N} (A : adversary (I_GNIKE_OUT N)) :
  AdvFor (GNIKE N) A
  <= AdvFor (PKEY (NIKE_to_GEN N)) (A ∘ ((NIKE N || ID (I_GNIKE_ID_COMP N)) ∘ (KEY N (NIKE_to_SGEN N) false || ID (I_PKEY_OUT (NIKE_to_GEN N))))) +
     AdvFor (PKEY (NIKE_to_GEN N)) (A ∘ ((NIKE N || ID (I_GNIKE_ID_COMP N)) ∘ (KEY N (NIKE_to_SGEN N) true || ID (I_PKEY_OUT (NIKE_to_GEN N))))) +
     AdvFor (GuNIKE N) A.
Proof.
unfold AdvFor, GNIKE, GuNIKE.
repeat rewrite Adv_sep_link.
rewrite swish.
  - rewrite swish.
  -- rewrite swash.
  --- rewrite swash.
  ---- repeat rewrite sep_par_empty_l.
       repeat rewrite sep_par_empty_r.




unfold AdvFor. unfold GNIKE. unfold GuNIKE. rewrite Adv_sep_link. rewrite Adv_sep_link. rewrite swish. - rewrite swish. -- rewrite sep_par_empty_l. rewrite sep_par_empty_l. rewrite swash. --- rewrite swash.  rewrite swish. - nssprove_adv_trans .



(**Theorem Corollary3_Adv_GNIKE_GuNIKE {N} (A : adversary (I_GNIKE_OUT N)) :
  AdvFor (GNIKE N) A
  <= AdvFor (PKEY (NIKE_to_GEN N)) (A ∘ ((NIKE N || ID (I_GNIKE_ID_COMP N)) ∘ (KEY N (NIKE_to_SGEN N) true || ID (I_PKEY_OUT (NIKE_to_GEN N))))) +
     AdvFor (KEY N (NIKE_to_SGEN N)) (A ∘ ((NIKE N || ID (I_GNIKE_ID_COMP N)) ∘ ((ID (I_KEY_OUT N (NIKE_to_SGEN N))) || PKEY (NIKE_to_GEN N) false))) +
     AdvFor (GuNIKE N) A.
Proof.
unfold AdvFor. unfold GNIKE. unfold GuNIKE. rewrite Adv_sep_link. rewrite swish. - nssprove_adv_trans .*))



(*Theorem Corollary3_Adv_GNIKE_GuNIKE {N} (A : adversary (I_GNIKE_OUT N)) :
  AdvFor (GNIKE N) A
  <= AdvFor (fun b => PKEY b (NIKE_to_GEN N)) (A ∘ ) + AdvFor (fun b => KEY b N (NIKE_to_SGEN N)) A + AdvFor (GuNIKE N) A.
Proof.
unfold AdvFor. unfold GNIKE. rewrite Adv_sep_link. rewrite swish. - nssprove_adv_trans .*)


(*change bool to second argument in PKEY*) (*swash*)


End GNIKE.