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

From NominalSSP Require Import AE HYBRID KEY NBSES NIKE SAE GAE GSAE.

Import AE HYBRID KEY NBSES NIKE_scheme SAE GAE GSAE.

Module GH.

Definition I_GH_OUT (E: NBSES_scheme) (N : NIKE_scheme) :=
  [interface
    #val #[ SET ]: (('pk N × 'pk N) × 'fin #|N.(NIKE_scheme.Shared_Key)|) → 'unit  ;
    #val #[ CSET ]: (('pk N × 'pk N) × 'fin #|N.(NIKE_scheme.Shared_Key)|) → 'unit ;
    #val #[ ENC ]: ((('pk N × 'pk N) × 'm E) × 'n E) → 'c E ;
    #val #[ DEC ]: ((('pk N × 'pk N) × 'c E) × 'n E) → 'm E 
].

Definition I_GH_ID_COMP (N : NIKE_scheme) :=
  [interface
    #val #[ SET ]: (('pk N × 'pk N) × 'fin #|N.(NIKE_scheme.Shared_Key)|) → 'unit  ;
    #val #[ CSET ]: (('pk N × 'pk N) × 'fin #|N.(NIKE_scheme.Shared_Key)|) → 'unit ;
    #val #[ GET ]: ('pk N × 'pk N) → 'fin #|N.(NIKE_scheme.Shared_Key)|
].

Definition I_GH_FST (E: NBSES_scheme) (N : NIKE_scheme) :=
  [interface
    #val #[ GEN ]: 'unit → 'unit ; 
    #val #[ SENC ]: ('m E × 'n E) → 'c E  ;
    #val #[ SDEC ]: ('c E × 'n E) → 'm E ;
    #val #[ ENC ]: ((('pk N × 'pk N) × 'm E) × 'n E) → 'c E ;
    #val #[ DEC ]: ((('pk N × 'pk N) × 'c E) × 'n E) → 'm E 
].

Definition I_GH_SND (E: NBSES_scheme) (N : NIKE_scheme) :=
  [interface
    #val #[ SET ]: (('pk N × 'pk N) × 'fin #|N.(NIKE_scheme.Shared_Key)|) → 'unit  ;
    #val #[ CSET ]: (('pk N × 'pk N) × 'fin #|N.(NIKE_scheme.Shared_Key)|) → 'unit ;
    #val #[ GET ]: ('pk N × 'pk N) → 'fin #|N.(NIKE_scheme.Shared_Key)| ;
    #val #[ GEN ]: 'unit → 'unit ; 
    #val #[ SENC ]: ('m E × 'n E) → 'c E  ;
    #val #[ SDEC ]: ('c E × 'n E) → 'm E 
].

Definition I_GH_TRD (E: NBSES_scheme) (N : NIKE_scheme) :=
  [interface
    #val #[ SET ]: (('pk N × 'pk N) × 'fin #|N.(NIKE_scheme.Shared_Key)|) → 'unit  ;
    #val #[ CSET ]: (('pk N × 'pk N) × 'fin #|N.(NIKE_scheme.Shared_Key)|) → 'unit ;
    #val #[ GET ]: ('pk N × 'pk N) → 'fin #|N.(NIKE_scheme.Shared_Key)| ;
    #val #[ HON ]: ('pk N × 'pk N)  → 'option 'bool
].

#[export] Hint Unfold I_GH_OUT I_GH_ID_COMP I_HYBRID_IN I_HYBRID_OUT I_GH_FST I_GH_SND I_GH_TRD I_AE_IN I_AE_OUT I_KEY_OUT I_SAE_OUT : in_fset_eq.

Definition GH (E : NBSES_scheme) (N : NIKE_scheme) (I : NIKE_scheme.inj ('fin #|N.(NIKE_scheme.Shared_Key)|) ('fin #|E.(NBSES.Shared_Key)|)) i qset (b : 'bool):
  raw_module := (HYBRID E N I i qset) ∘ (((ID (I_GH_ID_COMP N) || ID (I_GH_FST E N)) ∘ (AE E N I b || ID (I_GH_SND E N)) ∘ (SAE E b || ID (I_GH_TRD E N))) ∘ (KEY N true)).

Lemma GH_valid (E : NBSES_scheme) (N: NIKE_scheme) (I : NIKE_scheme.inj ('fin #|N.(NIKE_scheme.Shared_Key)|) ('fin #|E.(NBSES.Shared_Key)|)) i qset (b : 'bool) :
  ValidPackage (GH E N I i qset b).(loc) [interface] (I_GH_OUT E N) (GH E N I i qset b).
Proof.
unfold GH. nssprove_valid. Qed.

(* Attempt at Lemma 3*)
Theorem Lemma3_Adv_GAE {E} {N} {qset} (A : adversary (I_GAE_OUT E N)) (I : NIKE_scheme.inj ('fin #|N.(NIKE_scheme.Shared_Key)|) ('fin #|E.(NBSES.Shared_Key)|)) :
  AdvFor (GAE E N I) A <= \sum_(1 <= i < qset)
    ( AdvFor (GSAE E) (A ∘ (HYBRID E N I i qset) ∘ (AE E N I true || ID (I_GH_ID_COMP N)) ∘ (KEY N true)) + 
      AdvFor (GSAE E) (A ∘ (HYBRID E N I i qset) ∘ (AE E N I false|| ID (I_GH_ID_COMP N)) ∘ (KEY N true))).
Proof.
unfold GAE.
Admitted.

End GH.