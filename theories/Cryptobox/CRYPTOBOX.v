(*This is an implementation of the state-separated game-based proof of security for the NaCl crypto_box authenticated encryption scheme.*)

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

From NominalSSP Require Import PK.DDH PK.Scheme.

From NominalSSP Require Import Prelude Group Misc.
Import PackageNotation.

From NominalSSP Require Import NIKE NBSES GPKAE GMODPKAE GAE MODPKAE AE GNIKE NIKE PKEY KEY PKAE Scheme.

#[local] Open Scope package_scope.
#[local] Open Scope ring_scope.

Module crypto_box.

(*Record SE_scheme :=
  { Shared_Key     : finType ;
    Shared_Key_pos : Positive #|Shared_Key|;
    M        : choice_type ;
    C        : choice_type ;
    sample_C : code fset0 [interface] C ;

   pkgen : 
      code fset0 [interface] ('fin #|PK| × 'fin #|SK|) ;

   enc : forall (sk : 'fin #|SK|) (pk : 'fin #|PK|) (m : M) (n : 'fin #|Nonce|),
      code fset0 [interface] C ;

   dec : forall (sk : 'fin #|SK|) (pk : 'fin #|PK|) (c : C) (n : 'fin #|Nonce|),
      code fset0 [interface] M 
  }.*)


Record inj A B :=
  { encode  : A → B
  ; decode  : B → A
  ; cancels : cancel encode decode
  }.

Arguments encode {A} {B} _.
Arguments decode {A} {B} _.


Notation " 'T c " := (c) (in custom pack_type at level 2, c constr at level 20).
Notation " 'T c " := (c) (at level 2): package_scope.

Instance shared_pos (N: NIKE_scheme.NIKE_scheme) : Positive #|(prod N.(NIKE_scheme.PK) N.(NIKE_scheme.SK) : finType)|.
Proof. Admitted.

Definition CRYPTOBOX_scheme (N: NIKE_scheme.NIKE_scheme) (E : NBSES.NBSES_scheme) (P : NBPES_scheme.NBPES_scheme) (I : inj ('fin #|N.(NIKE_scheme.Shared_Key)|) E.(NBSES.Shared_Key)): NBPES_scheme.NBPES_scheme := {|
    NBPES_scheme.PK       := N.(NIKE_scheme.PK) ;
    NBPES_scheme.SK       := N.(NIKE_scheme.SK) ;
    NBPES_scheme.Nonce    := E.(NBSES.Nonce) ;
    NBPES_scheme.M        := E.(NBSES.M) ;
    NBPES_scheme.C        := E.(NBSES.C) ;
    NBPES_scheme.sample_C := E.(NBSES.sample_C) ;

    NBPES_scheme.pkgen :=  
      {code
        '(pk, sk) ← N.(NIKE_scheme.pkgen) ;;
        ret (pk, sk)
      } ;

    NBPES_scheme.enc := λ sk pk m n,
      {code
        K ← N.(NIKE_scheme.sharedkey) pk sk ;;
        let k := I.(encode) K in
        C ← E.(NBSES.enc) m (fto k) n ;;
        ret C} ;


    NBPES_scheme.dec := λ sk pk c n,
      {code
        K ← N.(NIKE_scheme.sharedkey) pk sk ;;
        let k := I.(encode) K in
        M ← E.(NBSES.dec) c (fto k) n ;;
        ret M
      }
|}.


Theorem Lemma4_Adv_GuPKAE_CB {P} {N} {E} (A : adversary (GPKAE.I_GPKAE_OUT P)) (I : inj ('fin #|N.(NIKE_scheme.Shared_Key)|) E.(NBSES.Shared_Key)):
  AdvFor (GPKAE.GuPKAE (CRYPTOBOX_scheme N E P I)) A
  <= AdvFor (GNIKE.GuNIKE N) (A ∘ (ID (GMODPKAE.I_GMODPKAE_ID_COMP N) || ((MODPKAE.MODPKAE N E) ∘ ((ID (NIKE_scheme.I_NIKE_OUT N) || AE.AE E N false)))) ∘ ((ID (PKEY.I_PKEY_OUT (PKEY.NIKE_to_GEN N)) || ID (KEY.I_KEY_OUT N (KEY.NBSES_to_SGEN E))))).
Proof.
unfold GPKAE.GuPKAE, GNIKE.GuNIKE, AdvFor.

Lemma perfectcb b (N: NIKE_scheme.NIKE_scheme) (E : NBSES.NBSES_scheme) (P : NBPES_scheme.NBPES_scheme) (I : inj ('fin #|N.(NIKE_scheme.Shared_Key)|) E.(NBSES.Shared_Key)) (A : adversary (GPKAE.I_GPKAE_OUT P)):
  ∀ b, (GPKAE.GPKAE (CRYPTOBOX_scheme N E P I) b) ≈₀ (GPKAE.GPKAE (CRYPTOBOX_scheme N E P I) b).

Lemma Equiv_GuPKAE_GMODPKAE (P : NBPES_scheme.NBPES_scheme) (N : NIKE_scheme.NIKE_scheme) (E : NBSES.NBSES_scheme) (I : inj (N.(NIKE_scheme.Shared_Key)) (E.(NBSES.Shared_Key))) (A : inj ('fin #|P.(NBPES_scheme.PK)|) ('fin #|N.(NIKE_scheme.PK)|)) (B : inj (P.(NBPES_scheme.M)) (E.(NBSES.M))) (C : inj (P.(NBPES_scheme.N)) ('T 'fin #|E.(NBSES.Nonce)|)):
 ∀ b, (GPKAE.GuPKAE P) ≈₀ (GMODPKAE.GMODPKAE E N P I A B C D b).


(I : inj 'shared_key N 'k E) (A : inji ('fin #|F.(NBPES_scheme.PK)|) ('fin #|N.(NIKE_scheme.PK)|)) (B : inji ('m F) ('T E.(NBSES.M))) (C : inji ('n F) ('T 'fin #|E.(NBSES.Nonce)|)) (D : inji ('c F) ('T E.(NBSES.C)))


Theorem Lemma4_Adv_GuPKAE_CB {P} {N} {E} (A : adversary (I_GPKAE_OUT P)) :
  AdvFor (GuPKAE P) A
  <= AdvFor (GuNIKE N) (A ∘ (ID (I_GMODPKAE_ID_COMP N) || ((MODPKAE N E) ∘ ((ID (I_NIKE_OUT N) || AE E N false)))) ∘ ((ID (I_PKEY_OUT (NIKE_to_GEN N)) || ID (I_KEY_OUT N (NBSES_to_SGEN E))))).
Proof.
unfold AdvFor, GuPKAE, GuNIKE.



GMODPKAE:

(ID (I_GMODPKAE_ID_COMP N) || ((MODPKAE_F N E F A B C D) ∘ ((NIKE_E N E I || AE E N false)))) ∘ ((PKEY (NIKE_to_GEN N) true || KEY N (NBSES_to_SGEN E) false))

Theorem Corollary1_Adv_GPKAE {E} (A : adversary (I_GPKAE_OUT E)) :
  AdvFor (GPKAE E) A
  <=  AdvFor (PKEY (NBPES_to_GEN E)) (A ∘ (PKAE E false || ID (I_GPKAE_ID_COMP E))) +
      AdvFor (GuPKAE E) A +
      AdvFor (PKEY (NBPES_to_GEN E)) (A ∘ (PKAE E true || ID (I_GPKAE_ID_COMP E))).
Proof.

(*

Definition CRYPTOBOX (N: NIKE_scheme.NIKE_scheme) (E : NBSES.NBSES_scheme) (P : NBPES_scheme.NBPES_scheme) (P_N_pk : inj ('fin #|NBPES_scheme.PK P|) ('fin #|N.(NIKE_scheme.PK)|)) (P_N_sk : inj ('fin #|NBPES_scheme.SK P|) ('fin #|N.(NIKE_scheme.SK)|)) (N_P_pk : inj ('fin #|N.(NIKE_scheme.PK)|) P.(NBPES_scheme.PK)) (N_P_sk : inj ('fin #|N.(NIKE_scheme.SK)|) P.(NBPES_scheme.SK)) (N_P_k : inj ('fin #|N.(NIKE_scheme.Shared_Key)|) E.(NBSES.Shared_Key)) (P_E_m : inj P.(NBPES_scheme.M) E.(NBSES.M)) (P_E_n : inj ('fin #|P.(NBPES_scheme.Nonce)|) ('fin #|E.(NBSES.Nonce)|)): NBPES_scheme.NBPES_scheme := {|
    NBPES_scheme.PK       := P.(NBPES_scheme.PK) ;
    NBPES_scheme.SK       := P.(NBPES_scheme.SK) ;
    NBPES_scheme.Nonce    := P.(NBPES_scheme.Nonce) ;
    NBPES_scheme.M        := P.(NBPES_scheme.M) ;
    NBPES_scheme.C        := P.(NBPES_scheme.C) ;
    NBPES_scheme.sample_C := P.(NBPES_scheme.sample_C) ;

    NBPES_scheme.pkgen :=  
      {code
        '(pk, sk) ← N.(NIKE_scheme.pkgen) ;;
        let pk' := N_P_pk.(encode) pk in
        let sk' := N_P_sk.(encode) sk in
        ret ((fto pk'), (fto sk'))
      } ;

    NBPES_scheme.enc := λ sk pk m n,
      {code
        let pk' := P_N_pk.(encode) pk in
        let sk' := P_N_sk.(encode) sk in       
        K ← N.(NIKE_scheme.sharedkey) pk' sk' ;;
        let k := N_P_k.(encode) K in
        let m' := P_E_m.(encode) m in
        let n' := P_E_n.(encode) n in
        C ← E.(NBSES.enc) m' (fto k) n' ;;
        ret C} ;


    NBPES_scheme.dec := λ sk pk c n,
      {code
        K ← N.(NIKE_scheme.sharedkey) pk (fto sk) ;;
        let k := I.(encode) K in
        M ← E.(NBSES.dec) c (fto k) n ;;
        ret M
      }
|}.
*)

(*
Definition CRYPTOBOX (N: NIKE_scheme.NIKE_scheme) (E : NBSES.NBSES_scheme) (I : inj ('fin #|N.(NIKE_scheme.Shared_Key)|) E.(NBSES.Shared_Key)) : NBSES.NBSES_scheme := {|
    NBSES.Shared_Key := prod N.(NIKE_scheme.PK) N.(NIKE_scheme.SK) ;
    NBSES.Shared_Key_pos := _ ;
    NBSES.Nonce := E.(NBSES.Nonce) ;
    NBSES.M        := E.(NBSES.M) ;
    NBSES.C        := E.(NBSES.C) ;
  
    NBSES.sample_K :=
      {code
        k ← sample uniform #|(prod N.(NIKE_scheme.PK) N.(NIKE_scheme.SK) : finType)| ;;
        ret k
      } ;

    NBSES.sample_C := E.(NBSES.sample_C) ;


    NBSES.enc := λ m shared n,
      {code
        let '(pk, sk) := otf shared in        
        K ← N.(NIKE_scheme.sharedkey) (fto pk) (fto sk) ;;
        let k := I.(encode) K in
        C ← E.(NBSES.enc) m (fto k) n ;;
        ret C} ;


    NBSES.dec := λ c shared n,
      {code
        let '(pk, sk) := otf shared in
        K ← N.(NIKE_scheme.sharedkey) (fto pk) (fto sk) ;;
        let k := I.(encode) K in
        M ← E.(NBSES.dec) c (fto k) n ;;
        ret M
      }
|}.*)



(*
Definition PKGEN := 31%N.
Definition PKENC := 32%N.
Definition PKDEC := 33%N.

Definition I_CRYPTOBOX_OUT (N : NIKE_scheme) (E : NBSES_scheme) :=
  [interface
    #val #[ PKGEN ]: 'unit → ('T 'fin #|N.(NIKE_scheme.PK)| × 'T 'fin #|N.(NIKE_scheme.SK)|) ;
    #val #[ PKENC ]: (((('T 'fin #|N.(NIKE_scheme.SK)|) × 'T 'fin #|N.(NIKE_scheme.PK)|) × 'T 'fin #|E.(NBSES.M)|) × 'n E) → 'c E ;
    #val #[ PKDEC ]: (((('T 'fin #|N.(NIKE_scheme.SK)|) × 'T 'fin #|N.(NIKE_scheme.PK)|) × 'c E) × 'n E) → 'm E 
].

Definition CRYPTOBOX (N : NIKE_scheme) (E : NBSES_scheme) (I : inj 'fin #|N.(NIKE_scheme.Shared_Key)| 'k E):
  game (I_CRYPTOBOX_OUT N E) :=
  [module no_locs ;
    #def #[ PKGEN ] (_ : 'unit) : ('T 'fin #|N.(NIKE_scheme.PK)| × 'T 'fin #|N.(NIKE_scheme.SK)|) {
      '(PK, SK) ← N.(NIKE_scheme.pkgen) ;;
      ret (PK, SK)
    } ;
    #def #[ PKENC ] ('(((SK, PK), m), n) : (('T 'fin #|N.(NIKE_scheme.SK)| × 'T 'fin #|N.(NIKE_scheme.PK)|) × 'm E) × 'n E) : ('c E) {
      K ← N.(sharedkey) PK SK ;;
      let k := I.(encode) K in
      C ← E.(enc) m k n ;;
      ret C
    } ;
    #def #[ PKDEC ] ('(((SK, PK), c), n) : (('T 'fin #|N.(NIKE_scheme.SK)| × 'T 'fin #|N.(NIKE_scheme.PK)|) × 'c E) × 'n E) : ('m E) {
      K ← N.(sharedkey) PK SK ;;
      let k := I.(encode) K in
      M ← E.(dec) c k n ;;
      ret M
    }
  ].
*)



End crypto_box.
