import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointUnion
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRenaming
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureRetraction

/-! # Descent retaining computation certificates

Ordinary descent returns a lower typed equality but discards its checking
certificate. This stronger interface retains an actual lower computation.
The compatible closure constructs that certificate through changing binders.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
open private erase_app_inv erase_proj_inv erase_lam_inv erase_forallE_inv
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
open private ProofShape.liftN_app_inv ProofShape.liftN_proj_inv ProofShape.liftN_lam_inv
  ProofShape.liftN_forallE_inv equality_simAt
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypedReplay
open private erase_const_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
open private erase_sort_inv ProofShape.liftN_sort_inv ProofShape.liftN_const_inv
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureComparison
open private erased_lift_bvar_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureRecoveryDescent
open private subst_bvar_liftN from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRenaming
variable [Params]

/-- Certificate-preserving primitive descent. In addition to the lower typed
representative and exact lifted output, it requires a computation in Target
at the lower context. Ordinary semantic descent alone does not assert this
extra certificate; general joint-stage instances must be constructed. -/
def ErasedScopedPrimitiveCertificateDescent
    (Step Target : List ProofShape → ProofShape → ProofShape → Prop) : Prop :=
  ∀ {Γ Γ' n k e T out}, OnCtx Γ (env.IsType univs) → OnCtx Γ' (env.IsType univs) →
    Ctx.LiftN n k Γ Γ' → env.HasType univs Γ e T →
    Step (proofEraseCtx Γ') ((proofErase Γ e).liftN n k) out →
    ∃ e', env.IsDefEq univs Γ e e' T ∧
      ProofShape.ScopedCompute Target (proofEraseCtx Γ) (proofErase Γ e) (proofErase Γ e') ∧
      (proofErase Γ e').liftN n k = out

/-- Forgetting the lower certificate recovers the existing semantic interface. -/
theorem ErasedScopedPrimitiveCertificateDescent.descent
    (H : ErasedScopedPrimitiveCertificateDescent Step Target) : ErasedScopedPrimitiveDescent Step := by
  intro Γ Γ' n k e T out hΓ hΓ' W ht R
  obtain ⟨e', HE, _, Ee⟩ := H hΓ hΓ' W ht R
  exact ⟨e', HE, Ee⟩

/-- Compatible computation preserves the stronger primitive descent interface.
The output includes a reusable Target path at the lower context, even under
binders whose annotations change during computation. -/
theorem proofErase_scoped_compute_certificate_descend
    (hstep : ErasedScopedPrimitiveCertificateDescent Step Target)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.LiftN n k Γ Γ') (ht : env.HasType univs Γ e T)
    (hΔ : proofEraseCtx Γ' = Δ)
    (R : ProofShape.ScopedCompute Step Δ ((proofErase Γ e).liftN n k) out) :
    ∃ e', env.IsDefEq univs Γ e e' T ∧
      ProofShape.ScopedCompute Target (proofEraseCtx Γ) (proofErase Γ e) (proofErase Γ e') ∧
      (proofErase Γ e').liftN n k = out := by
  generalize hsrc : (proofErase Γ e).liftN n k = source at R
  induction R generalizing Γ Γ' k e T with
  | base R => exact hstep hΓ hΓ' W ht (hΔ ▸ hsrc ▸ R)
  | beta R =>
    rw [← hsrc, ← proofErase_liftN hΓ hΓ' W ht] at R
    obtain ⟨e', RR, HE⟩ := proofErase_beta_replay hΓ' (ht.weakN henv W) R
    rw [← lift'_consN_skipN] at RR
    obtain ⟨e₀, R₀, rfl⟩ := betaRed_lift_inv RR
    have HH := R₀.simAt henv.orderedStrong henv.betaSubjectReduction hΓ T ht
    rw [lift'_consN_skipN, proofErase_liftN hΓ hΓ' W HH.hasType.2] at HE
    exact ⟨e₀, HH, .beta (proofErase_beta_forward hΓ ht R₀), HE⟩
  | trans _ _ ih1 ih2 =>
    obtain ⟨e₁, H₁, R₁, E₁⟩ := ih1 hΓ hΓ' W ht hΔ hsrc
    obtain ⟨e₂, H₂, R₂, E₂⟩ := ih2 hΓ hΓ' W H₁.hasType.2 hΔ E₁
    exact ⟨e₂, H₁.trans H₂, R₁.trans R₂, E₂⟩
  | app _ _ ihf iha =>
    obtain ⟨_, _, hs, Hf, Ha⟩ := ProofShape.liftN_app_inv hsrc
    obtain ⟨f, a, rfl, hn, Ef, Ea⟩ := erase_app_inv hs
    rw [← Ef] at Hf
    rw [← Ea] at Ha
    obtain ⟨_, _, hf, ha⟩ := ht.app_inv henv hΓ
    obtain ⟨f', HF, RF, EF⟩ := ihf hΓ hΓ' W hf hΔ Hf
    obtain ⟨a', HA, RA, EA⟩ := iha hΓ hΓ' W ha hΔ Ha
    have HH := SimAt.app henv.orderedStrong hΓ (equality_simAt hΓ HF) (equality_simAt hΓ HA) T ht
    refine ⟨_, HH, ?_, ?_⟩
    · simpa only [proofErase, if_neg hn, if_neg (mt (isProof_congr hΓ HH).2 hn)] using
        ProofShape.ScopedCompute.app RF RA
    simp only [proofErase, if_neg (mt (isProof_congr hΓ HH).2 hn), ProofShape.liftN, EF, EA]
  | proj _ ihm =>
    obtain ⟨_, hs, Hm⟩ := ProofShape.liftN_proj_inv hsrc
    obtain ⟨m, rfl, hn, Em⟩ := erase_proj_inv hs
    rw [← Em] at Hm
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ := ht.proj_inv henv hΓ
    obtain ⟨m', HM, RM, EM⟩ := ihm hΓ hΓ' W hm.hasType.2 hΔ Hm
    have HH := SimAt.proj henv.orderedStrong hΓ (equality_simAt hΓ HM) T ht
    refine ⟨_, HH, ?_, ?_⟩
    · simpa only [proofErase, if_neg hn, if_neg (mt (isProof_congr hΓ HH).2 hn)] using
        ProofShape.ScopedCompute.proj RM
    simp only [proofErase, if_neg (mt (isProof_congr hΓ HH).2 hn), ProofShape.liftN, EM]
  | lam _ _ ihA ihb =>
    obtain ⟨_, _, hs, HA, Hb⟩ := ProofShape.liftN_lam_inv hsrc
    obtain ⟨A, b, rfl, hn, EA, Eb⟩ := erase_lam_inv hs
    rw [← EA] at HA
    rw [← Eb] at Hb
    obtain ⟨⟨u, hA⟩, _, hb⟩ := ht.lam_inv henv hΓ
    have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
    have hΓA' : OnCtx (A.liftN n k :: Γ') (env.IsType univs) := ⟨hΓ', u, hA.weakN henv W⟩
    obtain ⟨A', HAA, RAA, EAA⟩ := ihA hΓ hΓ' W hA hΔ HA
    obtain ⟨b', Hbb, Rbb, Ebb⟩ := ihb hΓA hΓA' W.succ hb
      (by simp only [proofEraseCtx, proofErase_liftN hΓ hΓ' W hA, hΔ, HA]) Hb
    have HH := SimAt.lam henv.orderedStrong hΓ (equality_simAt hΓ HAA)
      (fun _ => equality_simAt hΓA Hbb) T ht
    have Ebb' := proofErase_defeqCtx hΓA (.succ .zero HAA) Hbb.hasType.2
    refine ⟨_, HH, ?_, ?_⟩
    · simpa only [proofErase, if_neg hn, if_neg (mt (isProof_congr hΓ HH).2 hn), ← Ebb'] using
        ProofShape.ScopedCompute.lam RAA Rbb
    simp only [proofErase, if_neg (mt (isProof_congr hΓ HH).2 hn), ProofShape.liftN,
      EAA, ← Ebb', Ebb]
  | forallE _ _ ihA ihB =>
    obtain ⟨_, _, hs, HA, HB⟩ := ProofShape.liftN_forallE_inv hsrc
    obtain ⟨A, B, rfl, hn, EA, EB⟩ := erase_forallE_inv hs
    rw [← EA] at HA
    rw [← EB] at HB
    obtain ⟨⟨u, hA⟩, _, hB⟩ := ht.forallE_inv henv
    have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
    have hΓA' : OnCtx (A.liftN n k :: Γ') (env.IsType univs) := ⟨hΓ', u, hA.weakN henv W⟩
    obtain ⟨A', HAA, RAA, EAA⟩ := ihA hΓ hΓ' W hA hΔ HA
    obtain ⟨B', HBB, RBB, EBB⟩ := ihB hΓA hΓA' W.succ hB
      (by simp only [proofEraseCtx, proofErase_liftN hΓ hΓ' W hA, hΔ, HA]) HB
    have HH := SimAt.forallE henv.orderedStrong hΓ (equality_simAt hΓ HAA)
      (fun _ => equality_simAt hΓA HBB) T ht
    have EBB' := proofErase_defeqCtx hΓA (.succ .zero HAA) HBB.hasType.2
    refine ⟨_, HH, ?_, ?_⟩
    · simpa only [proofErase, if_neg hn, if_neg (mt (isProof_congr hΓ HH).2 hn), ← EBB'] using
        ProofShape.ScopedCompute.forallE RAA RBB
    simp only [proofErase, if_neg (mt (isProof_congr hΓ HH).2 hn), ProofShape.liftN,
      EAA, ← EBB', EBB]

/-- Selected type recovery descends with a reusable lower recovery
certificate whenever its primitive computations have certificate descent.
No exact recovery at an arbitrary assigned type is asserted. -/
theorem proofErase_scoped_recovery_certificate_descend
    (hstep : ErasedScopedPrimitiveCertificateDescent Step Target)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.LiftN n k Γ Γ')
    (ht : env.HasType univs Γ e T) (hΔ : proofEraseCtx Γ' = Δ)
    (R : ProofShape.ScopedTypeRecovery Step Δ ((proofErase Γ e).liftN n k) out) :
    ∃ A, env.HasType univs Γ e A ∧
      ProofShape.ScopedTypeRecovery Target (proofEraseCtx Γ) (proofErase Γ e) (proofErase Γ A) ∧
      (proofErase Γ A).liftN n k = out := by
  generalize Ee : (proofErase Γ e).liftN n k = source at R
  induction R generalizing Γ Γ' k e T with
  | bvar =>
    obtain ⟨i, rfl, rfl⟩ := erased_lift_bvar_inv Ee
    obtain ⟨A, hl⟩ := ht.bvar_inv henv hΓ
    have H := ErasedOracleValid.above (erasedTypeOracle_valid hΓ') hΓ hΓ' W hl
    refine ⟨A, .bvar hl, ?_, ?_⟩
    · have hn : ¬ IsProof Γ (.bvar i) := by
        intro HP
        rw [proofErase_eq_proof.2 HP] at Ee
        cases Ee
      have HR := ProofShape.ScopedTypeRecovery.bvar (Step := Target) (Δ := proofEraseCtx Γ) (i := i)
      rw [proofEraseCtx_oracle, erasedTypeOracle_valid hΓ hl] at HR
      simpa only [proofErase, if_neg hn] using HR
    rw [← hΔ, proofEraseCtx_oracle]
    exact H.symm
  | sort hu =>
    obtain rfl := erase_sort_inv (ProofShape.liftN_sort_inv Ee)
    refine ⟨_, .sort hu, ?_, ?_⟩
    · simpa only [proofErase,
        if_neg (not_isProof_of_sort hΓ (HasType.sort hu)),
        if_neg (not_isProof_of_sort hΓ (HasType.sort (l := .succ _) hu))] using
        (ProofShape.ScopedTypeRecovery.sort (Step := Target) (Δ := proofEraseCtx Γ) hu)
    rw [show proofErase Γ (.sort (.succ _)) = .sort (.succ _) from
      if_neg (not_isProof_of_sort hΓ (HasType.sort (l := .succ _) hu))]
    rfl
  | const hc hw hn =>
    rename_i c ci ls Δ₀
    obtain rfl := erase_const_inv (ProofShape.liftN_const_inv Ee)
    have hc0 := HasType.const (Γ := []) hc hw hn
    obtain ⟨_, hT⟩ := hc0.isType henv (by trivial)
    refine ⟨_, .const hc hw hn, ?_, ?_⟩
    · have hnp : ¬ IsProof Γ (.const c ls) := by
        intro HP
        rw [proofErase_eq_proof.2 HP] at Ee
        cases Ee
      rw [show proofErase Γ (.const c ls) = .const c ls from if_neg hnp,
        proofErase_closed_context ((henv.ordered.closedC hc).instL) hT hΓ]
      exact .const hc hw hn
    rw [proofErase_closed_context ((henv.ordered.closedC hc).instL) hT hΓ,
      proofErase_closed_liftN ((henv.ordered.closedC hc).instL.mono (Nat.zero_le _))]
  | lam _ ih =>
    obtain ⟨_, _, Es, EA, Eb⟩ := ProofShape.liftN_lam_inv Ee
    obtain ⟨A, b, rfl, _, EAA, Ebb⟩ := erase_lam_inv Es
    rw [← EAA] at EA
    rw [← Ebb] at Eb
    obtain ⟨⟨u, hA⟩, _, hb⟩ := ht.lam_inv henv hΓ
    have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
    have hΓA' : OnCtx (A.liftN n k :: Γ') (env.IsType univs) := ⟨hΓ', u, hA.weakN henv W⟩
    obtain ⟨B, hB, RB, EB⟩ := ih hΓA hΓA' W.succ hb
      (by simp only [proofEraseCtx, proofErase_liftN hΓ hΓ' W hA, hΔ, EA]) Eb
    obtain ⟨_, hPi⟩ := (HasType.lam hA hB).isType henv hΓ
    refine ⟨.forallE A B, .lam hA hB, ?_, ?_⟩
    · rw [Es, ← EAA, ← Ebb]
      rw [show proofErase Γ (.forallE A B) = .forallE _ _ from if_neg (not_isProof_of_sort hΓ hPi)]
      exact .lam RB
    simp only [proofErase, if_neg (not_isProof_of_sort hΓ hPi), ProofShape.liftN, EA, EB]
  | app _ ih =>
    obtain ⟨_, _, Es, Ef, Ea⟩ := ProofShape.liftN_app_inv Ee
    obtain ⟨f, a, rfl, hna, Eff, Eaa⟩ := erase_app_inv Es
    rw [← Eff] at Ef
    rw [← Eaa] at Ea
    obtain ⟨_, _, hf, ha⟩ := ht.app_inv henv hΓ
    obtain ⟨F, hfF, RF, EF⟩ := ih hΓ hΓ' W hf hΔ Ef
    obtain ⟨_, _, Es, EA, EB⟩ := ProofShape.liftN_forallE_inv EF
    obtain ⟨A, B, rfl, _, EAA, EBB⟩ := erase_forallE_inv Es
    rw [← EAA] at EA
    rw [← EBB] at EB
    obtain ⟨⟨_, hCA⟩, _⟩ := (hf.uniqU henv hΓ hfF).forallE_inv henv hΓ
    have haA := hCA.defeq ha
    obtain ⟨⟨u, hA⟩, _, hB⟩ := (hfF.isType henv hΓ).forallE_inv henv
    have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
    refine ⟨B.inst a, .app hfF haA, ?_, ?_⟩
    · rw [show proofErase Γ (.app f a) = .app _ _ from if_neg hna,
        proofErase_instN hΓA haA Ctx.InstN.zero hB]
      rw [Es, ← EAA, ← EBB] at RF
      exact .app RF
    rw [proofErase_instN hΓA haA Ctx.InstN.zero hB]
    simpa only [Nat.add_zero, EB, Ea] using
      (ProofShape.liftN_instN (proofErase (A :: Γ) B) (proofErase Γ a) n k 0)
  | forallE _ _ ihA ihB =>
    obtain ⟨_, _, Es, EA, EB⟩ := ProofShape.liftN_forallE_inv Ee
    obtain ⟨A, B, rfl, _, EAA, EBB⟩ := erase_forallE_inv Es
    rw [← EAA] at EA
    rw [← EBB] at EB
    obtain ⟨⟨_, hA⟩, _, hB⟩ := ht.forallE_inv henv
    obtain ⟨S, hAu, RA, ES⟩ := ihA hΓ hΓ' W hA hΔ EA
    obtain rfl := erase_sort_inv (ProofShape.liftN_sort_inv ES)
    have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, _, hAu⟩
    have hΓA' : OnCtx (A.liftN n k :: Γ') (env.IsType univs) := ⟨hΓ', _, hAu.weakN henv W⟩
    obtain ⟨S, hBv, RB, ES⟩ := ihB hΓA hΓA' W.succ hB
      (by simp only [proofEraseCtx, proofErase_liftN hΓ hΓ' W hAu, hΔ, EA]) EB
    obtain rfl := erase_sort_inv (ProofShape.liftN_sort_inv ES)
    refine ⟨_, .forallE hAu hBv, ?_, ?_⟩
    · rw [Es, ← EAA, ← EBB]
      have hS := HasType.sort (env := env) (U := univs) (Γ := Γ) (l := .imax _ _)
        (show (VLevel.imax _ _).WF univs from ⟨hAu.sort_r henv hΓ, hBv.sort_r henv hΓA⟩)
      rw [show proofErase Γ (.sort (.imax _ _)) = .sort (.imax _ _) from
        if_neg (not_isProof_of_sort hΓ hS)]
      rw [show proofErase Γ (.sort _) = .sort _ from if_neg (not_isProof_of_sort hΓ
        (HasType.sort (hAu.sort_r henv hΓ)))] at RA
      rw [show proofErase (A :: Γ) (.sort _) = .sort _ from if_neg (not_isProof_of_sort hΓA
        (HasType.sort (hBv.sort_r henv hΓA)))] at RB
      exact .forallE RA RB
    rw [show proofErase Γ (.sort (.imax _ _)) = .sort (.imax _ _) from
      if_neg (not_isProof_of_sort hΓ
        (HasType.sort (l := .imax _ _) ⟨hAu.sort_r henv hΓ, hBv.sort_r henv hΓA⟩))]
    rfl
  | proj hi HT hj hlen R ih =>
    rename_i s info ls doms result j argsRaw
    obtain ⟨_, Es, Em⟩ := ProofShape.liftN_proj_inv Ee
    obtain ⟨m, rfl, hn, Emm⟩ := erase_proj_inv Es
    rw [← Emm] at Em
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ := ht.proj_inv henv hΓ
    obtain ⟨F, hmF, RM, EF⟩ := ih hΓ hΓ' W hm.hasType.2 hΔ Em
    obtain ⟨rawArgs, Es, Eargs⟩ := ProofShape.liftN_const_spine_inv EF
    obtain ⟨args, rfl, rfl⟩ := proofErase_const_spine_inv Es
    obtain ⟨hj', F, hproj, E⟩ := proofErase_projection_at_recovered_family hΓ hi HT ht hn hmF
    have E' : proofErase Γ F = ProofShape.projectionType s info doms j hj
        (args.map (proofErase Γ)) (proofErase Γ m) := by
      simpa only [ProofShape.projectionType, List.map_take] using E
    refine ⟨F, hproj, ?_, ?_⟩
    · rw [show proofErase Γ (.proj s j m) = .proj s j _ from if_neg hn, E']
      rw [Es] at RM
      apply ProofShape.ScopedTypeRecovery.proj hi HT hj _ RM
      have hh := congrArg List.length Eargs
      simp only [List.length_map] at hh ⊢
      omega
    rw [E', ProofShape.projectionType_liftN HT hj (by
      have hh := congrArg List.length Eargs
      simp only [List.length_map] at hh ⊢
      omega), ← Eargs, Em]
  | convert _ RC ih =>
    obtain ⟨A, heA, RA, EA⟩ := ih hΓ hΓ' W ht hΔ Ee
    obtain ⟨u, hA⟩ := heA.isType henv hΓ
    obtain ⟨A', HAA, RAA, EA'⟩ := proofErase_scoped_compute_certificate_descend hstep hΓ hΓ' W hA hΔ (EA ▸ RC)
    exact ⟨A', HAA.defeq heA, .convert RA RAA, EA'⟩

/-- Ordinary-core primitives have certificate-preserving descent at the
same stage. Raw retraction is used only after typed descent proves that the
source and output are both lifted erasures; no removed binder is inhabited. -/
theorem erased_joint_zero_certificate_descent (hs : D.Sound env univs) :
    ErasedScopedPrimitiveCertificateDescent (ErasedJointStage D 0) (ErasedJointStage D 0) := by
  intro Γ Γ' n k e T out hΓ hΓ' W ht H
  obtain ⟨e', HE, Ee⟩ := ErasedPrimitiveReplay.toDescent hs (erased_iota_replay hs)
    hΓ hΓ' W ht H
  refine ⟨e', HE, .base ?_, Ee⟩
  have HR := erased_iota_primitive_subst
    (σ := ProofShape.Subst.retract (.consN (.skipN .refl n) k)) H
  rw [← Ee, ← ProofShape.lift'_consN_skipN, ← ProofShape.lift'_consN_skipN,
    ProofShape.subst_retract_lift', ProofShape.subst_retract_lift'] at HR
  exact HR

/-- Stage-zero computation certificates are invariant under inserting unused
binders, at every cut position and with the prescribed raw output. Reflection
requires source typing below, but no inhabitant of the inserted declarations. -/
theorem proofErase_joint_zero_compute_lift_iff
    (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.LiftN n k Γ Γ') (ht : env.HasType univs Γ e T) :
    ProofShape.ScopedCompute (ErasedJointStage D 0) (proofEraseCtx Γ')
      ((proofErase Γ e).liftN n k) (out.liftN n k) ↔
    ProofShape.ScopedCompute (ErasedJointStage D 0) (proofEraseCtx Γ) (proofErase Γ e) out := by
  constructor
  · intro H
    obtain ⟨e', _, R, E⟩ := proofErase_scoped_compute_certificate_descend
      (erased_joint_zero_certificate_descent hs) hΓ hΓ' W ht rfl H
    have E' : proofErase Γ e' = out := ProofShape.lift'_inj (ρ := .consN (.skipN .refl n) k)
      (by simpa only [ProofShape.lift'_consN_skipN] using E)
    exact E' ▸ R
  · intro H
    have R := H.rename (Step' := ErasedJointStage D 0) (fun H _ => erased_iota_primitive_subst H)
      (ProofShape.ContextRenaming.of_liftN hΓ hΓ' W)
    simpa only [subst_bvar_liftN] using R

/-- Exact selected recovery at stage zero is invariant under an unused binder
block. This returns the original selected raw type, not merely some convertible
lower typing. It does not assert completeness of recovery for assigned types. -/
theorem proofErase_joint_zero_recovery_lift_iff
    (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.LiftN n k Γ Γ') (ht : env.HasType univs Γ e T) :
    ProofShape.ScopedTypeRecovery (ErasedJointStage D 0) (proofEraseCtx Γ')
      ((proofErase Γ e).liftN n k) (out.liftN n k) ↔
    ProofShape.ScopedTypeRecovery (ErasedJointStage D 0) (proofEraseCtx Γ) (proofErase Γ e) out := by
  constructor
  · intro H
    obtain ⟨A, _, R, E⟩ := proofErase_scoped_recovery_certificate_descend
      (erased_joint_zero_certificate_descent hs) hΓ hΓ' W ht rfl H
    have E' : proofErase Γ A = out := ProofShape.lift'_inj (ρ := .consN (.skipN .refl n) k)
      (by simpa only [ProofShape.lift'_consN_skipN] using E)
    exact E' ▸ R
  · intro H
    have R := H.rename (Step' := ErasedJointStage D 0) (fun H _ => erased_iota_primitive_subst H)
      (ProofShape.ContextRenaming.of_liftN hΓ hΓ' W)
    simpa only [subst_bvar_liftN] using R

end Lean4Lean.VEnv.Strengthening
