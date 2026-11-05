import Lean4Lean.Theory.Typing.Strengthening.ProofErasureFirstStageSimulation
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJoinedNativeGuard

/-! # Retain the original Eq-prefix annotation while computing its guard

Computing a prefix's endpoints before contracting it changes the generated
proof-domain annotation. A native eta frame retains the original annotation;
computation then runs inside the frame and beta erases the changed one.
This supplies exact output after operational guard exposure, not a theorem
that arbitrary comparison guards admit such exposure.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private subst_bvar_liftN from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRenaming
variable [Params] {D : Definitions}

/-- A witnessed domain permits weakening any fixed-stage computation beneath
its binder without increasing guard depth. The endpoints can be raw shapes. -/
theorem staged_compute_under_domain
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (SD : DomainSort Δ A u)
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionStage D n) Δ e out) :
    ScopedCompute (ErasedStaticStructureEtaExpansionStage D n) (A :: Δ)
      (e.liftN 1) (out.liftN 1) := by
  obtain ⟨Γ, B, hΓ, rfl, hB, rfl⟩ := SD
  have H := R.rename (erased_static_structure_eta_expansion_stage_rename heq hs n)
    (ContextRenaming.of_liftN hΓ (show OnCtx (B :: Γ) _ from ⟨hΓ, u, hB⟩) Ctx.LiftN.one)
  simpa only [subst_bvar_liftN, proofEraseCtx] using H

/-- Eta can retain a source's selected domain while computation exposes a
constant lambda at a different domain. Beta erases the computed annotation,
so the original selected domain is restored without a reverse domain path. -/
theorem staged_eta_retains_constant_domain {m : ProofShape}
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D n) Δ f (.forallE A B))
    (SD : DomainSort Δ A u)
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionStage D (n + 1)) Δ f (.lam L (m.liftN 1))) :
    ScopedCompute (ErasedStaticStructureEtaExpansionStage D (n + 1)) Δ f (.lam A (m.liftN 1)) := by
  have RE : ScopedCompute (ErasedStaticStructureEtaExpansionStage D (n + 1)) Δ f
      (.lam A (.app (f.liftN 1) (etaArgument u))) :=
    .base (.inr (.inr (.inr (.inr (.inl (.intro RN SD))))))
  apply RE.trans ((ScopedCompute.lam .refl (.app (staged_compute_under_domain heq hs SD R) .refl)).trans ?_)
  apply ScopedCompute.beta
  apply ProofShape.BetaRed.lam .refl
  have RB := ProofShape.BetaRed.beta (A := L.liftN 1) (b := (m.liftN 1).liftN 1 1) (a := etaArgument u)
  have E : ((m.liftN 1).liftN 1 1).inst (etaArgument u) = m.liftN 1 := by
    rw [← ProofShape.liftN_comm m 1 1 0 0 (Nat.zero_le _)]
    simp only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN,
      ProofShape.Subst.one, ProofShape.lift_subst_cons, ProofShape.subst_id]
  rw [E] at RB
  exact RB

/-- The literal five-argument canonical Eq recursor follows its stored type
exactly. This declaration walk needs no computational conversion of a supplied
argument and supplies the old proof-domain guard before any endpoint changes. -/
theorem eq_prefix_literal_native_guard
    (heq : env.HasCanonicalEq) (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ (Strengthening.eqRecBeforeMajor v w α a M m b) T)
    (hn : ¬ IsProof Γ (Strengthening.eqRecBeforeMajor v w α a M m b)) :
    ∃ body,
      ScopedTypeRecovery Step (proofEraseCtx Γ)
        (proofErase Γ (Strengthening.eqRecBeforeMajor v w α a M m b))
        (.forallE (eqProofType w (proofErase Γ α) (proofErase Γ a) (proofErase Γ b)) body) ∧
      DomainSort (proofEraseCtx Γ)
        (eqProofType w (proofErase Γ α) (proofErase Γ a) (proofErase Γ b)) .zero := by
  obtain ⟨hv, hw, hα, ha, hM, hm, hb⟩ := eqRecBeforeMajor_typings henv heq hΓ ⟨_, ht⟩
  have hls : ∀ l ∈ [v, w], l.WF univs := by
    intro l hl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl <;> assumption
  have hc : env.HasType univs Γ (.const ``Eq.rec [v, w]) (canonicalEqRecType.instL [v, w]) :=
    .const heq.2.2.1 hls rfl
  obtain ⟨residual, HW, _⟩ := HasType.mkApps_telescope henv hΓ hc ⟨_, ht⟩ (by rfl)
  have ER : residual = .forallE (eqApp w α a b) (.app (.app M.lift b.lift) (.bvar 0)) := by
    cases HW with | cons _ H =>
    cases H with | cons _ H =>
    cases H with | cons _ H =>
    cases H with | cons _ H =>
    cases H with | cons _ H =>
    cases H
    simp [instL, VLevel.inst, VExpr.inst, instVar, inst_liftN_lo, eqApp, VExpr.lift]
  rw [ER] at HW
  have RN := proofErase_const_native_recovery (Step := Step) hΓ heq.2.2.1 hls rfl HW hn
  have hf := eqRecBeforeMajor_typed heq hv hw hα ha hM hm hb
  obtain ⟨_, hPi⟩ := hf.isType henv hΓ
  have hE := HasType.eqApp heq hw hα ha hb
  have EE := proofErase_eqProofType heq hw hΓ hα ha hb
  rw [show proofErase Γ (.forallE (eqApp w α a b) (.app (.app M.lift b.lift) (.bvar 0))) =
      .forallE (proofErase Γ (eqApp w α a b)) _ from if_neg (not_isProof_of_sort hΓ hPi), EE] at RN
  exact ⟨_, RN, EE ▸ DomainSort.of_typed hΓ hE⟩

/-- Operationally exposing the carrier and endpoints to a stage-zero guard
suffices to contract the original typed Eq prefix in stage one, with its exact
original proof-domain annotation. The motive may compute independently; the
minor is retained. No reverse endpoint or carrier paths are needed. -/
theorem first_stage_eq_prefix_of_computed_guard
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ (Strengthening.eqRecBeforeMajor v w α a M m b) T)
    (hn : ¬ IsProof Γ (Strengthening.eqRecBeforeMajor v w α a M m b))
    (Rα : ScopedCompute (ErasedStaticStructureEtaExpansionStage D 1) (proofEraseCtx Γ) (proofErase Γ α) α')
    (Ra : ScopedCompute (ErasedStaticStructureEtaExpansionStage D 1) (proofEraseCtx Γ) (proofErase Γ a) a')
    (RM : ScopedCompute (ErasedStaticStructureEtaExpansionStage D 1) (proofEraseCtx Γ) (proofErase Γ M) M')
    (Rb : ScopedCompute (ErasedStaticStructureEtaExpansionStage D 1) (proofEraseCtx Γ) (proofErase Γ b) b')
    (HG : ComputedJointCarrierGuard (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ) α' a' b') :
    ScopedCompute (ErasedStaticStructureEtaExpansionStage D 1) (proofEraseCtx Γ)
      (proofErase Γ (Strengthening.eqRecBeforeMajor v w α a M m b))
      (.lam (eqProofType w (proofErase Γ α) (proofErase Γ a) (proofErase Γ b)) ((proofErase Γ m).liftN 1)) := by
  obtain ⟨body, RN, SD⟩ := eq_prefix_literal_native_guard
    (Step := ErasedStaticStructureEtaExpansionStage D 0) heq hΓ ht hn
  apply staged_eta_retains_constant_domain heq hs RN SD (L := eqProofType w α' a' b')
  have ES := proofErase_const_spine hΓ (args := [α, a, M, m, b]) ht hn
  change proofErase Γ (Strengthening.eqRecBeforeMajor v w α a M m b) =
    ProofShape.eqRecBeforeMajor v w (proofErase Γ α) (proofErase Γ a)
      (proofErase Γ M) (proofErase Γ m) (proofErase Γ b) at ES
  rw [ES]
  have RC : ScopedCompute (ErasedStaticStructureEtaExpansionStage D 1) (proofEraseCtx Γ)
      (ProofShape.eqRecBeforeMajor v w (proofErase Γ α) (proofErase Γ a)
        (proofErase Γ M) (proofErase Γ m) (proofErase Γ b))
      (ProofShape.eqRecBeforeMajor v w α' a' M' (proofErase Γ m) b') :=
    .app (.app (.app (.app (.app .refl Rα) Ra) RM) .refl) Rb
  exact RC.trans (.base (.inr (.inr (.inl (.intro HG)))))

/-- A stage-one join of the actual endpoints already enables the exact prefix
contraction at stage one. A naive guard-depth bound would use stage two; the
retained eta annotation removes that extra layer. The endpoint paths may use
all first-stage primitives, not just beta or the ordinary core. -/
theorem first_stage_eq_prefix_of_endpoint_join
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ (Strengthening.eqRecBeforeMajor v w α a M m b) T)
    (hn : ¬ IsProof Γ (Strengthening.eqRecBeforeMajor v w α a M m b))
    (Ra : ScopedCompute (ErasedStaticStructureEtaExpansionStage D 1) (proofEraseCtx Γ) (proofErase Γ a) shared)
    (Rb : ScopedCompute (ErasedStaticStructureEtaExpansionStage D 1) (proofEraseCtx Γ) (proofErase Γ b) shared) :
    ScopedCompute (ErasedStaticStructureEtaExpansionStage D 1) (proofEraseCtx Γ)
      (proofErase Γ (Strengthening.eqRecBeforeMajor v w α a M m b))
      (.lam (eqProofType w (proofErase Γ α) (proofErase Γ a) (proofErase Γ b)) ((proofErase Γ m).liftN 1)) :=
  first_stage_eq_prefix_of_computed_guard heq hs hΓ ht hn .refl Ra .refl Rb (.carrierChecked (.leaf .refl))

end Lean4Lean.VEnv.Strengthening
