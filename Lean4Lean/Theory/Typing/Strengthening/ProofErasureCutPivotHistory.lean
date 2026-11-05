import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCutHistorySpinePivot

/-! # Monotone choices of the historical cut pivot

A selected actual body fixes the pivot as that body instantiated at the original
argument. Component rounds advance this same pivot by computation. Its native
outputs can therefore be used before subsequent rounds, without choosing an
unrelated witness after every step.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params] {D : PureObservation.Definitions}

/-- A component history together with the actual body that fixes its pivot.
Different body realizations are not silently identified. -/
def CutPivotHistory (D : PureObservation.Definitions) (Γ : List VExpr)
    (A b x : VExpr) (u : VLevel) (B : VExpr) (s : CutComponents) (d : VExpr) : Prop :=
  CutComponentHistory D Γ A b x u B s ∧
    env.IsDefEq univs (A :: Γ) b d B ∧ proofErase (A :: Γ) d = s.2.1

/-- The original body selects the original contractum as the first pivot. -/
theorem CutPivotHistory.refl
    (hA : env.HasType univs Γ A (.sort u)) (hb : env.HasType univs (A :: Γ) b B)
    (hx : env.HasType univs Γ x A) :
    CutPivotHistory D Γ A b x u B
      (proofErase Γ A, proofErase (A :: Γ) b, proofErase Γ x) b :=
  ⟨CutComponentHistory.refl hA hb hx, hb, rfl⟩

/-- One component round advances the chosen pivot by computation, not just
by definitional equality or by an existential common-reduct assertion. -/
theorem CutPivotHistory.advance
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (H : CutPivotHistory D Γ A b x u B s d)
    (HR : ¬ IsProof Γ x → ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D)
      (proofEraseCtx Γ) (proofErase Γ x) (proofErase Γ A))
    (R : CutComponentRound D (proofEraseCtx Γ) s t) :
    ∃ d', CutPivotHistory D Γ A b x u B t d' ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ (d.inst x)) (proofErase Γ (d'.inst x)) := by
  obtain ⟨HH, Hbd, Ed⟩ := H
  obtain ⟨C, HAC, EC, RA⟩ := HH.1
  obtain ⟨_, Hxy, _, _⟩ := HH.2.2
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, HAC.hasType.1⟩
  have HC : IsDefEqCtx env univs Γ (A :: Γ) (C :: Γ) := .succ .zero HAC
  have hdC := Hbd.hasType.2.defeqDFC henv HC
  have EdC : proofErase (C :: Γ) d = s.2.1 :=
    (proofErase_defeqCtx hΓA HC Hbd.hasType.2).symm.trans Ed
  have RD : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx (C :: Γ))
      (proofErase (C :: Γ) d) t.2.1 := by
    simpa only [proofEraseCtx, EC, EdC] using R.2.1
  have RD' := proofErase_static_structure_union_compute_backward_context heq hs hΓ HAC
    (EC ▸ RA) hdC RD
  obtain ⟨d', Hdd', Ed'⟩ := proofErase_scoped_compute_realize
    (erased_static_structure_eta_expansion_union_descent heq hs) hΓA Hbd.hasType.2 rfl rfl RD'
  refine ⟨d', ⟨HH.advance heq hs hΓ R, Hbd.trans Hdd', Ed'⟩, ?_⟩
  have RI := static_structure_union_compute_inst heq hs hΓ Hxy.hasType.1 HR Hbd.hasType.2 RD'
  rw [← Ed'] at RI
  simpa only [proofErase_instN hΓA Hxy.hasType.1 Ctx.InstN.zero Hbd.hasType.2,
    proofErase_instN hΓA Hxy.hasType.1 Ctx.InstN.zero Hdd'.hasType.2] using RI

/-- Finite rounds choose a final pivot reached from the already selected
pivot. This is the compatibility needed when an earlier guard has already
created an outer wrapper. -/
theorem CutPivotHistory.rounds
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (H : CutPivotHistory D Γ A b x u B s d)
    (HR : ¬ IsProof Γ x → ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D)
      (proofEraseCtx Γ) (proofErase Γ x) (proofErase Γ A))
    (R : ReflTransGen (CutComponentRound D (proofEraseCtx Γ)) s t) :
    ∃ d', CutPivotHistory D Γ A b x u B t d' ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ (d.inst x)) (proofErase Γ (d'.inst x)) := by
  induction R with
  | rfl => exact ⟨d, H, .refl⟩
  | tail _ R ih =>
    obtain ⟨d₁, H₁, R₁⟩ := ih
    obtain ⟨d₂, H₂, R₂⟩ := H₁.advance heq hs hΓ HR R
    exact ⟨d₂, H₂, R₁.trans R₂⟩

/-- The chosen pivot retains all current native outputs and a forward path
to the current raw contractum. It is the same pivot advanced by rounds. -/
theorem CutPivotHistory.native
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (H : CutPivotHistory D Γ A b x u B s d)
    (hn : ¬ IsProof Γ (.app (.lam A b) x))
    (HR : ¬ IsProof Γ x → ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D)
      (proofEraseCtx Γ) (proofErase Γ x) (proofErase Γ A)) :
    NativeOutputTransfer (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        s.redex (proofErase Γ (d.inst x)) ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ (d.inst x)) (s.2.1.inst s.2.2) := by
  obtain ⟨_, _, RA, HN⟩ := H.1.native_pivot_body heq hs hΓ H.2.1 H.2.2 hn HR
  exact ⟨HN, RA⟩

end Lean4Lean.VEnv.Strengthening
