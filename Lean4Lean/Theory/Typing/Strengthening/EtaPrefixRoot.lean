import Lean4Lean.Theory.Typing.Strengthening.EtaPrefixExchange

/-! # Actual prefix roots after arbitrary finite eta paths

A checked prefix retains a nonempty function telescope. Eta therefore cannot
have created its constant head. The argument exchange theorem consequently
applies to every finite eta path before an actual prefix root.
-/
namespace Lean4Lean.VEnv.Strengthening.PureObservation
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params]

/-- Every actual unfolding check types its source by a Pi: at least its major
binder is still unsupplied. -/
theorem unfoldingCheck_function_source
    (H : UnfoldingCheck env univs Γ source program) :
    ∃ A B, env.HasType univs Γ source (.forallE A B) := by
  have ht := H.source_typed
  have hn := H.remaining_nonempty
  cases hd : program.domains with
  | nil => exact (hn hd).elim
  | cons A ds =>
    exact ⟨A, wrapForalls ds program.result, by
      simpa only [InductiveSignature.RecursorData.PrefixUnfolding.type, hd, wrapForalls,
        List.foldr_cons] using ht⟩

/-- An arbitrary finite eta path before a singleton-prefix root factors into an
actual earlier prefix, eta expansion, and ordinary normal comparison. -/
theorem eta_singleton_prefix_compute (hΓ : OnCtx Γ (env.IsType univs))
    (RE : TypedEtaExpansion Γ source (mkApps (.const name levels) args))
    (ht : env.HasType univs Γ source T)
    (R : PrefixUnfold env univs recursorData Γ name levels args rhs) :
    ∃ out mid, PrefixCompute D Γ source out ∧
      TypedEtaExpansion Γ out mid ∧ NormalEq Γ mid rhs := by
  have hfn : ∃ A B, env.HasType univs Γ (mkApps (.const name levels) args) (.forallE A B) := by
    cases R with | intro _ _ _ _ _ _ _ H => exact unfoldingCheck_function_source H
  obtain ⟨A, B, hf⟩ := hfn
  have hsource := hf.defeqU_l henv hΓ ⟨_, (RE.simAt hΓ _ ht).symm⟩
  obtain ⟨args0, rfl, HA⟩ := RE.const_spine_source hΓ (.inr ⟨A, B, hsource⟩)
  obtain ⟨out, mid, R0, HE, HN⟩ := singleton_prefix_eta_exchange hΓ HA ht R
  exact ⟨out, mid, .singleton R0, HE, HN⟩

/-- Quotient-prefix roots have the same arbitrary finite eta exchange, using
their actual nonempty telescope and actual checked lower rule. -/
theorem eta_quotient_prefix_compute (hΓ : OnCtx Γ (env.IsType univs))
    (RE : TypedEtaExpansion Γ source (mkApps (.const ``Quot.lift levels) args))
    (ht : env.HasType univs Γ source T)
    (R : QuotPrefixUnfold env univs Γ levels args rhs) :
    ∃ out mid, PrefixCompute D Γ source out ∧
      TypedEtaExpansion Γ out mid ∧ NormalEq Γ mid rhs := by
  have hfn : ∃ A B, env.HasType univs Γ (mkApps (.const ``Quot.lift levels) args) (.forallE A B) := by
    cases R with | intro _ _ _ _ H => exact unfoldingCheck_function_source H
  obtain ⟨A, B, hf⟩ := hfn
  have hsource := hf.defeqU_l henv hΓ ⟨_, (RE.simAt hΓ _ ht).symm⟩
  obtain ⟨args0, rfl, HA⟩ := RE.const_spine_source hΓ (.inr ⟨A, B, hsource⟩)
  obtain ⟨out, mid, R0, HE, HN⟩ := quotient_prefix_eta_exchange hΓ HA ht R
  exact ⟨out, mid, .quotient R0, HE, HN⟩

end Lean4Lean.VEnv.Strengthening.PureObservation
