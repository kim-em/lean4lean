import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCoreOracleReduction
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCoreHeadBoundary

/-! # Free-major cast obstruction after the quotient-core repair

The repaired core embeds in the existing full head model, which already
contains the added quotient equations. Thus those equations do not repair the
free-major Eq cast. A guarded singleton layer is still needed for that test.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params PureObservation
open ConstructorObservation (EtaCompute)
open private forget_scope from Lean4Lean.Theory.Typing.Strengthening.ProofErasureCoreOracleReduction
open private erase_forallE_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta

/-- Every typed repaired-core pattern computation embeds in the full head model,
including its proposition-source quotient and registered structure equations. -/
theorem ErasedQuotCore.pattern_full_head_compute {env : VEnv} (henv : env.WF) (U : Nat)
    (heq : env.HasCanonicalEq) (hq : QuotRegistered env) :
    letI := henv.params U
    ∀ {e out Γ T}, PatternCompute (definitions hq) e out →
      OnCtx Γ (env.IsType U) → env.HasType U Γ e T →
      EtaCompute (FullHead.definitions henv heq U) e out := by
  letI := henv.params U
  intro e out Γ T R hΓ ht
  induction R generalizing Γ T with
  | base R =>
    apply EtaCompute.compute
    apply R.of_inclusion
    intro c ls rhs H
    apply Or.inl
    have HH := RegisteredStructure.definitions_inclusion H
    change (ClosedStructure.definitions (ClosedQuot.definitions env U henv hq)).unfolds c ls rhs at HH
    simpa only [FullHead.quotDefinitions, dif_pos hq] using HH
  | trans R₁ R₂ ih₁ ih₂ =>
    exact (ih₁ hΓ ht).trans (ih₂ hΓ (R₁.simAt (ErasedQuotCore.sound hq) hΓ _ ht).hasType.2)
  | pattern hp hm hc =>
    apply ClosedSingleton.etaCompute_base heq
    apply (concrete_pattern_compute henv hΓ hp hm (hc hΓ hm ht) ⟨_, ht⟩).of_inclusion
    intro c ls rhs H
    rcases H with H | H
    · exact .inl (FullHead.quot_base henv _ _ _ H)
    · exact .inr H
  | app _ _ ihf ihx =>
    obtain ⟨_, _, hf, hx⟩ := ht.app_inv henv hΓ
    exact .app (ihf hΓ hf) (ihx hΓ hx)
  | lam _ _ ihA ihb =>
    obtain ⟨⟨u, hA⟩, _, hb⟩ := ht.lam_inv henv hΓ
    exact .lam (ihA hΓ hA) (ihb (show OnCtx (_ :: Γ) _ from ⟨hΓ, u, hA⟩) hb)
  | forallE _ _ ihA ihB =>
    obtain ⟨⟨u, hA⟩, _, hB⟩ := ht.forallE_inv henv
    exact .forallE (ihA hΓ hA) (ihB (show OnCtx (_ :: Γ) _ from ⟨hΓ, u, hA⟩) hB)
  | proj _ ihm =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ := ht.proj_inv henv hΓ
    exact .proj (ihm hΓ hm.hasType.2)

/-- Adding the missing quotient equation does not expose a Pi from a reflexive
cast with a free equality major. The full head model already includes that
quotient equation and excludes the Pi exposure. -/
theorem ErasedQuotCore.cast_no_pi {env : VEnv} (henv : env.WF) (U : Nat)
    (hquot : QuotRegistered env) :
    letI := henv.params U
    ∀ {Γ X u i A B A' B'}, env.HasCanonicalEq → u.WF U →
      OnCtx Γ (env.IsType U) → env.HasType U Γ X (.sort u) →
      env.HasType U Γ (.bvar i) (eqApp (.succ u) (.sort u) X X) →
      env.HasType U Γ (.forallE A B) X →
      ¬ ProofShape.ScopedCompute (fun _ => Step hquot) (proofEraseCtx Γ)
        (proofErase Γ (typeCast u X X (.bvar i) (.forallE A B))) (.forallE A' B') := by
  letI := henv.params U
  intro Γ X u i A B A' B' heq hu hΓ hX hq hpi R
  obtain ⟨HC, HN⟩ := ConstructorObservation.canonical_cast_full_boundary henv heq hu hΓ hX hq hpi
  obtain ⟨out, RR, _, EE⟩ := replay hquot hΓ HC.hasType.1 (forget_scope R)
  obtain ⟨D, C, rfl, _, _, _⟩ := erase_forallE_inv EE
  exact HN D C (pattern_full_head_compute henv U heq hquot RR hΓ HC.hasType.1)

end Lean4Lean.VEnv.Strengthening
