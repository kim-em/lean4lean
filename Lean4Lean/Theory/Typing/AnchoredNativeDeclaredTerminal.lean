import Lean4Lean.Theory.Typing.AnchoredNativeSupportedReplay
import Lean4Lean.Theory.Typing.AnchoredNativeRhsOpening

/-! The canonical captured RHS is interpreted at the generated equation's
exact declared result. The source observer retained internally is the
eta-applied original RHS; target beta contraction is explicit. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

/-- Combine the checked capture producer with the strictly earlier-stage
whole RHS theorem. No natural-body typing is reinterpreted at the native rule
stage, and no caller-provided terminal conversion is required. -/
theorem NativeSupportedReplay.declaredTerminal
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hsource : sourceEnv.Ordered)
    (hle : sourceEnv ≤ env)
    (earlier : ∀ {Γ left right type}, sourceEnv.IsDefEqStrong U Γ left right type →
      GradedJoint env U registry Γ left right type)
    {target argumentSource : List VExpr} {argumentLocals : List Nat}
    {arguments : Subst} {argumentAvailable : Valuation}
    (hTarget : OnCtx target (env.IsType U))
    (rawArguments : Ctx.SubstEq env U target arguments arguments argumentSource)
    (argumentFits : PairedFits env U registry argumentSource target argumentLocals
      arguments arguments argumentAvailable)
    {domains : List VExpr} {plan : CapturePlan domains.reverse} {captures : Subst}
    {locals : List Nat} {available : Valuation}
    (replay : NativeSupportedReplay sourceEnv env U registry target argumentSource
      argumentLocals arguments argumentAvailable domains.reverse plan captures locals available)
    (closed : available.AtomClosed)
    {rhs result : VExpr}
    (original : sourceEnv.HasTypeStrong U [] (wrapLams domains rhs)
      (wrapForalls domains result) structural)
    (formation : sourceEnv.IsDefEqStrong U [] (wrapForalls domains result)
      (wrapForalls domains result) (.sort level))
    {demand : Profile n} {footprint : Footprint}
    (body : Obs env U registry target locals captures rhs demand footprint)
    (resources : footprint.Available available) :
    ProofInsertion env U target (plan.added arguments ++ target) (.skipN .refl plan.count) ∧
      Nonempty (DeclaredRhsResult env U registry (plan.added arguments ++ target) locals
        (raisedSubst captures plan.count) (plan.captures arguments)
        (Valuation.rename (.skipN .refl plan.count) available) domains rhs result
        (demand.rename (.skipN .refl plan.count))) := by
  obtain ⟨insertion, raw, fits⟩ := replay.canonical henv hscoped hle
    (fun original => earlier original) hTarget rawArguments argumentFits
  have observation := body.future henv insertion.toFuture
  have lifted : captures.lift_r (.skipN .refl plan.count) = raisedSubst captures plan.count := by
    funext i
    exact lift'_consN_skipN (k := 0)
  rw [lifted] at observation
  refine ⟨insertion, ?_⟩
  exact HasTypeStrong.declaredRhs (source := []) henv hscoped hsource hle earlier trivial original formation
    (closed.rename _) (insertion.targetWF henv)
    (by simpa only [List.append_nil] using raw)
    (by simpa only [List.append_nil] using fits) observation (resources.rename _)

end Lean4Lean.AnchoredSource.Adapted
