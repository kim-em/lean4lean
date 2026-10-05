import Lean4Lean.Theory.Typing.AnchoredNativeRhsPath

/-! A native function replay uses the fixed output support of its actual
application path. The arbitrary support selected inside the private native
frame is discarded at the first application; the final support is a literal
lift from the original path world, as required by protected-profile DROP. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

theorem NativeSupportedReplay.declaredTerminalPathFixed
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hsource : sourceEnv.Ordered)
    (hle : sourceEnv ≤ env)
    (earlier : ∀ {Γ left right type}, sourceEnv.IsDefEqStrong U Γ left right type →
      GradedJoint env U registry Γ left right type)
    {target argumentSource : List VExpr} {argumentLocals : List Nat}
    {arguments : Subst} {argumentAvailable : Valuation}
    (hTarget : OnCtx target (env.IsType U))
    (newValues : List VExpr) (newLength : newValues.length = argumentSource.length)
    (rawArguments : Ctx.SubstEq env U target arguments (nativeCaptureSubst newValues) argumentSource)
    (argumentFits : PairedFits env U registry argumentSource target argumentLocals
      arguments (nativeCaptureSubst newValues) argumentAvailable)
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
    {atom : Atom n} {footprint : Footprint}
    (body : Obs env U registry target locals captures rhs (.singleton atom) footprint)
    (resources : footprint.Available available)
    {Ω : List VExpr} {finalType : VExpr} {finalAtom : Atom m}
    (path : RhsApplicationPath env U registry n target (result.subst captures) atom
      m Ω finalType finalAtom)
    (nonempty : path.hasApplication = true) :
    ∃ Ω' τ, ProofInsertion env U Ω Ω' τ ∧
      ∃ changed : RhsApplicationPath env U registry n
        (plan.added (nativeCaptureSubst newValues) ++ target)
        ((result.subst captures).lift' (.skipN .refl plan.count))
        (atom.rename (.skipN .refl plan.count))
        m Ω' (finalType.lift' τ) (finalAtom.rename τ),
        (∀ expression, changed.leftAction (expression.lift' (.skipN .refl plan.count)) =
          (path.leftAction expression).lift' τ) ∧
        (∀ expression, changed.rightAction (expression.lift' (.skipN .refl plan.count)) =
          (path.rightAction expression).lift' τ) ∧
        Related env U registry Ω'
          ((path.leftAction (rhs.subst captures)).lift' τ)
          (changed.rightAction (rhs.subst (plan.captures (nativeCaptureSubst newValues))))
          (finalType.lift' τ) (.singleton (finalAtom.rename τ)) ((path.supportAction .empty).rename τ) := by
  obtain ⟨frame, ⟨terminal⟩⟩ := replay.declaredTerminalPair henv hscoped hsource hle earlier
    hTarget newValues newLength rawArguments argumentFits closed original formation body resources
  obtain ⟨Ω', τ, finalFrame, changed, leftEq, rightEq, supportEq, hasEq⟩ :=
    path.proofFutureWithSupport henv hscoped frame
  have literal := lowerProfile.related terminal.opened.bound henv (frame.targetWF henv)
    terminal.related
  have raised (expression : VExpr) : expression.subst (raisedSubst captures plan.count) =
      (expression.subst captures).lift' (.skipN .refl plan.count) := by
    have substitution : captures.lift_r (.skipN .refl plan.count) =
        raisedSubst captures plan.count := by
      funext i
      exact lift'_consN_skipN (k := 0)
    rw [← substitution, ← lift'_subst]
  have literal' : Related env U registry (plan.added (nativeCaptureSubst newValues) ++ target)
      ((rhs.subst captures).lift' (.skipN .refl plan.count))
      (rhs.subst (plan.captures (nativeCaptureSubst newValues)))
      ((result.subst captures).lift' (.skipN .refl plan.count))
      (.singleton (atom.rename (.skipN .refl plan.count)))
      (lowerProfile n terminal.opened.bound terminal.opened.support) := by
    simpa only [raised, Profile.rename_singleton] using literal
  have related := changed.replayFixed henv hscoped (hasEq.trans nonempty) (frame.targetWF henv) literal'
  have supported := supportEq .empty
  rw [Profile.rename_empty] at supported
  rw [supported] at related
  rw [leftEq] at related
  exact ⟨Ω', τ, finalFrame, changed, leftEq, rightEq, related⟩

end Lean4Lean.AnchoredSource.Adapted
