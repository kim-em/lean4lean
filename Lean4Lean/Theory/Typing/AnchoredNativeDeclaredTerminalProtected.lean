import Lean4Lean.Theory.Typing.AnchoredNativeDeclaredTerminalPair
import Lean4Lean.Theory.Typing.AnchoredNativeWitnessedReplay
import Lean4Lean.Theory.Typing.AnchoredSupport

/-! The native terminal's type support is chosen in the original target
world, using the witnessed capture tuple and the original RHS theorem.
The canonical RHS is then retagged at that literal lifted support. Thus the
private proof slots introduced by capture replay never enter the support
that must survive later contraction. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

structure DeclaredTerminalProtectedResult (env : VEnv) (U : Nat)
    (registry : CanonicalHead.Registry) (target : List VExpr) (locals : List Nat)
    (captures canonical : Subst) (available : Valuation) (rhs result : VExpr)
    (demand : Profile n) (added : List VExpr) (count : Nat) where
  support : Profile n
  footprint : Footprint
  certificate : CodeCert env U registry target locals captures result support footprint
  resources : footprint.Available available
  typed : demand.HasType support
  typeCode : TypeRelated env U registry target (result.subst captures)
    (result.subst captures) support
  witnessed : Related env U registry target (rhs.subst captures) (rhs.subst captures)
    (result.subst captures) demand support
  insertion : ProofInsertion env U target (added ++ target) (.skipN .refl count)
  related : Related env U registry (added ++ target)
    ((rhs.subst captures).lift' (.skipN .refl count)) (rhs.subst canonical)
    ((result.subst captures).lift' (.skipN .refl count))
    (demand.rename (.skipN .refl count)) (support.rename (.skipN .refl count))

/-- The protected support comes from an actual base source certificate.
Only the existing strict predecessor theorem interprets the original RHS;
no certificate or semantic support is projected out of a private frame. -/
theorem NativeSupportedReplay.declaredTerminalPairProtected
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
    {demand : Profile n} {footprint : Footprint}
    (body : Obs env U registry target locals captures rhs demand footprint)
    (resources : footprint.Available available) :
    Nonempty (DeclaredTerminalProtectedResult env U registry target locals captures
      (plan.captures (nativeCaptureSubst newValues)) available rhs result demand
      (plan.added (nativeCaptureSubst newValues)) plan.count) := by
  obtain ⟨raw, fits⟩ := replay.witnessed henv hle hTarget rawArguments.left argumentFits.left
  obtain ⟨base⟩ := HasTypeStrong.declaredRhs (source := []) henv hscoped hsource hle earlier
    trivial original formation closed hTarget
    (by simpa only [List.append_nil] using raw)
    (by simpa only [List.append_nil] using fits) body resources
  obtain ⟨insertion, ⟨terminal⟩⟩ := replay.declaredTerminalPair henv hscoped hsource hle earlier
    hTarget newValues newLength rawArguments argumentFits closed original formation body resources
  have typed := base.opened.requestedTyped
  have code := TypeRelated.lower henv base.opened.bound base.opened.typeCode
  have witnessed := lowerProfile.related base.opened.bound henv hTarget base.related
  have related := lowerProfile.related terminal.opened.bound henv (insertion.targetWF henv)
    terminal.related
  have raised (expression : VExpr) : expression.subst (raisedSubst captures plan.count) =
      (expression.subst captures).lift' (.skipN .refl plan.count) := by
    have substitution : captures.lift_r (.skipN .refl plan.count) =
        raisedSubst captures plan.count := by
      funext i
      exact lift'_consN_skipN (k := 0)
    rw [← substitution, ← lift'_subst]
  simp only [raised] at related
  exact ⟨{
    support := lowerProfile n base.opened.bound base.opened.support
    footprint := base.opened.typeFootprint
    certificate := base.opened.requestedCertificate
    resources := base.opened.typeAvailable
    typed := typed
    typeCode := code
    witnessed := witnessed
    insertion := insertion
    related := related.retag henv (Profile.rename_hasType_iff.mpr typed)
      (code.future henv insertion.toFuture) }⟩

end Lean4Lean.AnchoredSource.Adapted
