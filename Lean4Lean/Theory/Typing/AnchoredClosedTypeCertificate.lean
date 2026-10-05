import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceGradedCode

/-! Closed source type certificates are interpreted through their original
header formation result and reused under arbitrary surrounding source locals. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

noncomputable def CodeCert.closedSource
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {target : List VExpr} {oldLocals : List Nat} {oldRealization : Subst}
    {expression : VExpr} {support : Profile n}
    (certificate : CodeCert env U registry target oldLocals oldRealization expression support [])
    (closed : expression.Closed) (locals : List Nat) (realization : Subst) :
    CodeCert env U registry target locals realization expression support [] := by
  have changed := certificate.realizePrefix closed realization (by intro i hi; omega)
  simpa only [lift'_refl, Footprint.sourceLift, List.map_nil] using
    changed.renameSource .refl realization rfl locals

/-- Only the original declaration-stage formation theorem interprets the
stored finite type certificate. An empty source context needs no fitting
entry or semantic assumption about a target variable. -/
theorem CodeCert.closedTypeCode
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {target : List VExpr} (hTarget : OnCtx target (env.IsType U))
    {locals : List Nat} {realization : Subst} {expression : VExpr} {support : Profile n}
    (closed : expression.Closed)
    (original : GradedJoint env U registry [] expression expression (.sort level))
    (certificate : CodeCert env U registry target locals realization expression support []) :
    TypeRelated env U registry target expression expression support := by
  have emptyClosed : Valuation.AtomClosed (fun _ => []) := by intro _ _ h; cases h
  have transfer : GradedTransfer env U registry target locals realization realization
      (fun _ => []) expression expression (.sort level) := (original target locals realization realization (fun _ => [])
    emptyClosed hTarget .nil .nil).1
  obtain ⟨result⟩ := certificate.transfer_graded henv hscoped hTarget emptyClosed transfer
    (by intro _ _ h; cases h)
  have realized : expression.subst realization = expression := closed.subst_eq (by intro i hi; omega)
  simpa only [realized] using result.related

end Lean4Lean.AnchoredSource.Adapted
