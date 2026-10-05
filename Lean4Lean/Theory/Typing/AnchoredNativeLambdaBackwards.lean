import Lean4Lean.Theory.Typing.AnchoredNativeLambdaAlignment

/-! Pull an actual assigned-type certificate backward through the original
lambda conversions. This supplies the natural Pi certificate needed to read
its literal body row, while retaining the exact requested grade and profile. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

theorem OriginalLambdaTypePath.backward
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hle : sourceEnv ≤ env)
    {source target : List VExpr} {natural assigned : VExpr}
    (path : OriginalLambdaTypePath sourceEnv env U registry source natural assigned)
    (formation : GradedJoint env U registry source natural natural (.sort level))
    {locals : List Nat} {σ : Subst} {available : Valuation}
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (fits : PairedFits env U registry source target locals σ σ available)
    {support : Profile n} {footprint : Footprint}
    (certificate : CodeCert env U registry target locals σ assigned support footprint)
    (resources : footprint.Available available) :
    Nonempty (InitialNativeAlignment env U registry target locals σ available assigned natural support) := by
  induction path generalizing footprint with
  | refl =>
    obtain ⟨base⟩ := certificate.transfer_graded henv hscoped hTarget closed
      (formation target locals σ σ available closed hTarget substitutions fits).1 resources
    exact ⟨⟨base.footprint, base.certificate, base.available, .refl, base.related⟩⟩
  | tail _ conversion joint ih =>
    obtain ⟨next⟩ := certificate.transfer_graded henv hscoped hTarget closed
      (joint target locals σ σ available closed hTarget substitutions fits).2.1 resources
    obtain ⟨previous⟩ := ih next.certificate next.available
    have raw := (conversion.defeq.mono hle).substDF henv substitutions.wf hTarget substitutions
    exact ⟨{
      footprint := previous.footprint
      naturalCertificate := previous.naturalCertificate
      resources := previous.resources
      path := previous.path.trans (.single raw)
      related := previous.related.trans henv
        (next.related.symm henv certificate.formed.wf_value) }⟩

/-- Only original conversion and natural-Pi formation children are used.
The caller supplies its actual assigned code, not a natural-domain equality. -/
theorem OriginalLambdaOrigin.assignedCertificate
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hle : sourceEnv ≤ env)
    {source target : List VExpr} {A body assigned : VExpr}
    (origin : OriginalLambdaOrigin sourceEnv env U registry source A body assigned)
    {locals : List Nat} {σ : Subst} {available : Valuation}
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (fits : PairedFits env U registry source target locals σ σ available)
    {support : Profile n} {footprint : Footprint}
    (certificate : CodeCert env U registry target locals σ assigned support footprint)
    (resources : footprint.Available available) :
    Nonempty (InitialNativeAlignment env U registry target locals σ available assigned
      (.forallE A origin.bodyType) support) :=
  origin.conversions.backward henv hscoped hle origin.naturalJoint closed hTarget
    substitutions fits certificate resources

end Lean4Lean.AnchoredSource.Adapted
