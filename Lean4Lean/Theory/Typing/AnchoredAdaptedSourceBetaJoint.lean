import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceBetaExpansion
import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceGradedBetaForward

/-! Both directions of the original beta rule. Inverse substitution builds
the actual right-realized redex observation without changing its raw demand;
typed head-beta expansion transports the original instantiated-term evidence. -/

namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

theorem GradedTransferResult.betaExpand
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered)
    {source target : List VExpr} {locals : List Nat} {σ τ : Subst}
    {available : Valuation} {A B body argument : VExpr} {demand : Profile n}
    (originalArgument : GradedJoint env U registry source argument argument A)
    (rawBody : env.HasType U (A :: source) body B)
    (rawArgument : env.HasType U source argument A)
    (formedInstantiated : env.HasType U source (B.inst argument) (.sort bodyLevel))
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (fits : PairedFits env U registry source target locals σ τ available)
    (result : GradedTransferResult env U registry target locals σ τ available
      (body.inst argument) (body.inst argument) (B.inst argument) demand) :
    Nonempty (GradedTransferResult env U registry target locals σ τ available
      (body.inst argument) (.app (.lam A body) argument) (B.inst argument) demand) := by
  obtain ⟨footprint, ⟨observation⟩, resources⟩ := result.observation.betaExpand henv
    originalArgument rawArgument closed hTarget (substitutions.right henv hTarget)
    fits.right result.resultAvailable
  have beta := IsDefEq.beta rawBody rawArgument
  have typePair := formedInstantiated.substDF henv substitutions.wf hTarget substitutions
  have rightBeta := IsDefEq.defeqDF typePair.symm
    (beta.subst henv (substitutions.right henv hTarget) hTarget)
  have leftTyped := beta.hasType.2.subst henv substitutions.left hTarget
  have step : HeadBeta ((VExpr.app (.lam A body) argument).subst τ)
      ((body.inst argument).subst τ) := by
    simpa only [mkApps, List.foldl_cons, List.foldl_nil, subst, subst_inst] using
      (HeadBeta.contract (A := A.subst τ) (body := body.subst τ.lift)
        (argument := argument.subst τ) (trailing := []))
  exact ⟨{
    rank := result.rank
    bound := result.bound
    rawDemand := result.rawDemand
    resultFootprint := footprint
    observation := observation
    adapter := result.adapter
    resultAvailable := resources
    support := result.support
    typeFootprint := result.typeFootprint
    certificate := result.certificate
    typeAvailable := result.typeAvailable
    typed := result.typed
    rawTyped := result.rawTyped
    typeCode := result.typeCode
    related := Related.headBeta henv .refl step leftTyped rightBeta result.related
    rawRelated := Related.headBeta henv step step rightBeta rightBeta result.rawRelated }⟩

theorem GradedJoint.beta
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {source : List VExpr} {A B body argument : VExpr} {domainLevel bodyLevel : VLevel}
    (originalDomain : GradedJoint env U registry source A A (.sort domainLevel))
    (originalArgument : GradedJoint env U registry source argument argument A)
    (originalBody : GradedJoint env U registry (A :: source) body body B)
    (originalCodomain : GradedJoint env U registry (A :: source) B B (.sort bodyLevel))
    (originalInstantiated : GradedJoint env U registry source
      (body.inst argument) (body.inst argument) (B.inst argument))
    (formedA : env.HasType U source A (.sort domainLevel))
    (formedB : env.HasType U (A :: source) B (.sort bodyLevel))
    (rawBody : env.HasType U (A :: source) body B)
    (rawArgument : env.HasType U source argument A)
    (formedInstantiated : env.HasType U source (B.inst argument) (.sort bodyLevel)) :
    GradedJoint env U registry source (.app (.lam A body) argument)
      (body.inst argument) (B.inst argument) := by
  apply GradedJoint.of_transfers henv
  intro target locals σ τ available closed hTarget substitutions fits
  constructor
  · exact GradedTransfer.beta_forward henv hscoped originalDomain originalArgument
      originalBody originalCodomain originalInstantiated formedA formedB rawBody rawArgument
      closed hTarget substitutions fits
  · intro n demand footprint observation resources
    obtain ⟨result⟩ := (originalInstantiated target locals σ τ available closed hTarget
      substitutions fits).1 observation resources
    exact result.betaExpand henv originalArgument rawBody rawArgument formedInstantiated
      closed hTarget substitutions fits

end Lean4Lean.AnchoredSource.Adapted
