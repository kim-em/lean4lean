import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceGradedCode
import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceGradedSort

/-! Conversion transports the actual source type certificate through the
original type-equality child. Computational observations and their finite
grades remain unchanged. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

theorem GradedTransfer.convert
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {source target : List VExpr} {locals : List Nat} {σ τ : Subst}
    {available : Valuation} {left right A B : VExpr}
    (originalType : GradedJoint env U registry source A B (.sort level))
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (fits : PairedFits env U registry source target locals σ τ available)
    (originalTerm : GradedTransfer env U registry target locals σ τ available left right A) :
    GradedTransfer env U registry target locals σ τ available left right B := by
  intro n demand footprint observation resources
  obtain ⟨value⟩ := originalTerm observation resources
  have producer : GradedTransfer env U registry target locals σ σ available A B (.sort level) :=
    (originalType target locals σ σ available closed hTarget substitutions.left fits.left).1
  obtain ⟨type⟩ := value.certificate.transfer_graded henv hscoped hTarget closed producer value.typeAvailable
  exact ⟨{
    rank := value.rank
    bound := value.bound
    rawDemand := value.rawDemand
    adapter := value.adapter
    resultFootprint := value.resultFootprint
    observation := value.observation
    resultAvailable := value.resultAvailable
    support := value.support
    typeFootprint := type.footprint
    certificate := type.certificate
    typeAvailable := type.available
    typed := value.typed
    rawTyped := value.rawTyped
    typeCode := TypeRelated.left_diagonal (TypeRelated.symm henv value.typed.wf_type type.related)
    rawRelated := Related.convert henv value.rawTyped type.related value.rawRelated
    related := Related.convert henv value.typed type.related value.related }⟩

theorem GradedJoint.convert
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {source : List VExpr} {left right A B : VExpr}
    (originalType : GradedJoint env U registry source A B (.sort level))
    (originalTerm : GradedJoint env U registry source left right A) :
    GradedJoint env U registry source left right B := by
  apply GradedJoint.of_transfers henv
  intro target locals σ τ available closed hTarget substitutions fits
  have term := originalTerm target locals σ τ available closed hTarget substitutions fits
  exact ⟨GradedTransfer.convert henv hscoped originalType closed hTarget substitutions fits term.1,
    GradedTransfer.convert henv hscoped originalType closed hTarget substitutions fits term.2.1⟩

end Lean4Lean.AnchoredSource.Adapted
