import Lean4Lean.Theory.Typing.AnchoredBoundedCode

/-! Conversion transports the actual source type certificate through the
original type-equality child. Computational observations and their finite
grades remain unchanged. -/
namespace Lean4Lean.AnchoredSource.Adapted.Staged
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

theorem Joint.of_transfers
    {current : Name → Bool} {fuel : Nat}
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) {source : List VExpr} {left right sourceType : VExpr}
    (original : ∀ target locals σ τ available,
      available.AtomClosed → OnCtx target (env.IsType U) →
      Ctx.SubstEq env U target σ τ source →
      PairedFits current fuel env U registry source target locals σ τ available →
        Transfer current fuel env U registry target locals σ τ available left right sourceType ∧
        Transfer current fuel env U registry target locals σ τ available right left sourceType) :
    Joint current fuel env U registry source left right sourceType := by
  intro target locals σ τ available closed hTarget substitutions fits
  obtain ⟨forward, backward⟩ := original target locals σ τ available closed hTarget substitutions fits
  exact ⟨forward, backward, forward.sortCorrect henv hTarget, backward.sortCorrect henv hTarget⟩

theorem Joint.symm
    (joint : Joint current fuel env U registry source left right type) :
    Joint current fuel env U registry source right left type := by
  intro target locals σ τ available closed hTarget substitutions fits
  have result := joint target locals σ τ available closed hTarget substitutions fits
  exact ⟨result.2.1, result.1, result.2.2.2, result.2.2.1⟩

theorem Joint.left {left right type : VExpr} (henv : env.Ordered) (hscoped : registry.Scoped)
    (joint : Joint current fuel env U registry source left right type) :
    Joint current fuel env U registry source left left type :=
  joint.trans henv hscoped joint.symm

theorem Joint.right {left right type : VExpr} (henv : env.Ordered) (hscoped : registry.Scoped)
    (joint : Joint current fuel env U registry source left right type) :
    Joint current fuel env U registry source right right type :=
  joint.symm.trans henv hscoped joint

theorem Transfer.convert
    {current : Name → Bool} {fuel : Nat}
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {source target : List VExpr} {locals : List Nat} {σ τ : Subst}
    {available : Valuation} {left right A B : VExpr}
    (originalType : Joint current fuel env U registry source A B (.sort level))
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (fits : PairedFits current fuel env U registry source target locals σ τ available)
    (originalTerm : Transfer current fuel env U registry target locals σ τ available left right A) :
    Transfer current fuel env U registry target locals σ τ available left right B := by
  intro n demand footprint observation bound resources
  obtain ⟨value⟩ := originalTerm observation bound resources
  have producer : Transfer current fuel env U registry target locals σ σ available A B (.sort level) :=
    (originalType target locals σ σ available closed hTarget substitutions.left fits.left).1
  obtain ⟨type⟩ := producer.codeCertificate henv hscoped hTarget closed value.certificate value.certificateBound value.typeAvailable
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
    related := Related.convert henv value.typed type.related value.related
    observationBound := value.observationBound
    certificateBound := type.certificateBound }⟩

theorem Joint.convert
    {current : Name → Bool} {fuel : Nat}
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {source : List VExpr} {left right A B : VExpr}
    (originalType : Joint current fuel env U registry source A B (.sort level))
    (originalTerm : Joint current fuel env U registry source left right A) :
    Joint current fuel env U registry source left right B := by
  apply Joint.of_transfers henv
  intro target locals σ τ available closed hTarget substitutions fits
  have term := originalTerm target locals σ τ available closed hTarget substitutions fits
  exact ⟨Transfer.convert henv hscoped originalType closed hTarget substitutions fits term.1,
    Transfer.convert henv hscoped originalType closed hTarget substitutions fits term.2.1⟩

end Lean4Lean.AnchoredSource.Adapted.Staged
