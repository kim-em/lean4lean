import Lean4Lean.Theory.Typing.AnchoredOriginalFactorTraversal
import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceGradedFundamental
import Lean4Lean.Theory.Typing.AnchoredConversion

/-! Reindex a current-syntax whole cut before reflecting its source prefix.
The two semantic answers are finite results at the original cut and at its
exact returned support. The cut's assigned type may depend on the removed
binders. Only the destination argument type is a displayed source weakening.

This uses the current type-unindexed Obs/CodeCert reflection theorem. It
does not assert reflection for a future syntax containing source derivations
or additional metadata, nor produce the original coherence answer itself.
-/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalFactorCut
open VExpr VEnv AnchoredProfiles AnchoredSemantics
open OriginalClosureMeasure OriginalEndpointFactor
set_option backward.isDefEq.respectTransparency false

private theorem reflected_available
    {before after : Footprint} {full base : Valuation}
    (resources : before.Available full)
    (same : before = after.sourceLift (.skipN .refl depth))
    (tail : ∀ index, full (index + depth) = base index) :
    after.Available base := by
  intro index need member
  rw [← tail index]
  apply resources (index + depth) need
  rw [same]
  exact List.mem_map.mpr ⟨(index, need), member,
    by simp only [Lift.liftVar_skipN, Lift.liftVar]⟩

/-- Keep the finite observation produced at the original cut. Transfer its
actual returned type support to the displayed original argument type, then
reflect both the observation and that new certificate to the source tail.
No source typing or reflection assumption is made for `origin.type`. -/
theorem WholeCutQuery.reindexReflect
    {sourceEnv env : VEnv} {U : Nat}
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {argument : VExpr} {baseDepth : Nat} {boundary : List VExpr}
    {origin : OriginalEndpointFactor.CutOriginAt root boundary argument baseDepth}
    {registry : CanonicalHead.Registry} {target : List VExpr} {σ : Subst}
    {demand : Profile n} {originalFootprint : Footprint}
    (whole : WholeCutQuery (env := env) origin registry target σ demand originalFootprint)
    (henv : env.Ordered)
    {fullAvailable available : Valuation}
    (availableTail : ∀ index, fullAvailable (index + origin.depth) = available index)
    (baseLocals : List Nat)
    (value : GradedTransferResult env U registry target whole.locals
      whole.realization whole.realization fullAvailable
      origin.expression origin.expression origin.type demand)
    {argumentType : VExpr}
    (types : CodeTransferResult env U registry target whole.locals
      whole.realization whole.realization fullAvailable origin.type
      (argumentType.lift' (.skipN .refl origin.depth)) value.support) :
    Nonempty (GradedTransferResult env U registry target baseLocals σ σ available
      argument argument argumentType demand) := by
  obtain ⟨resultFootprint, ⟨observation⟩, resultEq⟩ :=
    value.observation.reflectSource (.skipN .refl origin.depth) origin.expression_eq baseLocals
  obtain ⟨typeFootprint, ⟨certificate⟩, typeEq⟩ :=
    types.certificate.reflectSource (.skipN .refl origin.depth) rfl baseLocals
  rw [whole.tail_eq] at observation certificate
  have bridge : TypeRelated env U registry target (origin.type.subst whole.realization)
      (argumentType.subst σ) value.support := by
    simpa only [subst_lift', whole.tail_eq] using types.related
  have related := Related.convert henv value.typed bridge value.related
  have rawRelated := Related.convert henv value.rawTyped bridge value.rawRelated
  exact ⟨{
    rank := value.rank
    bound := value.bound
    rawDemand := value.rawDemand
    resultFootprint := resultFootprint
    observation := observation
    adapter := value.adapter
    resultAvailable := reflected_available value.resultAvailable resultEq availableTail
    support := value.support
    typeFootprint := typeFootprint
    certificate := certificate
    typeAvailable := reflected_available types.available typeEq availableTail
    typed := value.typed
    rawTyped := value.rawTyped
    typeCode := (bridge.symm henv value.typed.wf_type).left_diagonal
    related := by simpa only [whole.realized] using related
    rawRelated := by simpa only [whole.realized] using rawRelated }⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalFactorCut
