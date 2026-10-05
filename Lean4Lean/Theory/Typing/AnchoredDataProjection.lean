import Lean4Lean.Theory.Typing.AnchoredExposureCanonicalProjection
import Lean4Lean.Theory.Typing.AnchoredDataRelations
import Lean4Lean.Theory.Inductive.SaturatedNativeSubstitution

/-! Raw data displays and projection origins follow the actual canonical
readback of their proof insertion history. -/
namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv InductiveSignature.NativeRecursorData
set_option backward.isDefEq.respectTransparency false

theorem ConstructorExposure.projectCanonical
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {Γ Δ Ω : List VExpr} {ρ : Lift} {expression type head : VExpr} {σ : Subst}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (hΓ : OnCtx Γ (env.IsType U)) (typed : Ctx.SubstEq env U Γ σ σ Δ)
    (E : ConstructorExposure env U registry Δ expression type Ω ρ head) :
    Nonempty (ConstructorExposure env U registry Γ (expression.subst σ) (type.subst σ)
      (replayContext Γ Ω ρ σ) (.skipN .refl (proofCount ρ))
      (head.subst (proofReadback ρ σ))) := by
  have total : ProofInsertion env U Δ E.postContext ρ := by
    simpa only [E.map_eq] using E.generated.comp E.post henv
  obtain ⟨frame, readback, _⟩ := total.mapSubstitution_exact henv hΓ typed
  have changed := E.terminal.replayContext henv total hΓ typed
  obtain ⟨front, _⟩ := E.generated.substFront henv hΓ typed E.added
  have post := ProofInsertion.mapSubstitutionWithPrefix henv hΓ typed E.added E.generated E.post
  rw [E.map_eq] at post
  have sound := ((E.terminal.symm henv).eq henv E.sound).subst henv
    readback (frame.targetWF henv)
  rw [proofReadback_commute] at sound
  refine ⟨{
    added := substAdded σ E.added
    result := E.result.subst (σ.liftN E.added.length)
    postMap := proofFrontMap E.added.length E.postMap
    trace := E.trace.subst hscoped σ
    generated := by simpa only [substAdded_length] using front
    postContext := replayContext Γ E.postContext ρ σ
    post := post
    terminal := changed
    map_eq := ?_
    result_eq := ?_
    sound := by simpa only [proofReadback_commute] using changed.eq henv sound }⟩
  · rw [substAdded_length, proofFrontMap_base]
    have counts := congrArg VEnv.proofCount E.map_eq
    simp only [VEnv.proofCount, Lift.depth_comp, Lift.depth_skipN, Lift.depth, Nat.zero_add] at counts
    exact congrArg (Lift.skipN .refl) counts
  · have result := proofReadback_front E.added.length E.postMap σ E.result
    rw [E.map_eq, E.result_eq] at result
    exact result.symm


namespace RankedData
private theorem head_subst (name : Name) (levels : List VLevel) (arguments : List VExpr) (σ : Subst) :
    (mkApps (.const name levels) arguments).subst σ =
      mkApps (.const name levels) (arguments.map (·.subst σ)) := by
  suffices ∀ head, (mkApps head arguments).subst σ =
      mkApps (head.subst σ) (arguments.map (·.subst σ)) from this _
  induction arguments with
  | nil => intro head; rfl
  | cons arg rest ih => intro head; exact ih (.app head arg)

def ProjectionOrigin.substitute {name : Name}
    (henv : env.Ordered) (hΓ : OnCtx Γ (env.IsType U))
    (typed : Ctx.SubstEq env U Γ σ σ Δ)
    (origin : ProjectionOrigin env U Δ info name index major assignedType domain) :
    ProjectionOrigin env U Γ info name index (major.subst σ)
      (assignedType.subst σ) (domain.subst σ) :=
  { origin with
    params := origin.params.map (·.subst σ)
    paramCount := by simpa only [List.length_map] using origin.paramCount
    indexArgs := origin.indexArgs.map (·.subst σ)
    indexCount := by simpa only [List.length_map] using origin.indexCount
    sourceMajor := origin.sourceMajor.subst σ
    fieldType := origin.fieldType.subst σ
    selected := info.fieldType_subst_some origin.ctorClosed origin.selected
    formation := origin.formation.subst henv typed hΓ
    familyPath := by simpa only [head_subst, List.map_append] using origin.familyPath.substTarget henv hΓ typed
    majorEq := by simpa only [head_subst, List.map_append] using origin.majorEq.subst henv typed hΓ
    fieldPath := origin.fieldPath.substTarget henv hΓ typed }
end RankedData

namespace ConstructorResultHeader
variable {levels : List VLevel}

def substitute (header : ConstructorResultHeader env constructor family levels arguments) (σ : Subst) :
    ConstructorResultHeader env constructor family levels (arguments.map (·.subst σ)) :=
  { header with saturated := by simpa only [List.length_map] using header.saturated }

theorem result_substitute (henv : env.Ordered)
    (header : ConstructorResultHeader env constructor family levels arguments) (σ : Subst) :
    (header.substitute σ).result = header.result.subst σ := by
  exact (instantiateParams_subst_scoped (header.resultScoped henv) σ).symm

end ConstructorResultHeader
end Lean4Lean.AnchoredSemantics
