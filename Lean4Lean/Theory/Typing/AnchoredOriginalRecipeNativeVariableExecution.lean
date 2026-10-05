import Lean4Lean.Theory.Typing.AnchoredOriginalRecipeVariableBodyCompile

/-! A productive charged-body clause. The input is a real root containing a
native Pi and a retained legacy variable row. Its binder demand is computed
from that row, and executing the demand produces ordinary destination syntax.
This is not a claim that arbitrary rich variable bodies have already been
normalized. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

section
variable {strata : EquationStratification env} {σ realization : Subst}
    (owner : CanonicalCodeOwner env registry strata name)
    {domainNode : EndpointState owner.selected.origin.source U [] A (.sort u)}
    {bodyNode : EndpointState owner.selected.origin.source U [A] (.bvar 0) (.sort v)}
    {key : Key n} {ambient output packed : Profile n}
    (hu : u.WF U) (hv : v.WF U)
    (domain : RichCert owner.selected.origin.source env U registry target domainNode
      [] realization true ambient domainFootprint)
    (piGuard : PiGuard env U target realization A (.bvar 0) prototypeDomain prototypeBody)
    (rowGuard : LambdaGuard env U registry target realization A key ambient)
    (body : SortableCert env U registry target (Locals.push []) (realization.cons key.anchor)
      (.bvar 0) relevant output bodyFootprint)
    (pack : BinderPack n packed bodyFootprint outside)
    (covered : packed.atoms ⊆ key.input.atoms)
    (tail : RichRows owner.selected.origin.source env U registry target domainNode bodyNode
      [] realization relevant ambient rest tailFootprint)
    (resources : (domainFootprint ++ (outside ++ tailFootprint)).Available (fun _ => []))
    (closed : (VExpr.forallE A (.bvar 0)).Closed)
    (expressionEq : EqUpToLevels U (.forallE A (.bvar 0)) (.forallE declaredDomain (.bvar 0)))

/-- The exact shared charged query whose next program is the stored row. -/
noncomputable def RichCodeRecipe.nativeVariableBody (source : List VExpr) (locals : List Nat) (σ : Subst) :
    RichCodeRecipe env U registry target (declaredDomain :: source) (Locals.push locals)
      (σ.cons key.anchor) (.bvar 0) relevant output [(0, ⟨n, key.input⟩)] :=
  by
    let root : RichCodeRecipe env U registry target source locals σ
        (.forallE declaredDomain (.bvar 0)) relevant
        (Profile.pi prototypeDomain prototypeBody ambient ((key, output) :: rest)) [] :=
      .root source locals σ owner (.pi hu hv domainNode bodyNode) closed expressionEq realization
        (.pi hu hv domain piGuard (.cons rowGuard (.legacy body) pack covered tail)) resources
    exact RichCodeRecipe.body (σ := σ.cons key.anchor) root List.mem_cons_self rfl

include body pack covered resources in
/-- Compute the actual argument demand for that selected row. The only
resource facts used are the root's own supplied empty-table footprint and
its retained binder pack. -/
theorem RichCodeRecipe.nativeVariableBodyDemand
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (formed : OnCtx target (env.IsType U)) :
    Nonempty (RecipeVariableDemand env U registry target key.input output) := by
  exact SortableCert.recipeVariableDemand henv hscoped formed body pack covered
    (fun index need member => resources index need
      (List.mem_append_right _ (List.mem_append_left _ member)))

include body pack covered resources in
/-- Execute the computed demand on an actual independent destination
argument. No source expression/capture factorization is stored in the returned
certificate, which remains usable with that destination's ordinary resources. -/
theorem RichCodeRecipe.executeNativeVariableBody
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (formed : OnCtx target (env.IsType U)) :
    ∃ demand : RecipeVariableDemand env U registry target key.input output,
      ∀ {argumentEnv : VEnv} {argumentSource : List VExpr} {argumentExpression argumentType : VExpr}
        {argumentNode : EndpointState argumentEnv U argumentSource argumentExpression argumentType}
        {argumentLocals : List Nat} {argumentσ : Subst} {argumentAvailable : Valuation},
      (argument : RichGradedResult argumentEnv env U registry target argumentNode
        argumentLocals argumentσ argumentAvailable demand.input) →
      ∃ footprint, ∃ certificate : RichCert argumentEnv env U registry target argumentNode
        argumentLocals argumentσ relevant output footprint,
        footprint.Available argumentAvailable ∧
        ∀ policy, certificate.headDepth policy ≤ argument.observation.headDepth policy := by
  obtain ⟨demand⟩ := SortableCert.recipeVariableDemand henv hscoped formed body pack covered
    (fun index need member => resources index need
      (List.mem_append_right _ (List.mem_append_left _ member)))
  refine ⟨demand, ?_⟩
  intro argumentEnv argumentSource argumentExpression argumentType argumentNode argumentLocals argumentσ argumentAvailable argument
  exact demand.compile henv hscoped formed body.formed argument
end

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
