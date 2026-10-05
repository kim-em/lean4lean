import Lean4Lean.Theory.Typing.AnchoredOriginalRecipeVariableNeedExecution
import Lean4Lean.Theory.Typing.AnchoredOriginalRecipeNativeVariableExecution

/-! A changed-anchor charged body is compiled from its retained row program.
The row itself is not reanchored by F. Its variable adapter is independent of
the old anchor; the new caller supplies the SAME key input at its own variable.
This is a concrete pending-action case, not a semantic Pi inversion. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1200000

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


/-- An actual `map(reanchor)` between the root and the body elimination. Its
footprint is exactly the new variable's Need, including empty input profiles. -/
noncomputable def RichCodeRecipe.reanchoredNativeVariableBody
    (admitted : Admitted env U registry target key newAnchor newAnchor)
    (source : List VExpr) (locals : List Nat) (σ : Subst) :
    RichCodeRecipe env U registry target (declaredDomain :: source) (Locals.push locals)
      (σ.cons newAnchor) (.bvar 0) relevant output [(0, ⟨n, key.input⟩)] := by
  let root : RichCodeRecipe env U registry target source locals σ
      (.forallE declaredDomain (.bvar 0)) relevant
      (Profile.pi prototypeDomain prototypeBody ambient ((key, output) :: rest)) [] :=
    .root source locals σ owner (.pi hu hv domainNode bodyNode) closed expressionEq realization
      (.pi hu hv domain piGuard (.cons rowGuard (.legacy body) pack covered tail)) resources
  let unused : Atom n := match n with | 0 => true | _ + 1 => .sort true
  let change : AtomView env U registry target (n := n + 1)
      (.fn key unused) (.fn (reanchorKey key newAnchor) unused) := .reanchor admitted
  let widened : RichCodeRecipe env U registry target source locals σ
      (.forallE declaredDomain (.bvar 0)) relevant
      (Profile.pi prototypeDomain prototypeBody ambient
        (reanchorRows key (reanchorKey key newAnchor) ((key, output) :: rest))) [] :=
    .action (.map change) root
  exact .body (σ := σ.cons newAnchor) (key := reanchorKey key newAnchor) widened
    (reanchorRows.changed (newKey := reanchorKey key newAnchor) List.mem_cons_self) rfl

include body pack covered resources in
/-- Execute the retained original body at a genuinely different caller
anchor. The result uses ordinary destination variable syntax and contains no
foreign sites. The only local requirement is the exact footprint of the
reanchored recipe above; no actual argument F result is assumed. -/
theorem RichCodeRecipe.executeReanchoredNativeVariableBody
    {callerStrata : EquationStratification env}
    {node : EndpointState sourceEnv U (declaredDomain :: source) (.bvar 0) assigned}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (formed : OnCtx target (env.IsType U))
    (exposed : Footprint.Available [(0, ⟨n, key.input⟩)] available)
    (controls : OriginalWorldControls callerStrata controlSource)
    (frontier : List (EquationWorldClosureOrder.World callerStrata.rules.length)) :
    ∃ footprint, ∃ certificate : RichCert sourceEnv env U registry target node
      (Locals.push locals) (σ.cons newAnchor) relevant output footprint,
    ∃ ready : ControlledStoredQuery controls frontier (.certificate certificate),
      footprint.Available available ∧ ready.annotation.worlds = [] ∧
      ∀ policy, certificate.headDepth policy = 0 := by
  obtain ⟨demand⟩ := SortableCert.recipeVariableDemand henv hscoped formed body pack covered
    (fun index need member => resources index need
      (List.mem_append_right _ (List.mem_append_left _ member)))
  exact demand.executeNeed henv hscoped formed body.formed
    (exposed 0 _ List.mem_cons_self) controls frontier
end

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
