import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRecipeBodyExecution
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRecipeFocusSize

/-! Executable pending recipe contexts retain the original program. Intermediate
recipes need semantic resource realizations, not fabricated original caller Pi
nodes. Body admissions are computed by real canonical calls under one retained
donor; no returned certificate replaces the recursive input. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder EquationStratifiedFuel
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1800000

/-- Original syntax, plus the concrete admission needed to enter each native
body at its eventual right anchor. This is data computed from the input frame,
not a query interpreter or a desired-result callback. -/
inductive PreparedRecipeContext :
    {env : VEnv} → {U : Nat} → {registry : CanonicalHead.Registry} → {target : List VExpr} →
    {source : List VExpr} → {locals : List Nat} → {σ : Subst} → {expression : VExpr} →
    {relevant : Bool} → {n : Nat} → {profile : Profile n} → {footprint : Footprint} →
    RichCodeRecipe env U registry target source locals σ expression relevant profile footprint →
    Subst → Type where
  | root : PreparedRecipeContext
      (.root source locals σ owner node closed expressionEq realization certificate resources) τ
  | domain (parent : PreparedRecipeContext recipe τ) :
      PreparedRecipeContext (.domain recipe) τ
  | body {σ τ : Subst} {key : Key n} {result support : Profile n}
      {rows : List (Key n × Profile n)}
      {recipe : RichCodeRecipe env U registry target source locals σ.tail (.forallE A B)
        relevant (.pi prototypeDomain prototypeBody support rows) footprint}
      (parent : PreparedRecipeContext recipe τ.tail)
      (selected : (key, result) ∈ rows) (anchor : key.anchor = σ 0)
      (admitted : Admitted env U registry target key (τ 0) (τ 0)) :
      PreparedRecipeContext (.body recipe selected anchor) τ
  | fixedBody (parent : PreparedRecipeContext recipe τ) :
      PreparedRecipeContext (.fixedBody recipe selected admitted) τ
  | resources (parent : PreparedRecipeContext recipe τ) :
      PreparedRecipeContext (.resources recipe transfer) τ
  | action (parent : PreparedRecipeContext recipe τ) :
      PreparedRecipeContext (.action change recipe) τ

private theorem WorldCodeRecipeProvenance.prepareContext
    {strata : EquationStratification env}
    {recipe : RichCodeRecipe env U registry target source locals σ expression relevant profile footprint}
    (annotation : WorldCodeRecipeProvenance strata recipe)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (cutoff : Nat) (cutoffBound : cutoff ≤ strata.rules.length) (fuel : Nat → Nat)
    (constants callerSchedule : Nat)
    (calls : annotation.Calls
      (EquationControlMeasure.key strata.rules.length cutoff fuel constants callerSchedule))
    (bounded : WithinAbove cutoff fuel
      (fun control => recipe.stratifiedDepth (strata.headOrdinal registry) control))
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (resources : RecipeResourceRealization env U registry target source σ τ footprint) :
    Nonempty (PreparedRecipeContext recipe τ) := by
  match annotation with
  | .root .. => exact ⟨.root⟩
  | .domain child =>
    obtain ⟨previous⟩ := child.prepareContext henv hscoped formed cutoff cutoffBound fuel constants
      callerSchedule calls (by simpa only [RichCodeRecipe.stratifiedDepth, RichCodeRecipe.headDepth] using bounded) substitutions resources
    exact ⟨.domain previous⟩
  | .fixedBody child selected admitted =>
    obtain ⟨previous⟩ := child.prepareContext henv hscoped formed cutoff cutoffBound fuel constants
      callerSchedule calls (by simpa only [RichCodeRecipe.stratifiedDepth, RichCodeRecipe.headDepth] using bounded) substitutions resources
    exact ⟨.fixedBody previous⟩
  | .action change child =>
    obtain ⟨previous⟩ := child.prepareContext henv hscoped formed cutoff cutoffBound fuel constants
      callerSchedule calls (by simpa only [RichCodeRecipe.stratifiedDepth, RichCodeRecipe.headDepth] using bounded) substitutions resources
    exact ⟨.action previous⟩
  | .resources (transfer := actual) child transfer =>
    obtain ⟨previous⟩ := child.prepareContext henv hscoped formed cutoff cutoffBound fuel constants
      callerSchedule calls (by
        intro control active
        apply Nat.le_trans (Nat.le_max_left _ _)
        simpa only [RichCodeRecipe.stratifiedDepth, RichCodeRecipe.headDepth] using bounded control active)
      substitutions (RecipeResourceTransfer.realize henv hscoped formed actual resources)
    exact ⟨.resources previous⟩
  | @WorldCodeRecipeProvenance.body _ _ _ _ _ source locals A B relevant prototypeDomain prototypeBody
      n support rows footprint key result σ parent child selected anchor =>
    have previousResources : RecipeResourceRealization env U registry target source σ.tail τ.tail footprint := by
      intro index need member assigned lookup
      obtain ⟨value⟩ := resources (index + 1) need
        (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨(index, need), member, rfl⟩))
        assigned.lift (.succ lookup)
      exact ⟨by simpa only [lift_subst, Subst.tail] using value⟩
    have tailSubstitutions : Ctx.SubstEq env U target σ.tail τ.tail source := by
      cases substitutions with
      | cons tail _ _ => exact tail
    have parentBound : WithinAbove cutoff fuel
        (fun control => parent.stratifiedDepth (strata.headOrdinal registry) control) := by simpa only [RichCodeRecipe.stratifiedDepth, RichCodeRecipe.headDepth] using bounded
    obtain ⟨previous⟩ := child.prepareContext henv hscoped formed cutoff cutoffBound fuel constants
      callerSchedule calls parentBound tailSubstitutions previousResources
    obtain ⟨next, nextAnnotation, worlds, depth, whole⟩ := child.rebuildWorld
      henv hscoped formed cutoff cutoffBound fuel constants callerSchedule calls parentBound
      tailSubstitutions previousResources
    obtain ⟨argument⟩ := resources 0 _ List.mem_cons_self A.lift (.zero (Γ := source) (ty := A))
    have raw := substitutions.lookup (Lookup.zero (Γ := source) (ty := A))
    have paired : Related env U registry target (σ 0) (τ 0) (A.subst σ.tail)
        key.input argument.support := by simpa only [lift_subst] using argument.related
    rw [lift_subst] at raw
    have admitted := TypeRelated.literalPiRightAdmissionFromBinder henv hscoped formed
      (by simpa only [subst] using whole) selected anchor raw paired
    exact ⟨.body previous selected anchor admitted⟩
termination_by sizeOf annotation
decreasing_by all_goals simp_wf; omega

/-- The complete preparation pass uses only actual lower canonical F calls.
The donor is a genuine current original node; intermediate recipe expressions
are not assumed to be its original children. -/
theorem WorldCodeRecipeProvenance.prepareContextFromBank
    {strata : EquationStratification env} {P : VEnv → Prop}
    {recipe : RichCodeRecipe env U registry target source locals σ expression relevant profile footprint}
    (annotation : WorldCodeRecipeProvenance strata recipe)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (caller : EndpointState callerEnv U callerSource callerExpression callerAssigned)
    (controls : OriginalWorldControls strata callerEnv)
    (baseline : WorldEnvironmentProvenance strata U environment)
    (frontier : List (World strata.rules.length))
    (callerPaid : Sponsored frontier [originalCallWorld controls .fundamental caller baseline])
    (sources : annotation.Sources P) (sponsored : Sponsored frontier annotation.worlds)
    (bounded : WithinAbove controls.cutoff controls.fuel
      (fun control => recipe.stratifiedDepth (strata.headOrdinal registry) control))
    (bank : WorldBoundedUnaryCallBank env U registry strata P
      (frontier ++ [originalCallWorld controls .fundamental caller baseline]))
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (resources : RecipeResourceRealization env U registry target source σ τ footprint) :
    Nonempty (PreparedRecipeContext recipe τ) := by
  have calls := annotation.callsOfBank formed caller controls baseline frontier callerPaid sources sponsored bank
  exact annotation.prepareContext henv hscoped formed controls.cutoff controls.cutoffBound controls.fuel
    controls.ordered.constantCount
    (richSchedule .fundamental (Closure.close (caller.dependencyOrigin controls.ordered) environment).cost)
    calls bounded substitutions resources


private def bodyAdmissionGoal
    (recipe : RichCodeRecipe env U registry target source locals σ expression relevant profile footprint)
    (τ : Subst) : Prop :=
  match recipe with
  | .body (key := key) _ _ _ => Admitted env U registry target key (τ 0) (τ 0)
  | _ => True

private theorem PreparedRecipeContext.headAdmission
    (prepared : PreparedRecipeContext recipe τ) : bodyAdmissionGoal recipe τ := by
  cases prepared with
  | body parent selected anchor admitted => exact admitted
  | root | domain | fixedBody | resources | action => trivial

/-- The machine can use the prepared right anchor directly; the original
selected key and original parent program are unchanged. -/
theorem PreparedRecipeContext.bodyAdmission
    {σ τ : Subst} {key : Key n} {result support : Profile n}
    {rows : List (Key n × Profile n)}
    {recipe : RichCodeRecipe env U registry target source locals σ.tail (.forallE A B)
      relevant (.pi prototypeDomain prototypeBody support rows) footprint}
    {selected : (key, result) ∈ rows} {anchor : key.anchor = σ 0}
    (prepared : PreparedRecipeContext (.body (key := key) recipe selected anchor) τ) :
    Admitted env U registry target key (τ 0) (τ 0) := prepared.headAdmission

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
