import Lean4Lean.Theory.Typing.AnchoredOriginalProjectionSortableSyntax

/-! A charged recipe is an actual closed input program and a finite pending
elimination context. Focusing does not manufacture a requested body recipe:
the next program is the stored input certificate, strictly below the complete
recipe syntax. The context retains resource transfers and level alignment. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1200000

structure RichRecipeRootInput (env : VEnv) (U : Nat)
    (registry : CanonicalHead.Registry) (target : List VExpr) where
  strata : EquationStratification env
  name : Name
  owner : CanonicalCodeOwner env registry strata name
  expression : VExpr
  canonicalExpression : VExpr
  level : VLevel
  node : EndpointState owner.selected.origin.source U [] canonicalExpression (.sort level)
  closed : canonicalExpression.Closed
  expressionEq : EqUpToLevels U canonicalExpression expression
  source : List VExpr
  locals : List Nat
  substitution : Subst
  realization : Subst
  relevant : Bool
  rank : Nat
  profile : Profile rank
  footprint : Footprint
  certificate : RichCert owner.selected.origin.source env U registry target node
    [] realization relevant profile footprint
  resources : footprint.Available (fun _ => [])

def RichRecipeRootInput.recipe (input : RichRecipeRootInput env U registry target) :
    RichCodeRecipe env U registry target input.source input.locals input.substitution
      input.expression input.relevant input.profile [] :=
  .root input.source input.locals input.substitution input.owner input.node input.closed
    input.expressionEq input.realization input.certificate input.resources

/-- Typed pending operations, indexed by the exact original recipe. The
identity case starts at the actual retained root, not an interpreted answer. -/
inductive RichRecipeContext {env : VEnv} {U : Nat}
    {registry : CanonicalHead.Registry} {target : List VExpr}
    (input : RichRecipeRootInput env U registry target) :
    {source : List VExpr} → {locals : List Nat} → {σ : Subst} →
    {expression : VExpr} → {relevant : Bool} → {n : Nat} →
    {profile : Profile n} → {footprint : Footprint} →
    RichCodeRecipe env U registry target source locals σ expression relevant profile footprint → Type where
  | root : RichRecipeContext input input.recipe
  | domain (pending : RichRecipeContext input parent) :
      RichRecipeContext input (.domain parent)
  | body {σ : Subst} {n : Nat} {support result : Profile n} {key : Key n}
      {rows : List (Key n × Profile n)}
      {parent : RichCodeRecipe env U registry target source locals σ.tail (.forallE A B)
        relevant (.pi prototypeDomain prototypeBody support rows) footprint}
      (pending : RichRecipeContext input parent)
      (selected : (key, result) ∈ rows) (anchor : key.anchor = σ 0) :
      RichRecipeContext input (.body parent selected anchor)
  | fixedBody {A B : VExpr} {n : Nat} {support result : Profile n} {key : Key n}
      {rows : List (Key n × Profile n)}
      {parent : RichCodeRecipe env U registry target source locals σ (.forallE A B.lift)
        relevant (.pi prototypeDomain prototypeBody support rows) footprint}
      (pending : RichRecipeContext input parent)
      (selected : (key, result) ∈ rows)
      (admitted : Admitted env U registry target key anchor anchor) :
      RichRecipeContext input (.fixedBody parent selected admitted)
  | resources (pending : RichRecipeContext input parent) (transfer) :
      RichRecipeContext input (.resources parent transfer)
  | action (pending : RichRecipeContext input parent) (change) :
      RichRecipeContext input (.action change parent)

/-- Exhaustive focusing through every shared recipe constructor. No semantic
Pi decomposition or result query is assumed; the next certificate is the
literal child stored by the root. -/
theorem RichCodeRecipe.focusInput
    (recipe : RichCodeRecipe env U registry target source locals σ expression relevant profile footprint) :
    ∃ input : RichRecipeRootInput env U registry target,
      Nonempty (RichRecipeContext input recipe) ∧ sizeOf input.certificate < sizeOf recipe := by
  match recipe with
  | .root source locals σ owner node closed expressionEq realization certificate supplied =>
    refine ⟨⟨_, _, owner, _, _, _, node, closed, expressionEq, source, locals, σ,
      realization, _, _, _, _, certificate, supplied⟩, ⟨.root⟩, ?_⟩
    simp_wf
    omega
  | .domain parent =>
    obtain ⟨input, ⟨pending⟩, smaller⟩ := parent.focusInput
    refine ⟨input, ⟨.domain pending⟩, Nat.lt_trans smaller ?_⟩
    simp_wf
    omega
  | .body parent selected anchor =>
    obtain ⟨input, ⟨pending⟩, smaller⟩ := parent.focusInput
    refine ⟨input, ⟨.body pending selected anchor⟩, Nat.lt_trans smaller ?_⟩
    simp_wf
    omega
  | .fixedBody parent selected admitted =>
    obtain ⟨input, ⟨pending⟩, smaller⟩ := parent.focusInput
    refine ⟨input, ⟨.fixedBody pending selected admitted⟩, Nat.lt_trans smaller ?_⟩
    simp_wf
    omega
  | .resources parent transfer =>
    obtain ⟨input, ⟨pending⟩, smaller⟩ := parent.focusInput
    refine ⟨input, ⟨.resources pending transfer⟩, Nat.lt_trans smaller ?_⟩
    simp_wf
    omega
  | .action change parent =>
    obtain ⟨input, ⟨pending⟩, smaller⟩ := parent.focusInput
    refine ⟨input, ⟨.action pending change⟩, Nat.lt_trans smaller ?_⟩
    simp_wf
    omega
termination_by sizeOf recipe
decreasing_by all_goals simp_wf; omega

/-- Every pending Pi elimination starts at a literal Pi root. Actions and
resource transfers preserve the expression; no semantic shape inversion is
used to identify the retained canonical program. -/
theorem RichRecipeContext.rootIsPi
    {input : RichRecipeRootInput env U registry target}
    {recipe : RichCodeRecipe env U registry target source locals σ expression relevant profile footprint}
    (pending : RichRecipeContext input recipe)
    (shape : ∃ A B, expression = VExpr.forallE A B) :
    ∃ A B, input.expression = VExpr.forallE A B := by
  induction pending with
  | root => exact shape
  | domain pending ih => exact ih ⟨_, _, rfl⟩
  | body pending selected anchor ih => exact ih ⟨_, _, rfl⟩
  | fixedBody pending selected admitted ih => exact ih ⟨_, _, rfl⟩
  | resources pending transfer ih => exact ih shape
  | action pending change ih => exact ih shape

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
