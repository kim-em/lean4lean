import Lean4Lean.Theory.Typing.AnchoredLevels
import Lean4Lean.Theory.Typing.AnchoredOriginalRecipeResourceSemantics
import Lean4Lean.Theory.Typing.AnchoredRecipePiSemantics
import Lean4Lean.Theory.Typing.AnchoredOriginalRichVariableValue
import Lean4Lean.Theory.Typing.AnchoredOriginalPiDomainRequest
import Lean4Lean.Theory.Typing.AnchoredNativeSeededRegistered
import Lean4Lean.Theory.Typing.ProjectionLevelCongruence
import Lean4Lean.Theory.Typing.EquationStratifiedFuel

/-! Interpret the shared charged recipe on the current paired realization.
Only its actual canonical original root calls the lower fundamental clause;
all subsequent Pi elimination, resource transfer and right reconstruction are
finite operations on the same stored syntax and realized binder resources. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor EquationStratifiedFuel
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1200000

noncomputable def recipeRootSchedule
    (owner : CanonicalCodeOwner env registry strata name)
    (node : EndpointState owner.selected.origin.source U [] expression (.sort level)) : Nat :=
  richSchedule .fundamental
    (Closure.close (node.dependencyOrigin owner.selected.origin.ordered) []).cost

/-- The only supplied induction clause is F at the exact retained original
formation, guarded by its computed canonical source and well-founded key. -/
def RecipeRootCall
    (owner : CanonicalCodeOwner env registry strata name)
    (node : EndpointState owner.selected.origin.source U [] expression (.sort level))
    (certificate : RichCert owner.selected.origin.source env U registry target node
      [] realization relevant profile footprint)
    (parentKey : EquationControlMeasure.Key strata.rules.length) : Prop :=
  ∀ fuel : Nat → Nat,
    WithinAbove (owner.selected.ordinal - 1) fuel
      (fun control => certificate.stratifiedDepth (strata.headOrdinal registry) control) →
    strata.SourceCutoff owner.selected.origin.source (owner.selected.ordinal - 1) →
    EquationControlMeasure.Less
      (EquationControlMeasure.key strata.rules.length (owner.selected.ordinal - 1) fuel
        owner.selected.origin.ordered.constantCount (recipeRootSchedule owner node)) parentKey →
    Nonempty (RichSupportedValue owner.selected.origin.source env U registry target
      node [] realization realization (fun _ => []) profile)

/-- These are exact original call guards along the finite recipe. A root is
indexed by the operative strata, so an unrelated retained equation ordering
cannot be substituted at opening. -/
inductive RichRecipeCalls {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {target : List VExpr} (strata : EquationStratification env)
    (parentKey : EquationControlMeasure.Key strata.rules.length) :
    {source : List VExpr} → {locals : List Nat} → {σ : Subst} →
    {expression : VExpr} → {relevant : Bool} → {n : Nat} →
    {profile : Profile n} → {footprint : Footprint} →
    RichCodeRecipe env U registry target source locals σ expression relevant profile footprint → Prop where
  | root (owner : CanonicalCodeOwner env registry strata name)
      (node : EndpointState owner.selected.origin.source U [] canonicalExpression (.sort level))
      (closed : canonicalExpression.Closed)
      (expressionEq : EqUpToLevels U canonicalExpression expression)
      (certificate : RichCert owner.selected.origin.source env U registry target node
        [] realization relevant profile footprint)
      (resources : footprint.Available (fun _ => []))
      (lower : RecipeRootCall owner node certificate parentKey) :
      RichRecipeCalls strata parentKey (.root source locals σ owner node closed expressionEq
        realization certificate resources)
  | domain (calls : RichRecipeCalls strata parentKey parent) :
      RichRecipeCalls strata parentKey (.domain parent)
  | body {σ : Subst} {n : Nat} {support result : Profile n} {key : Key n}
      {rows : List (Key n × Profile n)}
      {parent : RichCodeRecipe env U registry target source locals σ.tail (.forallE A B)
        relevant (.pi prototypeDomain prototypeBody support rows) footprint}
      (calls : RichRecipeCalls strata parentKey parent)
      (selected : (key, result) ∈ rows) (anchor : key.anchor = σ 0) :
      RichRecipeCalls strata parentKey (.body parent selected anchor)
  | fixedBody {A B : VExpr} {n : Nat} {support result : Profile n} {key : Key n}
      {rows : List (Key n × Profile n)}
      {parent : RichCodeRecipe env U registry target source locals σ (.forallE A B.lift)
        relevant (.pi prototypeDomain prototypeBody support rows) footprint}
      (calls : RichRecipeCalls strata parentKey parent)
      (selected : (key, result) ∈ rows)
      (admitted : Admitted env U registry target key anchor anchor) :
      RichRecipeCalls strata parentKey (.fixedBody parent selected admitted)
  | resources (calls : RichRecipeCalls strata parentKey parent) (transfer) :
      RichRecipeCalls strata parentKey (.resources parent transfer)
  | action (calls : RichRecipeCalls strata parentKey parent) (change) :
      RichRecipeCalls strata parentKey (.action change parent)

private theorem recipeIndependentBody {A B : VExpr}
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (whole : TypeRelated env U registry target
      ((VExpr.forallE A B.lift).subst σ) ((VExpr.forallE A B.lift).subst τ)
      (.pi prototypeDomain prototypeBody ambient rows))
    (selected : (key, result) ∈ rows)
    (admitted : Admitted env U registry target key anchor anchor) :
    TypeRelated env U registry target (B.subst σ) (B.subst τ) result := by
  have output := TypeRelated.literalPiBody_pair henv hscoped formed
    (by simpa only [subst] using whole) selected admitted
  simpa only [lift_subst_lift, inst_lift] using output.2

/-- The right recipe, paired code relation, footprint and all-policy depth
are proved together for the same reconstructed syntax. The semantic resource
input is obtained from the actual caller frame by `recipeResources`. -/
theorem RichRecipeCalls.rebuild
    {strata : EquationStratification env}
    {recipe : RichCodeRecipe env U registry target source locals σ expression relevant profile footprint}
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (cutoff : Nat) (cutoffBound : cutoff ≤ strata.rules.length) (fuel : Nat → Nat)
    (constants callerSchedule : Nat)
    (calls : RichRecipeCalls strata
      (EquationControlMeasure.key strata.rules.length cutoff fuel constants callerSchedule) recipe)
    (bounded : WithinAbove cutoff fuel
      (fun control => recipe.stratifiedDepth (strata.headOrdinal registry) control))
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (resources : RecipeResourceRealization env U registry target source σ τ footprint) :
    ∃ next : RichCodeRecipe env U registry target source locals τ expression relevant profile footprint,
      (∀ policy, next.headDepth policy = recipe.headDepth policy) ∧
      TypeRelated env U registry target (expression.subst σ) (expression.subst τ) profile := by
  induction calls generalizing τ with
  | root owner node closed expressionEq certificate available lower =>
    let children := fun control => certificate.stratifiedDepth (strata.headOrdinal registry) control
    have rootBound : WithinAbove cutoff fuel (headDepth owner.selected.ordinal children) := by
      intro control active
      simpa only [RichCodeRecipe.stratifiedDepth, RichCodeRecipe.headDepth,
        stratifiedHeadPolicy, owner.headOrdinal_eq, children, RichCert.stratifiedDepth,
        headDepth] using bounded control active
    have decrease := openingDecrease owner.selected.ordinal_pos owner.selected.ordinal_le
      cutoffBound rootBound constants callerSchedule owner.selected.origin.ordered.constantCount
      (recipeRootSchedule owner node)
    obtain ⟨answer⟩ := lower children (fun _ _ => Nat.le_refl _) owner.sourceCutoff decrease
    have child := answer.related.code_of_sortable henv hscoped formed certificate.formed
    simp only [closed.subst_eq (σ := _) .zero] at child
    have targetClosed := expressionEq.closedN_iff.mp closed
    refine ⟨.root _ _ τ owner node closed expressionEq _ certificate available,
      (fun _ => by simp only [RichCodeRecipe.headDepth]), ?_⟩
    simpa only [targetClosed.subst_eq (σ := _) .zero] using TypeRelated.levels henv expressionEq expressionEq child
  | domain calls ih =>
    obtain ⟨next, depth, whole⟩ := ih (by simpa only [RichCodeRecipe.stratifiedDepth, RichCodeRecipe.headDepth] using bounded) substitutions resources
    exact ⟨.domain next, (fun policy => by simpa only [RichCodeRecipe.headDepth] using depth policy), TypeRelated.literalPiDomain henv hscoped formed
      (by simpa only [subst] using whole)⟩
  | fixedBody calls selected admitted ih =>
    obtain ⟨next, depth, whole⟩ := ih (by simpa only [RichCodeRecipe.stratifiedDepth, RichCodeRecipe.headDepth] using bounded) substitutions resources
    exact ⟨.fixedBody next selected admitted, (fun policy => by simpa only [RichCodeRecipe.headDepth] using depth policy),
      recipeIndependentBody henv hscoped formed whole selected admitted⟩
  | action calls change ih =>
    obtain ⟨next, depth, whole⟩ := ih (by simpa only [RichCodeRecipe.stratifiedDepth, RichCodeRecipe.headDepth] using bounded) substitutions resources
    exact ⟨.action change next, (fun policy => by simpa only [RichCodeRecipe.headDepth] using depth policy), change.codeMap henv hscoped whole⟩
  | resources calls transfer ih =>
    obtain ⟨next, depth, whole⟩ := ih (by
      intro control active
      apply Nat.le_trans (Nat.le_max_left _ _)
      simpa only [RichCodeRecipe.stratifiedDepth, RichCodeRecipe.headDepth] using bounded control active)
      substitutions (transfer.realize henv hscoped formed resources)
    refine ⟨.resources next (transfer.requery τ), ?_, whole⟩
    intro policy
    simp only [RichCodeRecipe.headDepth, transfer.requery_headDepth, depth]
  | @body source locals A B relevant prototypeDomain prototypeBody footprint σ n support result key rows
      parent calls selected anchor ih =>
    have previous : RecipeResourceRealization env U registry target source σ.tail τ.tail footprint := by
      intro index need member assigned lookup
      obtain ⟨value⟩ := resources (index + 1) need
        (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨(index, need), member, rfl⟩))
        assigned.lift (.succ lookup)
      exact ⟨by simpa only [lift_subst, Subst.tail] using value⟩
    have tailSubstitutions : Ctx.SubstEq env U target σ.tail τ.tail source := by
      cases substitutions with
      | cons tail _ _ => exact tail
    obtain ⟨next, depth, whole⟩ := ih (by simpa only [RichCodeRecipe.stratifiedDepth, RichCodeRecipe.headDepth] using bounded) tailSubstitutions previous
    obtain ⟨argument⟩ := resources 0 _ List.mem_cons_self A.lift (.zero (Γ := source) (ty := A))
    have raw := substitutions.lookup (Lookup.zero (Γ := source) (ty := A))
    have paired : Related env U registry target (σ 0) (τ 0) (A.subst σ.tail)
        key.input argument.support := by
      simpa only [lift_subst] using argument.related
    rw [lift_subst] at raw
    have admitted := TypeRelated.literalPiRightAdmissionFromBinder henv hscoped formed
      (by simpa only [subst] using whole) selected anchor raw paired
    let unused : Atom n := match n with | 0 => true | _ + 1 => .sort true
    let change : AtomView env U registry target (n := n + 1)
        (.fn key unused) (.fn (reanchorKey key (τ 0)) unused) := .reanchor admitted
    let widened : RichCodeRecipe env U registry target source locals τ.tail (.forallE A B)
        relevant (.pi prototypeDomain prototypeBody support
          (reanchorRows key (reanchorKey key (τ 0)) rows)) footprint :=
      .action (.map change) next
    have result := TypeRelated.literalPiRowPairFromBinder henv hscoped formed
      (by simpa only [subst] using whole) selected anchor raw paired
    have leftEq : σ.tail.cons (σ 0) = σ := by funext i; cases i <;> rfl
    have rightEq : τ.tail.cons (τ 0) = τ := by funext i; cases i <;> rfl
    refine ⟨.body (key := reanchorKey key (τ 0)) widened
      (reanchorRows.changed (newKey := reanchorKey key (τ 0)) selected) rfl, (fun policy => by simpa only [RichCodeRecipe.headDepth, widened] using depth policy), ?_⟩
    simpa only [inst_lift_cons, leftEq, rightEq] using result

/-- The public entry consumes the actual caller frame. In particular, a
resource-transfer node cannot ask the caller to supply a semantic realization
of its hidden requirements: those are evaluated internally from frame lookup. -/
theorem RichRecipeCalls.rebuildFromFrame
    {strata : EquationStratification env}
    {recipe : RichCodeRecipe env U registry target source locals σ expression relevant profile footprint}
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (cutoff : Nat) (cutoffBound : cutoff ≤ strata.rules.length) (fuel : Nat → Nat)
    (constants callerSchedule : Nat)
    (calls : RichRecipeCalls strata
      (EquationControlMeasure.key strata.rules.length cutoff fuel constants callerSchedule) recipe)
    (bounded : WithinAbove cutoff fuel
      (fun control => recipe.stratifiedDepth (strata.headOrdinal registry) control))
    {context : ContextDerivation sourceEnv U source}
    (frame : OriginalRichFrame sourceEnv env U registry target context locals σ τ available)
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (resources : footprint.Available available) :
    ∃ next : RichCodeRecipe env U registry target source locals τ expression relevant profile footprint,
      (∀ policy, next.headDepth policy = recipe.headDepth policy) ∧
      TypeRelated env U registry target (expression.subst σ) (expression.subst τ) profile ∧
      WithinAbove cutoff fuel
        (fun control => next.stratifiedDepth (strata.headOrdinal registry) control) := by
  obtain ⟨next, sameDepth, related⟩ := calls.rebuild henv hscoped formed cutoff cutoffBound fuel
    constants callerSchedule bounded substitutions (frame.recipeResources henv hscoped formed resources)
  exact ⟨next, sameDepth, related, by
    intro control active
    simpa only [RichCodeRecipe.stratifiedDepth, sameDepth] using bounded control active⟩

/-- Reconstruction attaches the computed recipe to the actual caller
original. Its certificate and paired semantics share the exact same result,
without an original comparison spanning caller and canonical source. -/
theorem RichRecipeCalls.rebuildCertificate
    {strata : EquationStratification env}
    {recipe : RichCodeRecipe env U registry target source locals σ expression relevant profile footprint}
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (cutoff : Nat) (cutoffBound : cutoff ≤ strata.rules.length) (fuel : Nat → Nat)
    (constants callerSchedule : Nat)
    (calls : RichRecipeCalls strata
      (EquationControlMeasure.key strata.rules.length cutoff fuel constants callerSchedule) recipe)
    (bounded : WithinAbove cutoff fuel
      (fun control => recipe.stratifiedDepth (strata.headOrdinal registry) control))
    {context : ContextDerivation sourceEnv U source}
    (frame : OriginalRichFrame sourceEnv env U registry target context locals σ τ available)
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (resources : footprint.Available available)
    (node : EndpointState nodeEnv U source expression assigned) :
    ∃ certificate : RichCert nodeEnv env U registry target node locals τ relevant profile footprint,
      (∀ policy, certificate.headDepth policy = recipe.headDepth policy) ∧
      TypeRelated env U registry target (expression.subst σ) (expression.subst τ) profile ∧
      WithinAbove cutoff fuel
        (fun control => certificate.stratifiedDepth (strata.headOrdinal registry) control) := by
  obtain ⟨next, sameDepth, related, nextBound⟩ := calls.rebuildFromFrame henv hscoped formed
    cutoff cutoffBound fuel constants callerSchedule bounded frame substitutions resources
  exact ⟨.recipe next, (fun policy => by simpa only [RichCert.headDepth] using sameDepth policy),
    related, by simpa only [RichCert.stratifiedDepth, RichCert.headDepth,
      RichCodeRecipe.stratifiedDepth] using nextBound⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
