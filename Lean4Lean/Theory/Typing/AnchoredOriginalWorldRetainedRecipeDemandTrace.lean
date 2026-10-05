import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRetainedDemandReadback

/-! Exact backward demand execution through a retained recipe context.
The relation records the selected keys, input actions and continuation syntax;
equality of the final displayed operands alone would forget that information. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder EquationStratifiedFuel
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1800000

inductive RetainedRecipeDemandPush
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {target : List VExpr}
    {goalFunction goalArgument : VExpr} {goalRank : Nat} {goalOutput : Atom goalRank}
    (input : RichRecipeRootInput env U registry target) :
    {source : List VExpr} → {locals : List Nat} → {σ : Subst} →
    {expression : VExpr} → {relevant : Bool} → {n : Nat} →
    {profile : Profile n} → {footprint : Footprint} →
    {recipe : RichCodeRecipe env U registry target source locals σ expression relevant profile footprint} →
    (pending : RichRecipeContext input recipe) → (τ : Subst) →
    {atom : Atom n} → RetainedApplicationDemand env U registry target goalFunction goalArgument goalOutput expression atom →
    {rootAtom : Atom input.rank} →
    RetainedApplicationDemand env U registry target goalFunction goalArgument goalOutput input.canonicalExpression rootAtom → Type where
  | root {atom : Atom input.rank}
      (member : atom ∈ input.profile.atoms)
      (demand : RetainedApplicationDemand env U registry target goalFunction goalArgument goalOutput input.expression atom) :
      RetainedRecipeDemandPush input .root τ demand (.levels input.expressionEq demand)
  | domain
      {parent : RichCodeRecipe env U registry target source locals σ (.forallE A B)
        relevant (.pi prototypeDomain prototypeBody (support : Profile n) rows) footprint}
      (pending : RichRecipeContext input parent)
      {rootAtom : Atom input.rank}
      {output : RetainedApplicationDemand env U registry target goalFunction goalArgument goalOutput input.canonicalExpression rootAtom}
      (member : atom ∈ support.atoms)
      (demand : RetainedApplicationDemand env U registry target goalFunction goalArgument goalOutput A atom)
      (previous : RetainedRecipeDemandPush input pending τ (.domain (prototypeDomain := prototypeDomain) (prototypeBody := prototypeBody) (rows := rows) member demand) output) :
      RetainedRecipeDemandPush input (.domain pending) τ demand output
  | body {σ τ : Subst}
      {parent : RichCodeRecipe env U registry target source locals σ.tail (.forallE A B)
        relevant (.pi prototypeDomain prototypeBody (support : Profile n) rows) footprint}
      (pending : RichRecipeContext input parent)
      {rootAtom : Atom input.rank}
      {output : RetainedApplicationDemand env U registry target goalFunction goalArgument goalOutput input.canonicalExpression rootAtom}
      (selected : (key, result) ∈ rows) (anchor : key.anchor = σ 0)
      (member : atom ∈ result.atoms)
      (admitted : Admitted env U registry target key (τ 0) (τ 0))
      (demand : RetainedApplicationDemand env U registry target goalFunction goalArgument goalOutput B atom)
      (previous : RetainedRecipeDemandPush input pending τ.tail
        (.body (prototypeDomain := prototypeDomain) (prototypeBody := prototypeBody) (support := support) selected member (τ 0) admitted demand) output) :
      RetainedRecipeDemandPush input (.body pending selected anchor) τ demand output
  | fixedBody
      {parent : RichCodeRecipe env U registry target source locals σ (.forallE A B.lift)
        relevant (.pi prototypeDomain prototypeBody (support : Profile n) rows) footprint}
      (pending : RichRecipeContext input parent)
      {rootAtom : Atom input.rank}
      {output : RetainedApplicationDemand env U registry target goalFunction goalArgument goalOutput input.canonicalExpression rootAtom}
      (selected : (key, result) ∈ rows)
      (admitted : Admitted env U registry target key anchor anchor)
      (member : atom ∈ result.atoms)
      (demand : RetainedApplicationDemand env U registry target goalFunction goalArgument goalOutput B atom)
      (previous : RetainedRecipeDemandPush input pending τ
        (.body (prototypeDomain := prototypeDomain) (prototypeBody := prototypeBody) (support := support) selected member anchor admitted
          ((lift_eq_lift' (e := B)).symm ▸ .rename (.skip .refl) demand)) output) :
      RetainedRecipeDemandPush input (.fixedBody pending selected admitted) τ demand output
  | resources
      {parent : RichCodeRecipe env U registry target source locals σ expression relevant profile required}
      (pending : RichRecipeContext input parent)
      {rootAtom : Atom input.rank}
      {output : RetainedApplicationDemand env U registry target goalFunction goalArgument goalOutput input.canonicalExpression rootAtom}
      (transfer : RecipeResourceTransfer env U registry target locals σ required footprint)
      (demand : RetainedApplicationDemand env U registry target goalFunction goalArgument goalOutput expression atom)
      (previous : RetainedRecipeDemandPush input pending τ demand output) :
      RetainedRecipeDemandPush input (.resources pending transfer) τ demand output
  | action
      {parent : RichCodeRecipe env U registry target source locals σ expression relevant (profile : Profile n) footprint}
      {nextProfile : Profile m} {atom : Atom m} {original : Atom n}
      (pending : RichRecipeContext input parent)
      {rootAtom : Atom input.rank}
      {output : RetainedApplicationDemand env U registry target goalFunction goalArgument goalOutput input.canonicalExpression rootAtom}
      (change : SortableCodeAction env U registry target relevant profile next nextProfile)
      (member : atom ∈ nextProfile.atoms) (originalMember : original ∈ profile.atoms)
      (selectedAction : SortableCodeAction env U registry target relevant (.singleton original) next (.singleton atom))
      (demand : RetainedApplicationDemand env U registry target goalFunction goalArgument goalOutput expression atom)
      (previous : RetainedRecipeDemandPush input pending τ
        (.output (.code .refl selectedAction (parent.formed.singleton_of_mem originalMember)) demand) output) :
      RetainedRecipeDemandPush input (.action pending change) τ demand output

open private parentPrepared tailConsHead readback_transport from Lean4Lean.Theory.Typing.AnchoredOriginalWorldRetainedDemandReadback

/-- Follow the actual annotation and retain its exact backward request
execution, alongside readback and the original controlled root provenance. -/
theorem WorldCodeRecipeProvenance.focusPreparedDemandTrace
    {strata : EquationStratification env}
    {recipe : RichCodeRecipe env U registry target source locals σ expression relevant profile footprint}
    (annotation : WorldCodeRecipeProvenance strata recipe)
    (prepared : PreparedRecipeContext recipe τ)
    (sources : annotation.Sources P)
    (demand : RetainedApplicationDemand env U registry target goalFunction goalArgument goalOutput expression atom)
    (member : atom ∈ profile.atoms) :
    ∃ input : RichRecipeRootInput env U registry target,
      ∃ pending : RichRecipeContext input recipe, input.strata = strata ∧
      P input.owner.selected.origin.source ∧
      ∃ child : WorldCertProvenance strata input.certificate,
      ∃ controls : OriginalWorldControls strata input.owner.selected.origin.source,
      ∃ provenance : EndpointProvenance (.nil : ContextDerivation input.owner.selected.origin.source U []) input.node,
      ∃ selected ∈ input.profile.atoms,
        ∃ nextDemand : RetainedApplicationDemand env U registry target goalFunction goalArgument goalOutput
          input.canonicalExpression selected,
        nextDemand.readback input.realization = demand.readback τ ∧
        Nonempty (RetainedRecipeDemandPush input pending τ demand nextDemand) ∧
        List.Subset ((WorldQuerySite.empty (registry := registry) (target := target)
          controls provenance input.realization).worlds ++ child.worlds) annotation.worlds ∧
        sizeOf child < sizeOf annotation := by
  match annotation with
  | .root source locals σ owner node closed expressionEq realization certificate supplied child controls provenance =>
    let input : RichRecipeRootInput env U registry target :=
      ⟨_, _, owner, _, _, _, node, closed, expressionEq, source, locals, σ,
        realization, _, _, _, _, certificate, supplied⟩
    refine ⟨input, .root, rfl, sources,
      child, controls, provenance, atom, member, .levels expressionEq demand, ?_,
      ⟨.root (input := input) member demand⟩, List.Subset.refl _, ?_⟩
    · exact (.levels expressionEq demand : RetainedApplicationDemand env U registry target
        goalFunction goalArgument goalOutput _ _).readback_closed (τ := τ) closed
    · simp_wf
      omega
  | .domain child =>
    obtain ⟨previous⟩ := parentPrepared prepared
    obtain ⟨input, pending, same, sourceReady, cert, controls, provenance,
      selected, present, nextDemand, sameReadback, ⟨pushed⟩, included, smaller⟩ :=
      child.focusPreparedDemandTrace previous sources (.domain member demand) List.mem_cons_self
    refine ⟨input, .domain pending, same, sourceReady, cert, controls, provenance,
      selected, present, nextDemand, sameReadback, ⟨.domain pending member demand pushed⟩, included, Nat.lt_trans smaller ?_⟩
    · simp_wf
      omega
  | .body child selected anchor =>
    obtain ⟨previous⟩ := parentPrepared prepared
    obtain ⟨input, pending, same, sourceReady, cert, controls, provenance,
      nextAtom, present, nextDemand, sameReadback, ⟨pushed⟩, included, smaller⟩ :=
      child.focusPreparedDemandTrace previous sources
        (.body selected member (τ 0) prepared.bodyAdmission demand) List.mem_cons_self
    refine ⟨input, .body pending selected anchor, same, sourceReady, cert, controls, provenance,
      nextAtom, present, nextDemand, ?_, ⟨.body pending selected anchor member prepared.bodyAdmission demand pushed⟩, included, Nat.lt_trans smaller ?_⟩
    · simpa only [RetainedApplicationDemand.readback, Subst.lift_l_skip, Subst.lift_l_refl,
        Subst.cons_tail, tailConsHead] using sameReadback
    · simp_wf
      omega
  | .fixedBody (anchor := actualAnchor) child selected admitted =>
    obtain ⟨previous⟩ := parentPrepared prepared
    let lifted : RetainedApplicationDemand env U registry target goalFunction goalArgument goalOutput
        expression.lift atom :=
      (lift_eq_lift' (e := expression)).symm ▸ RetainedApplicationDemand.rename (.skip .refl) demand
    obtain ⟨input, pending, same, sourceReady, cert, controls, provenance,
      nextAtom, present, nextDemand, sameReadback, ⟨pushed⟩, included, smaller⟩ :=
      child.focusPreparedDemandTrace previous sources
        (.body selected member _ admitted lifted) List.mem_cons_self
    refine ⟨input, .fixedBody pending selected admitted, same, sourceReady, cert, controls, provenance,
      nextAtom, present, nextDemand, ?_, ⟨.fixedBody pending selected admitted member demand pushed⟩, included, Nat.lt_trans smaller ?_⟩
    · have liftedSame : lifted.readback (τ.cons actualAnchor) = demand.readback τ := by
        dsimp only [lifted]
        rw [readback_transport]
        rfl
      exact sameReadback.trans liftedSame
    · simp_wf
      omega
  | .resources child transfer =>
    obtain ⟨previous⟩ := parentPrepared prepared
    obtain ⟨input, pending, same, sourceReady, cert, controls, provenance,
      selected, present, nextDemand, sameReadback, ⟨pushed⟩, included, smaller⟩ :=
      child.focusPreparedDemandTrace previous sources demand member
    refine ⟨input, .resources pending _, same, sourceReady, cert, controls, provenance,
      selected, present, nextDemand, sameReadback, ⟨.resources pending _ demand pushed⟩, (fun _ h => List.mem_append_left _ (included h)),
      Nat.lt_trans smaller ?_⟩
    · simp_wf
      omega
  | .action (parent := parent) change child =>
    obtain ⟨previous⟩ := parentPrepared prepared
    obtain ⟨old, oldMember, ⟨selectedAction⟩⟩ := change.atom member
    obtain ⟨input, pending, same, sourceReady, cert, controls, provenance,
      selected, present, nextDemand, sameReadback, ⟨pushed⟩, included, smaller⟩ :=
      child.focusPreparedDemandTrace previous sources
        (.output (.code .refl selectedAction (parent.formed.singleton_of_mem oldMember)) demand) oldMember
    refine ⟨input, .action pending change, same, sourceReady, cert, controls, provenance,
      selected, present, nextDemand, sameReadback, ⟨.action pending change member oldMember selectedAction demand pushed⟩, included, Nat.lt_trans smaller ?_⟩
    · simp_wf
      omega
termination_by sizeOf annotation
decreasing_by all_goals simp_wf; omega

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
