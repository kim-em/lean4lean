import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRetainedRecipeDemand

/-! The pending demand remembers its final operands in the current display.
Binder entry uses the selected actual anchor; skipped binders pull back the
substitution. A canonical closed root may change its ambient substitution
without changing this readback. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1200000

noncomputable def RetainedApplicationDemand.readback
    (demand : RetainedApplicationDemand env U registry target goalFunction goalArgument goalOutput expression atom)
    (τ : Subst) : VExpr × VExpr :=
  by
    induction demand generalizing τ with
    | application => exact (goalFunction.subst τ, goalArgument.subst τ)
    | output _ _ ih | domain _ _ ih | levels _ _ ih => exact ih τ
    | body _ _ anchor _ _ ih => exact ih (τ.cons anchor)
    | rename ρ _ ih => exact ih (Subst.lift_l ρ τ)

private theorem readback_transport (same : expression = next)
    (demand : RetainedApplicationDemand env U registry target goalFunction goalArgument goalOutput expression atom)
    (τ : Subst) : (same ▸ demand).readback τ = demand.readback τ := by
  cases same
  rfl

private theorem levelsSubstitutionKernel
    (levels : EqUpToLevels U expression expression')
    (same : expression.subst σ = expression.subst τ) :
    expression'.subst σ = expression'.subst τ := by
  induction levels generalizing σ τ with
  | bvar => exact same
  | sort | const | elim => rfl
  | app _ _ function argument =>
    obtain ⟨f, a⟩ := VExpr.app.inj same
    change VExpr.app _ _ = VExpr.app _ _
    rw [function f, argument a]
  | proj _ major =>
    exact congrArg (VExpr.proj _ _) (major (VExpr.proj.inj same).2.2)
  | lam _ _ domain body =>
    obtain ⟨a, b⟩ := VExpr.lam.inj same
    change VExpr.lam _ _ = VExpr.lam _ _
    rw [domain a, body b]
  | forallE _ _ domain body =>
    obtain ⟨a, b⟩ := VExpr.forallE.inj same
    change VExpr.forallE _ _ = VExpr.forallE _ _
    rw [domain a, body b]

/-- Only variables actually occurring in the input expression affect the
eventual requested operands. This also covers pending binder instructions. -/
theorem RetainedApplicationDemand.readback_congr
    (demand : RetainedApplicationDemand env U registry target goalFunction goalArgument goalOutput expression atom)
    (same : expression.subst σ = expression.subst τ) :
    demand.readback σ = demand.readback τ := by
  induction demand generalizing σ τ with
  | application =>
    obtain ⟨f, a⟩ := VExpr.app.inj same
    change (goalFunction.subst σ, goalArgument.subst σ) = _
    rw [f, a]
    rfl
  | output path continuation ih => exact ih same
  | domain member continuation ih => exact ih (VExpr.forallE.inj same).1
  | body selected member anchor admitted continuation ih =>
    apply ih
    have body := congrArg (fun e : VExpr => e.inst anchor) (VExpr.forallE.inj same).2
    simpa only [inst_lift_cons] using body
  | levels equal continuation ih => exact ih (levelsSubstitutionKernel equal same)
  | rename ρ continuation ih =>
    apply ih
    simpa only [subst_lift'] using same

theorem RetainedApplicationDemand.readback_closed
    (demand : RetainedApplicationDemand env U registry target goalFunction goalArgument goalOutput expression atom)
    (closed : expression.Closed) : demand.readback σ = demand.readback τ := by
  apply demand.readback_congr
  exact (closed.subst_eq Subst.Fixes.zero).trans (closed.subst_eq Subst.Fixes.zero).symm


private theorem tailConsHead (σ : Subst) : σ.tail.cons (σ 0) = σ := by
  funext i
  cases i <;> rfl

open OriginalClosureMeasure OriginalEndpointFactor OriginalTail EquationWorldClosureOrder EquationStratifiedFuel
private def readbackParent
    (recipe : RichCodeRecipe env U registry target source locals σ expression relevant profile footprint)
    (τ : Subst) : Prop :=
  match recipe with
  | .root .. => True
  | .domain parent | .fixedBody parent _ _ | .resources parent _ | .action _ parent =>
      Nonempty (PreparedRecipeContext parent τ)
  | .body parent _ _ => Nonempty (PreparedRecipeContext parent τ.tail)

private theorem parentPrepared
    (prepared : PreparedRecipeContext recipe τ) : readbackParent recipe τ := by
  cases prepared with
  | root => trivial
  | domain parent | fixedBody parent | resources parent | action parent => exact ⟨parent⟩
  | body parent selected anchor admitted => exact ⟨parent⟩

/-- Backward execution preserves the final operands under the actual resource
substitution, including closed-root reset and both binder operations. -/
theorem WorldCodeRecipeProvenance.focusPreparedDemandReadback
    {strata : EquationStratification env}
    {recipe : RichCodeRecipe env U registry target source locals σ expression relevant profile footprint}
    (annotation : WorldCodeRecipeProvenance strata recipe)
    (prepared : PreparedRecipeContext recipe τ)
    (sources : annotation.Sources P)
    (demand : RetainedApplicationDemand env U registry target goalFunction goalArgument goalOutput expression atom)
    (member : atom ∈ profile.atoms) :
    ∃ input : RichRecipeRootInput env U registry target,
      Nonempty (RichRecipeContext input recipe) ∧ input.strata = strata ∧
      P input.owner.selected.origin.source ∧
      ∃ child : WorldCertProvenance strata input.certificate,
      ∃ controls : OriginalWorldControls strata input.owner.selected.origin.source,
      ∃ provenance : EndpointProvenance (.nil : ContextDerivation input.owner.selected.origin.source U []) input.node,
      ∃ selected ∈ input.profile.atoms,
        ∃ nextDemand : RetainedApplicationDemand env U registry target goalFunction goalArgument goalOutput
          input.canonicalExpression selected,
        nextDemand.readback input.realization = demand.readback τ ∧
        List.Subset ((WorldQuerySite.empty (registry := registry) (target := target)
          controls provenance input.realization).worlds ++ child.worlds) annotation.worlds ∧
        sizeOf child < sizeOf annotation := by
  match annotation with
  | .root source locals σ owner node closed expressionEq realization certificate supplied child controls provenance =>
    refine ⟨⟨_, _, owner, _, _, _, node, closed, expressionEq, source, locals, σ,
      realization, _, _, _, _, certificate, supplied⟩, ⟨.root⟩, rfl, sources,
      child, controls, provenance, atom, member, .levels expressionEq demand, ?_,
      List.Subset.refl _, ?_⟩
    · exact (.levels expressionEq demand : RetainedApplicationDemand env U registry target
        goalFunction goalArgument goalOutput _ _).readback_closed (τ := τ) closed
    · simp_wf
      omega
  | .domain child =>
    obtain ⟨previous⟩ := parentPrepared prepared
    obtain ⟨input, ⟨pending⟩, same, sourceReady, cert, controls, provenance,
      selected, present, nextDemand, sameReadback, included, smaller⟩ :=
      child.focusPreparedDemandReadback previous sources (.domain member demand) List.mem_cons_self
    refine ⟨input, ⟨.domain pending⟩, same, sourceReady, cert, controls, provenance,
      selected, present, nextDemand, sameReadback, included, Nat.lt_trans smaller ?_⟩
    · simp_wf
      omega
  | .body child selected anchor =>
    obtain ⟨previous⟩ := parentPrepared prepared
    obtain ⟨input, ⟨pending⟩, same, sourceReady, cert, controls, provenance,
      nextAtom, present, nextDemand, sameReadback, included, smaller⟩ :=
      child.focusPreparedDemandReadback previous sources
        (.body selected member (τ 0) prepared.bodyAdmission demand) List.mem_cons_self
    refine ⟨input, ⟨.body pending selected anchor⟩, same, sourceReady, cert, controls, provenance,
      nextAtom, present, nextDemand, ?_, included, Nat.lt_trans smaller ?_⟩
    · simpa only [RetainedApplicationDemand.readback, Subst.lift_l_skip, Subst.lift_l_refl,
        Subst.cons_tail, tailConsHead] using sameReadback
    · simp_wf
      omega
  | .fixedBody (anchor := actualAnchor) child selected admitted =>
    obtain ⟨previous⟩ := parentPrepared prepared
    let lifted : RetainedApplicationDemand env U registry target goalFunction goalArgument goalOutput
        expression.lift atom :=
      (lift_eq_lift' (e := expression)).symm ▸ RetainedApplicationDemand.rename (.skip .refl) demand
    obtain ⟨input, ⟨pending⟩, same, sourceReady, cert, controls, provenance,
      nextAtom, present, nextDemand, sameReadback, included, smaller⟩ :=
      child.focusPreparedDemandReadback previous sources
        (.body selected member _ admitted lifted) List.mem_cons_self
    refine ⟨input, ⟨.fixedBody pending selected admitted⟩, same, sourceReady, cert, controls, provenance,
      nextAtom, present, nextDemand, ?_, included, Nat.lt_trans smaller ?_⟩
    · have liftedSame : lifted.readback (τ.cons actualAnchor) = demand.readback τ := by
        dsimp only [lifted]
        rw [readback_transport]
        rfl
      exact sameReadback.trans liftedSame
    · simp_wf
      omega
  | .resources child transfer =>
    obtain ⟨previous⟩ := parentPrepared prepared
    obtain ⟨input, ⟨pending⟩, same, sourceReady, cert, controls, provenance,
      selected, present, nextDemand, sameReadback, included, smaller⟩ :=
      child.focusPreparedDemandReadback previous sources demand member
    refine ⟨input, ⟨.resources pending _⟩, same, sourceReady, cert, controls, provenance,
      selected, present, nextDemand, sameReadback, (fun _ h => List.mem_append_left _ (included h)),
      Nat.lt_trans smaller ?_⟩
    · simp_wf
      omega
  | .action (parent := parent) change child =>
    obtain ⟨previous⟩ := parentPrepared prepared
    obtain ⟨old, oldMember, ⟨selectedAction⟩⟩ := change.atom member
    obtain ⟨input, ⟨pending⟩, same, sourceReady, cert, controls, provenance,
      selected, present, nextDemand, sameReadback, included, smaller⟩ :=
      child.focusPreparedDemandReadback previous sources
        (.output (.code .refl selectedAction (parent.formed.singleton_of_mem oldMember)) demand) oldMember
    refine ⟨input, ⟨.action pending change⟩, same, sourceReady, cert, controls, provenance,
      selected, present, nextDemand, sameReadback, included, Nat.lt_trans smaller ?_⟩
    · simp_wf
      omega
termination_by sizeOf annotation
decreasing_by all_goals simp_wf; omega

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
