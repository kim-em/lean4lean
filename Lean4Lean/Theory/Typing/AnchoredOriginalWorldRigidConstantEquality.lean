import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRigidConstantStep

/-! The primitive constant equality clause executes the same rigid-family
input through the checked primitive F producer. Only the opposite displayed
universe packet changes; its exact frozen demand and retained header remain. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
open private singletonSponsoredBelow from
  Lean4Lean.Theory.Typing.AnchoredOriginalWorldPiReanchorReplay
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

private theorem primitiveOppositeWorld
    {strata : EquationStratification env} {P : VEnv → Prop}
    {context : ContextDerivation sourceEnv U source}
    {plan : RigidFamilySpine n} {support : Profile n}
    (input : RichRigidConstantInput sourceEnv env U registry target name frozenLevels levels plan support)
    (reference : EndpointRef sourceEnv U source (.const name levels) assigned)
    (opposite : EndpointRef sourceEnv U source (.const name nextLevels) assigned)
    (primitive : reference.Primitive)
    (provenance : EndpointProvenance context (.ref reference))
    (controls : OriginalWorldControls strata sourceEnv)
    (frame : OriginalRichFrame sourceEnv env U registry target context locals σ τ available)
    (captured : WorldEnvironmentProvenance strata U (frame.dependencyEnvironment controls.ordered))
    (baseline : WorldEnvironmentProvenance strata U baselineEnvironment)
    (frontier : List (World strata.rules.length))
    (capacity : environmentCost (frame.dependencyEnvironment controls.ordered) ≤ environmentCost baselineEnvironment)
    (covered : Covered (@EquationControlMeasure.Less strata.rules.length) captured.worlds baseline.worlds)
    (data : WorldUnaryFrameData P controls frontier frame captured)
    (closed : available.AtomClosed) (formed : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (sourceClosed : ∀ source, source ≤ env → P source)
    (queryReady : ControlledStoredQuery controls frontier
      (.observation (input.observation (.ref reference) locals σ)))
    (paid : Sponsored frontier [originalCallWorld controls .fundamental (.ref reference) baseline])
    (unary : WorldBoundedUnaryCallBank env U registry strata P
      (frontier ++ [originalCallWorld controls .fundamental (.ref reference) baseline]))
    (replay : WorldBoundedCallBank env U registry strata P
      (frontier ++ [originalCallWorld controls .fundamental (.ref reference) baseline]))

    (nextWF : ∀ level ∈ nextLevels, level.WF U)
    (equivalent : List.Forall₂ (· ≈ ·) levels nextLevels) :
    ∃ answer : RichComputationalValue sourceEnv env U registry target (.ref reference)
        locals σ τ available (.singleton (plan.atom name frozenLevels [])),
    ∃ rightQuery : RichGradedResult sourceEnv env U registry target (.ref opposite)
        locals τ available (.singleton (plan.atom name frozenLevels [])),
      Related env U registry target ((VExpr.const name levels).subst σ) ((VExpr.const name nextLevels).subst τ)
        (assigned.subst σ) (.singleton (plan.atom name frozenLevels [])) answer.support ∧
      Nonempty (ControlledStoredQuery controls frontier (.certificate answer.certificate)) ∧
      Nonempty (ControlledStoredQuery controls frontier (.observation rightQuery.observation)) := by
  obtain ⟨answer, certificateReady, _⟩ := input.primitiveWorld reference primitive provenance
    controls frame captured baseline frontier capacity covered data closed formed substitutions henv hscoped
    sourceClosed queryReady paid unary replay
  have frozenNext : List.Forall₂ (· ≈ ·) frozenLevels nextLevels :=
    Lean4Lean.List.Forall₂.trans (T := (· ≈ ·)) (fun _ _ _ a b => a.trans b)
      input.frozenLevelsEq equivalent
  let moved := input.redisplay nextWF frozenNext
  let result : RichGradedResult sourceEnv env U registry target (.ref opposite) locals τ available
      (.singleton (plan.atom name frozenLevels [])) := {
    rank := n, bound := Nat.le_refl _, raw := .singleton (plan.atom name frozenLevels []),
    footprint := [], observation := moved.observation (.ref opposite) locals τ,
    adapter := by rw [raiseProfile_self]; exact .refl _,
    resources := (fun _ _ member => nomatch member),
    live := input.ready.live plan name frozenLevels [] }
  have headerPaid := singletonSponsoredBelow paid
    (originalClosedHeader_below controls input.origin
      (.ref (input.origin.familyHeader input.seedWF).reference) (.ref reference) baseline
      .fundamental .fundamental)
  have resultReady := moved.observationControlled controls (.ref opposite) locals τ
    (input.certificateControlled controls (.ref reference) locals σ queryReady) headerPaid
  have selfLevels : List.Forall₂ (· ≈ ·) levels levels :=
    Lean4Lean.List.Forall₂.rfl (fun _ _ => rfl)
  have related : Related env U registry target (.const name levels) (.const name levels)
      (assigned.subst σ) (.singleton (plan.atom name frozenLevels [])) answer.support := by
    simpa only [subst_const] using answer.related
  exact ⟨answer, result, by
    simpa only [subst_const] using related.levels henv
      (.const input.levelsWF input.levelsWF selfLevels) (.const input.levelsWF nextWF equivalent),
    certificateReady, ⟨resultReady⟩⟩
section ConstantEquality
variable
    {env sourceEnv : VEnv} {U : Nat} {source target : List VExpr}
    {name : Name} {info : VConstant} {leftLevels rightLevels : List VLevel} {level : VLevel}
    {strata : EquationStratification env} {P : VEnv → Prop}
    {context : ContextDerivation sourceEnv U source}
    {plan : RigidFamilySpine n} {support : Profile n}
    (lookup : sourceEnv.constants name = some info)
    (leftWF : ∀ level ∈ leftLevels, level.WF U)
    (rightWF : ∀ level ∈ rightLevels, level.WF U)
    (length : leftLevels.length = info.uvars)
    (equivalent : List.Forall₂ (· ≈ ·) leftLevels rightLevels)
    (levelWF : level.WF U)
    (header : Derivation sourceEnv U [] (info.type.instL leftLevels) (info.type.instL rightLevels) (.sort level))
    (ambient : Derivation sourceEnv U source (info.type.instL leftLevels) (info.type.instL rightLevels) (.sort level))

local notation "original" => Derivation.constDF lookup leftWF rightWF length equivalent levelWF header ambient

/-- Forward primitive equality F, using only actual lower unary and replay
banks. The universe demand is frozen independently of both constDF displays. -/
theorem RichRigidConstantInput.constDFForwardWorld
    (input : RichRigidConstantInput sourceEnv env U registry target name frozenLevels leftLevels plan support)
    (provenance : EndpointProvenance context (.ref (.left original)))
    (controls : OriginalWorldControls strata sourceEnv)
    (frame : OriginalRichFrame sourceEnv env U registry target context locals σ τ available)
    (captured : WorldEnvironmentProvenance strata U (frame.dependencyEnvironment controls.ordered))
    (baseline : WorldEnvironmentProvenance strata U baselineEnvironment)
    (frontier : List (World strata.rules.length))
    (capacity : environmentCost (frame.dependencyEnvironment controls.ordered) ≤ environmentCost baselineEnvironment)
    (covered : Covered (@EquationControlMeasure.Less strata.rules.length) captured.worlds baseline.worlds)
    (data : WorldUnaryFrameData P controls frontier frame captured)
    (closed : available.AtomClosed) (formed : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (sourceClosed : ∀ source, source ≤ env → P source)
    (queryReady : ControlledStoredQuery controls frontier
      (.observation (input.observation (.ref (.left original)) locals σ)))
    (paid : Sponsored frontier [originalCallWorld controls .fundamental (.ref (.left original)) baseline])
    (unary : WorldBoundedUnaryCallBank env U registry strata P
      (frontier ++ [originalCallWorld controls .fundamental (.ref (.left original)) baseline]))
    (replay : WorldBoundedCallBank env U registry strata P
      (frontier ++ [originalCallWorld controls .fundamental (.ref (.left original)) baseline])) :
    ∃ result : OriginalDirectionalEqualityResult original true env registry target locals σ τ available
        (.singleton (plan.atom name frozenLevels [])),
      Nonempty (ControlledStoredQuery controls frontier (.observation result.rightQuery.observation)) := by
  obtain ⟨answer, query, related, _, ready⟩ := primitiveOppositeWorld input (.left original) (.right original)
    trivial provenance controls frame captured baseline frontier capacity covered data closed formed substitutions
    henv hscoped sourceClosed queryReady paid unary replay rightWF equivalent
  exact ⟨⟨answer.support, related, query⟩, ready⟩

/-- Reverse primitive equality retains the original left-hand assigned seed,
while the runtime constant and its right observer change to the other display. -/
theorem RichRigidConstantInput.constDFReverseWorld
    (input : RichRigidConstantInput sourceEnv env U registry target name frozenLevels rightLevels plan support)
    (provenance : EndpointProvenance context (.ref (.right original)))
    (controls : OriginalWorldControls strata sourceEnv)
    (frame : OriginalRichFrame sourceEnv env U registry target context locals σ τ available)
    (captured : WorldEnvironmentProvenance strata U (frame.dependencyEnvironment controls.ordered))
    (baseline : WorldEnvironmentProvenance strata U baselineEnvironment)
    (frontier : List (World strata.rules.length))
    (capacity : environmentCost (frame.dependencyEnvironment controls.ordered) ≤ environmentCost baselineEnvironment)
    (covered : Covered (@EquationControlMeasure.Less strata.rules.length) captured.worlds baseline.worlds)
    (data : WorldUnaryFrameData P controls frontier frame captured)
    (closed : available.AtomClosed) (formed : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (sourceClosed : ∀ source, source ≤ env → P source)
    (queryReady : ControlledStoredQuery controls frontier
      (.observation (input.observation (.ref (.right original)) locals σ)))
    (paid : Sponsored frontier [originalCallWorld controls .fundamental (.ref (.right original)) baseline])
    (unary : WorldBoundedUnaryCallBank env U registry strata P
      (frontier ++ [originalCallWorld controls .fundamental (.ref (.right original)) baseline]))
    (replay : WorldBoundedCallBank env U registry strata P
      (frontier ++ [originalCallWorld controls .fundamental (.ref (.right original)) baseline])) :
    ∃ result : OriginalDirectionalEqualityResult original false env registry target locals σ τ available
        (.singleton (plan.atom name frozenLevels [])),
      Nonempty (ControlledStoredQuery controls frontier (.observation result.rightQuery.observation)) := by
  have reverse : List.Forall₂ (· ≈ ·) rightLevels leftLevels :=
    Lean4Lean.List.Forall₂.imp (fun _ _ equal => equal.symm) (Lean4Lean.List.Forall₂.flip equivalent)
  obtain ⟨answer, query, related, _, ready⟩ := primitiveOppositeWorld input (.right original) (.left original)
    trivial provenance controls frame captured baseline frontier capacity covered data closed formed substitutions
    henv hscoped sourceClosed queryReady paid unary replay leftWF reverse
  exact ⟨⟨answer.support, related, query⟩, ready⟩

end ConstantEquality
end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
