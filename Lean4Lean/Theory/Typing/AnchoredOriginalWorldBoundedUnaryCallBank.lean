import Lean4Lean.Theory.Typing.AnchoredOriginalWorldBoundedCallBank
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldFamilyHistoryPreservation
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldFamilySandbox
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldBaseHistory

/-! Fixed-frame unary interpretation uses a genuine identity sandbox. It retains
the caller's exact finite frame ancestry, including dormant histories.
The answer uses exactly its existing
frame, substitutions and resource table. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

structure WorldUnaryFrameData
    {strata : EquationStratification env} (P : VEnv → Prop)
    {context : ContextDerivation sourceEnv U source}
    (controls : OriginalWorldControls strata sourceEnv)
    (frontier : List (World strata.rules.length))
    (frame : OriginalRichFrame sourceEnv env U registry target context locals σ τ available)
    (captured : WorldEnvironmentProvenance strata U (frame.dependencyEnvironment controls.ordered)) where
  ambient : frame.Ambient
  sources : frame.raw.AllSources P
  queries : ∀ query ∈ frame.raw.storedQueries,
    Nonempty (ControlledStoredQuery controls frontier query)
  history : WorldFrameHistory strata U registry target P (.mk frame.raw controls captured)
  historyReady : history.Ready frontier controls.cutoff controls.fuel

/-- The identity sandbox uses the exact frame and annotation. Its finite base
ancestry is retained separately by `generation_hereditary`. -/
noncomputable def WorldUnaryFrameData.generation
    {strata : EquationStratification env} {P : VEnv → Prop}
    {context : ContextDerivation sourceEnv U source}
    {controls : OriginalWorldControls strata sourceEnv}
    {frontier : List (World strata.rules.length)}
    {frame : OriginalRichFrame sourceEnv env U registry target context locals σ τ available}
    {captured : WorldEnvironmentProvenance strata U (frame.dependencyEnvironment controls.ordered)}
    (data : WorldUnaryFrameData P controls frontier frame captured)
    (substitutions : Ctx.SubstEq env U target σ τ source) :
    WorldGenerated strata P (frame.captureBase substitutions)
      (frame.captureBase substitutions).initialCaps σ τ (.identity context) frame.raw controls :=
  WorldGenerated.identity (base := frame.captureBase substitutions) data.ambient data.sources controls captured

theorem WorldUnaryFrameData.controlled
    {strata : EquationStratification env} {P : VEnv → Prop}
    {context : ContextDerivation sourceEnv U source}
    {controls : OriginalWorldControls strata sourceEnv}
    {frontier : List (World strata.rules.length)}
    {frame : OriginalRichFrame sourceEnv env U registry target context locals σ τ available}
    {captured : WorldEnvironmentProvenance strata U (frame.dependencyEnvironment controls.ordered)}
    (data : WorldUnaryFrameData P controls frontier frame captured)
    (substitutions : Ctx.SubstEq env U target σ τ source) :
    Nonempty ((data.generation substitutions).Controlled frontier) := by
  apply WorldGenerated.Controlled.ofRetainedQueries
  simpa only [generation, WorldGenerated.retainedQueries, OriginalRichFrame.captureBase] using data.queries

/-- Creating the identity sandbox keeps the exact old frame history as its
single base occurrence; it never recovers ancestry from the raw frame. -/
noncomputable def WorldUnaryFrameData.generation_hereditary
    {strata : EquationStratification env} {P : VEnv → Prop}
    {context : ContextDerivation sourceEnv U source}
    {controls : OriginalWorldControls strata sourceEnv}
    {frontier : List (World strata.rules.length)}
    {frame : OriginalRichFrame sourceEnv env U registry target context locals σ τ available}
    {captured : WorldEnvironmentProvenance strata U (frame.dependencyEnvironment controls.ordered)}
    (data : WorldUnaryFrameData P controls frontier frame captured)
    (substitutions : Ctx.SubstEq env U target σ τ source) :
    (data.generation substitutions).Hereditary frontier where
  tablesClosed := data.historyReady.tableClosed
  bases := .cons data.history .nil
  ready := ⟨data.historyReady, trivial⟩

/-- The ordinary selected-frame case stores the actual generation together
with the histories of all its base occurrences. -/
theorem WorldUnaryFrameData.ofGenerated
    {strata : EquationStratification env} {P : VEnv → Prop}
    {base : OriginalCaptureBase env U registry target}
    {context : ContextDerivation sourceEnv U source}
    {graph : OriginalCaptureMap (common := common) context raw}
    {controls : OriginalWorldControls strata sourceEnv}
    {frontier : List (World strata.rules.length)}
    (frame : OriginalRichFrame sourceEnv env U registry target context locals σ τ available)
    (generated : WorldGenerated strata P base caps left right graph frame.raw controls)
    (ready : generated.Controlled frontier)
    (replayable : generated.Replayable)
    (compatible : generated.UsesControlPrefix controls.cutoff controls.fuel)
    (hereditary : generated.Hereditary frontier) :
    Nonempty (WorldUnaryFrameData P controls frontier frame generated.environment) := by
  refine ⟨⟨generated.erase.ambientGenerated.ambient.2,
    generated.erase.sources.2, ?_, .generated generated hereditary.bases,
    ⟨⟨ready⟩, replayable, hereditary.tablesClosed, compatible, hereditary.ready⟩⟩⟩
  intro query member
  exact ready.selectStored (generated.storedQueries_in_retained member)

/-- These are the unary clauses of the stronger fixed-bound motive. Their
semantic construction remains part of the mutual induction, not an axiom or
a consequence of the old numeric bank. -/
structure WorldBoundedUnaryAt
    (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (strata : EquationStratification env) (P : VEnv → Prop)
    (budget : List (World strata.rules.length)) : Prop where
  computational :
    ∀ {sourceEnv : VEnv} {source target : List VExpr}
      {context : ContextDerivation sourceEnv U source}
      {expression assigned : VExpr}
      (node : EndpointState sourceEnv U source expression assigned),
    EndpointProvenance context node →
    ∀ (controls : OriginalWorldControls strata sourceEnv)
      {locals : List Nat} {σ τ : Subst} {available : Valuation}
      (frame : OriginalRichFrame sourceEnv env U registry target context locals σ τ available)
      (captured : WorldEnvironmentProvenance strata U (frame.dependencyEnvironment controls.ordered))
      {baselineEnvironment} (baseline : WorldEnvironmentProvenance strata U baselineEnvironment)
      (frontier : List (World strata.rules.length)),
    environmentCost (frame.dependencyEnvironment controls.ordered) ≤ environmentCost baselineEnvironment →
    Covered (@EquationControlMeasure.Less strata.rules.length) captured.worlds baseline.worlds →
    frontier ++ [originalCallWorld controls .fundamental node baseline] = budget →
    Sponsored frontier [originalCallWorld controls .fundamental node baseline] →
    WorldUnaryFrameData P controls frontier frame captured →
    available.AtomClosed → OnCtx target (env.IsType U) →
    Ctx.SubstEq env U target σ τ source →
    ∀ {n : Nat} {profile : Profile n} {footprint : Footprint}
      (query : RichObs sourceEnv env U registry target node locals σ profile footprint),
    footprint.Available available → ControlledStoredQuery controls frontier (.observation query) →
    ∃ answer : RichComputationalValue sourceEnv env U registry target node locals σ τ available profile,
      Nonempty (ControlledStoredQuery controls frontier (.certificate answer.certificate)) ∧
      Nonempty (ControlledStoredQuery controls frontier (.observation answer.rightQuery.observation))
  equality :
    ∀ {sourceEnv : VEnv} {source target : List VExpr}
      {context : ContextDerivation sourceEnv U source} {A B assigned : VExpr}
      (original : Derivation sourceEnv U source A B assigned) (forward : Bool),
    EndpointProvenance context (.ref (originalTypeRouteSide original forward)) →
    ∀ (controls : OriginalWorldControls strata sourceEnv)
      {locals : List Nat} {σ τ : Subst} {available : Valuation}
      (frame : OriginalRichFrame sourceEnv env U registry target context locals σ τ available)
      (captured : WorldEnvironmentProvenance strata U (frame.dependencyEnvironment controls.ordered))
      {baselineEnvironment} (baseline : WorldEnvironmentProvenance strata U baselineEnvironment)
      (frontier : List (World strata.rules.length)),
    environmentCost (frame.dependencyEnvironment controls.ordered) ≤ environmentCost baselineEnvironment →
    Covered (@EquationControlMeasure.Less strata.rules.length) captured.worlds baseline.worlds →
    frontier ++ [originalCallWorld controls .fundamental
      (.ref (originalTypeRouteSide original forward)) baseline] = budget →
    Sponsored frontier [originalCallWorld controls .fundamental
      (.ref (originalTypeRouteSide original forward)) baseline] →
    WorldUnaryFrameData P controls frontier frame captured →
    available.AtomClosed → OnCtx target (env.IsType U) →
    Ctx.SubstEq env U target σ τ source →
    ∀ {n : Nat} {profile : Profile n} {footprint : Footprint}
      (query : RichObs sourceEnv env U registry target
        (.ref (originalTypeRouteSide original forward)) locals σ profile footprint),
    footprint.Available available → ControlledStoredQuery controls frontier (.observation query) →
    ∃ answer : OriginalDirectionalEqualityResult original forward env registry target locals σ τ available profile,
      Nonempty (ControlledStoredQuery controls frontier (.observation answer.rightQuery.observation))

def WorldBoundedUnaryCallBank
    (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (strata : EquationStratification env) (P : VEnv → Prop)
    (parent : List (World strata.rules.length)) : Prop :=
  ∀ retained, CallBelow strata.rules.length retained parent →
    WorldBoundedUnaryAt env U registry strata P retained

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
