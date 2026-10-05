import Lean4Lean.Theory.Typing.AnchoredOriginalRichPiExtraction
import Lean4Lean.Theory.Typing.AnchoredOriginalRichVariableQueries
import Lean4Lean.Theory.Typing.AnchoredSortableVariableNormalization
import Lean4Lean.Theory.Typing.AnchoredSortableEtaPack
import Lean4Lean.Theory.Typing.AnchoredOriginalRichCodeHeadDepth

/-! A literal variable codomain is compiled from the selected row's actual
body certificate. The retained binder pack controls the finite leaf demands;
the whole row input is not installed as a new footprint on the destination.
Reconstruction uses an actual query at the destination argument itself. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
set_option maxRecDepth 4096

/-- The computational leaves of a selected variable body are drawn from
the actual body footprint, including only its existing singleton closure. -/
theorem RichPiRowCertificate.variableBodyTrace
    {domainNode : EndpointState sourceEnv U source A (.sort u)}
    {bodyNode : EndpointState sourceEnv U (A :: source) (.bvar 0) (.sort v)}
    (row : RichPiRowCertificate env U registry target locals σ available relevant
      domainNode bodyNode (key : Key n) result)
    (closed : available.AtomClosed) :
    ∃ required, ∃ query : SortableCert env U registry target (Locals.push locals)
      (σ.cons key.anchor) (.bvar 0) relevant result required,
      (∀ index need, (index, need) ∈ required → index = 0 ∧
        need ∈ row.bodyFootprint.localNeeds ++ row.bodyFootprint.localNeeds.flatMap Need.singletons) ∧
      (∀ index need, (index, need) ∈ required → need.rank ≤ n) ∧
      List.Subset (required.atGrade n).atoms key.input.atoms := by
  let localNeeds := row.bodyFootprint.localNeeds
  have resources := row.pack.available_atomized_localNeeds row.outsideAvailable
  obtain ⟨required, ⟨query⟩, supplied⟩ := row.body.variableQuery
    (Valuation.push_atomized_closed closed localNeeds) resources
  have leaves : ∀ index need, (index, need) ∈ required → index = 0 ∧
      need ∈ row.bodyFootprint.localNeeds ++ row.bodyFootprint.localNeeds.flatMap Need.singletons := by
    intro index need member
    have indexEq := query.variableTrace.indices member
    subst index
    exact ⟨rfl, supplied 0 need member⟩
  refine ⟨required, query, leaves, ?_, ?_⟩
  · intro index need member
    exact (row.pack.atomized_localNeeds need (leaves index need member).2).1
  · intro atom member
    obtain ⟨⟨index, need⟩, selected, belongs⟩ := List.mem_flatMap.mp member
    exact row.covered atom
      ((row.pack.atomized_localNeeds need (leaves index need selected).2).2 atom belongs)

/-- A finite code program for the variable body. It contains no original
derivation supplier and performs no recursive semantic call. -/
structure VariableBodyProgram (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (input output : Profile n) where
  rank : Nat
  bound : n ≤ rank
  adapter : GeneralNormalProfileAdapter env U registry target
    (raiseProfile rank bound input) (raiseProfile rank bound output)

/-- Only these computed argument atoms are needed by the selected body.
Unused atoms of the original row key are absent. -/
structure VariableBodyDemand (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (keyInput output : Profile n) where
  input : Profile n
  covered : List.Subset input.atoms keyInput.atoms
  program : VariableBodyProgram env U registry target input output

private noncomputable def selectGeneral {p q : Profile n}
    (included : List.Subset q.atoms p.atoms) :
    GeneralNormalProfileAdapter env U registry target p q :=
  GeneralProfileAdapter.select (fun _ h => by
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp h
    exact List.mem_map.mpr ⟨a, included ha, rfl⟩)

theorem RichPiRowCertificate.variableBodyDemand
    {domainNode : EndpointState sourceEnv U source A (.sort u)}
    {bodyNode : EndpointState sourceEnv U (A :: source) (.bvar 0) (.sort v)}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (formed : OnCtx target (env.IsType U))
    (row : RichPiRowCertificate env U registry target locals σ available relevant
      domainNode bodyNode (key : Key n) result)
    (closed : available.AtomClosed) :
    Nonempty (VariableBodyDemand env U registry target key.input result) := by
  obtain ⟨required, query, _, bounded, covered⟩ := row.variableBodyTrace closed
  let trace := query.variableTrace
  let N := max n trace.height
  have hn : n ≤ N := Nat.le_max_left _ _
  have ht : trace.height ≤ N := Nat.le_max_right _ _
  refine ⟨⟨required.atGrade n, covered, N, hn, ?_⟩⟩
  rw [← Footprint.atGrade_raise hn bounded]
  exact trace.normalize henv hscoped formed N ht

/-- The selected row itself computes the argument-to-result program, even
when grading and code actions make the two profiles different. -/
theorem RichPiRowCertificate.variableBodyProgram
    {domainNode : EndpointState sourceEnv U source A (.sort u)}
    {bodyNode : EndpointState sourceEnv U (A :: source) (.bvar 0) (.sort v)}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (formed : OnCtx target (env.IsType U))
    (row : RichPiRowCertificate env U registry target locals σ available relevant
      domainNode bodyNode (key : Key n) result)
    (closed : available.AtomClosed) :
    Nonempty (VariableBodyProgram env U registry target key.input result) := by
  obtain ⟨required, query, _, bounded, covered⟩ := row.variableBodyTrace closed
  let trace := query.variableTrace
  let N := max n trace.height
  have hn : n ≤ N := Nat.le_max_left _ _
  have ht : trace.height ≤ N := Nat.le_max_right _ _
  have selected : GeneralNormalProfileAdapter env U registry target
      (raiseProfile N hn key.input) (required.atGrade N) := by
    rw [Footprint.atGrade_raise hn bounded]
    exact selectGeneral (raiseProfile_subset hn covered)
  exact ⟨⟨N, hn, selected.comp (trace.normalize henv hscoped formed N ht)⟩⟩

/-- Compile onto an arbitrary actual original argument endpoint. The
original argument observation is retained (only raised); its frame and
footprint are unchanged. -/
noncomputable def VariableBodyProgram.replay
    (program : VariableBodyProgram env U registry target input output)
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (formed : OnCtx target (env.IsType U))
    (argument : RichGradedResult argumentEnv env U registry target argumentNode
      argumentLocals argumentσ argumentAvailable input) :
    RichGradedResult argumentEnv env U registry target argumentNode
      argumentLocals argumentσ argumentAvailable output := by
  let N := max argument.rank program.rank
  have ha : argument.rank ≤ N := Nat.le_max_left _ _
  have hp : program.rank ≤ N := Nat.le_max_right _ _
  let raised := argument.raiseTo henv hscoped formed N ha
  refine ⟨N, Nat.le_trans program.bound hp, raised.raw, raised.footprint,
    raised.observation, ?_, raised.resources, raised.live⟩
  have mapped := GeneralNormalProfileAdapter.raise henv hscoped formed hp program.adapter
  simp only [raiseProfile_trans] at mapped
  exact raised.adapter.comp mapped

theorem VariableBodyProgram.replay_footprint
    (program : VariableBodyProgram env U registry target input output)
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (formed : OnCtx target (env.IsType U))
    (argument : RichGradedResult argumentEnv env U registry target argumentNode
      argumentLocals argumentσ argumentAvailable input) :
    (program.replay henv hscoped formed argument).footprint = argument.footprint := rfl

theorem VariableBodyProgram.replay_headDepth
    (program : VariableBodyProgram env U registry target input output)
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (formed : OnCtx target (env.IsType U))
    (argument : RichGradedResult argumentEnv env U registry target argumentNode
      argumentLocals argumentσ argumentAvailable input)
    (policy : Name → Nat → Nat) :
    (program.replay henv hscoped formed argument).observation.headDepth policy =
      argument.observation.headDepth policy :=
  argument.observation.headDepth_raise policy (Nat.le_max_left _ _)

/-- Reconstruct from the computed demand alone. The actual destination
argument query is the sole source-query input and bounds every returned
masked control on the same witness. -/
theorem VariableBodyDemand.compile
    (demand : VariableBodyDemand env U registry target keyInput output)
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (formed : OnCtx target (env.IsType U))
    (sorted : output.HasType (.sort relevant))
    (argument : RichGradedResult argumentEnv env U registry target argumentNode
      argumentLocals argumentσ argumentAvailable demand.input) :
    ∃ required, ∃ certificate : RichCert argumentEnv env U registry target argumentNode
      argumentLocals argumentσ relevant output required,
      required.Available argumentAvailable ∧ ∀ policy,
        certificate.headDepth policy ≤ argument.observation.headDepth policy := by
  obtain ⟨required, certificate, resources, depth⟩ :=
    (demand.program.replay henv hscoped formed argument).code_headDepth henv sorted
  refine ⟨required, certificate, resources, ?_⟩
  intro policy
  rw [← demand.program.replay_headDepth henv hscoped formed argument policy]
  exact depth policy

/-- All masked controls are bounded on the same returned certificate.
The canonical row contributes only a finite adapter; caller-owned argument
queries retain their own policies and are never placed beneath a new mask. -/
theorem RichPiRowCertificate.compileVariableBody_headDepth
    {domainNode : EndpointState sourceEnv U source A (.sort u)}
    {bodyNode : EndpointState sourceEnv U (A :: source) (.bvar 0) (.sort v)}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (formed : OnCtx target (env.IsType U))
    (row : RichPiRowCertificate env U registry target locals σ available relevant
      domainNode bodyNode (key : Key n) result)
    (closed : available.AtomClosed)
    (argument : RichGradedResult argumentEnv env U registry target argumentNode
      argumentLocals argumentσ argumentAvailable key.input) :
    ∃ required, ∃ certificate : RichCert argumentEnv env U registry target argumentNode
      argumentLocals argumentσ relevant result required,
      required.Available argumentAvailable ∧ ∀ policy,
        certificate.headDepth policy ≤ argument.observation.headDepth policy := by
  obtain ⟨program⟩ := row.variableBodyProgram henv hscoped formed closed
  obtain ⟨required, certificate, resources, depth⟩ :=
    (program.replay henv hscoped formed argument).code_headDepth henv row.body.formed
  refine ⟨required, certificate, resources, ?_⟩
  intro policy
  rw [← program.replay_headDepth henv hscoped formed argument policy]
  exact depth policy

/-- This returns an actual source certificate at the destination argument,
not merely a semantic Pi elimination. No body formation is reindexed to an
invented original node. -/
theorem RichPiRowCertificate.compileVariableBody
    {domainNode : EndpointState sourceEnv U source A (.sort u)}
    {bodyNode : EndpointState sourceEnv U (A :: source) (.bvar 0) (.sort v)}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (formed : OnCtx target (env.IsType U))
    (row : RichPiRowCertificate env U registry target locals σ available relevant
      domainNode bodyNode (key : Key n) result)
    (closed : available.AtomClosed)
    (argument : RichGradedResult argumentEnv env U registry target argumentNode
      argumentLocals argumentσ argumentAvailable key.input) :
    ∃ required, Nonempty (RichCert argumentEnv env U registry target argumentNode
      argumentLocals argumentσ relevant result required) ∧ required.Available argumentAvailable := by
  obtain ⟨required, certificate, resources, _⟩ :=
    row.compileVariableBody_headDepth henv hscoped formed closed argument
  exact ⟨required, ⟨certificate⟩, resources⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
