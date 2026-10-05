import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRetainedProjectionTerminal
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRetainedTermBodyDispatch
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRetainedTermDomainProgramDispatch

/-! A complete retained-program transcript. Each edge owns the SAME selected
body execution, domain program, or charged input/context, and each terminal
owns the actual physical projection children and lower-call answer. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder EquationStratifiedFuel
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 2200000

inductive RetainedTermProgramTransition
    (before : RetainedTermProgramState env U registry target strata P frontier goal goalOutput) :
    RetainedTermProgramState env U registry target strata P frontier goal goalOutput → Type where
  | body (witness : RetainedTermBodyTransitionWitness before next) : RetainedTermProgramTransition before next
  | domain (witness : RetainedTermDomainTransitionWitness before next) : RetainedTermProgramTransition before next
  | charged (witness : RetainedTermChargedTransitionWitness before next) : RetainedTermProgramTransition before next

theorem RetainedTermProgramTransition.readback (edge : RetainedTermProgramTransition before next) :
    next.demand.readback next.right = before.demand.readback before.right := by
  cases edge with
  | body witness => exact witness.readback
  | domain witness => exact witness.readback
  | charged witness =>
    cases witness with
    | intro annotation sources resources worlds depth smaller demand member path same opening =>
      have result := opening.readback
      exact result.trans (congrArg (fun d => d.readback before.right) same)

inductive RetainedProjectionProgramTrace (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (strata : EquationStratification env) (P : VEnv → Prop)
    (frontier : List (World strata.rules.length)) (goal : VExpr)
    {goalRank : Nat} (goalOutput : Atom goalRank) :
    RetainedTermProgramState env U registry target strata P frontier goal goalOutput →
    RetainedProjectionProgramTerminal env U registry target strata P frontier goal goalOutput → Type where
  | terminal (witness : RetainedProjectionTerminalWitness before terminal) :
      RetainedProjectionProgramTrace env U registry target strata P frontier goal goalOutput before terminal
  | step (smaller : next.programSize < before.programSize)
      (edge : RetainedTermProgramTransition before next)
      (rest : RetainedProjectionProgramTrace env U registry target strata P frontier goal goalOutput next terminal) :
      RetainedProjectionProgramTrace env U registry target strata P frontier goal goalOutput before terminal

theorem RetainedProjectionProgramTrace.readback
    {result : RetainedProjectionProgramTerminal env U registry target strata P frontier goal goalOutput}
    (trace : RetainedProjectionProgramTrace env U registry target strata P frontier goal goalOutput before result) :
    result.readback = before.demand.readback before.right := by
  induction trace with
  | terminal witness => exact witness.readback
  | step _ edge _ ih => exact ih.trans edge.readback

theorem RetainedTermProgramState.projectionStepWithTrace
    (state : RetainedTermProgramState env U registry target strata P frontier (.proj goalName goalIndex goalMajor) goalOutput)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (sourceClosed : ∀ next ≤ env, P next) :
    (∃ terminal : RetainedProjectionProgramTerminal env U registry target strata P frontier (.proj goalName goalIndex goalMajor) goalOutput,
      Nonempty (RetainedProjectionTerminalWitness state terminal)) ∨
    ∃ next : RetainedTermProgramState env U registry target strata P frontier (.proj goalName goalIndex goalMajor) goalOutput,
      next.programSize < state.programSize ∧ Nonempty (RetainedTermProgramTransition state next) := by
  let originalState := state
  rcases state with ⟨sourceEnv, source, context, expression, assigned, node, provenance, controls,
    locals, left, right, available, frame, captured, data, closed, substitutions, sourceBelow,
    relevant, rank, profile, footprint, program, annotation, within, sponsored, resources,
    selected, member, demand, paid, bank⟩
  obtain ⟨head, ⟨normalized⟩, same⟩ := demand.headNormalized (EqUpToLevels.refl context.forget.levelWF node.sound).1
  cases head with
  | terminal ρ levels path =>
    change EqUpToLevels U expression (.proj goalName goalIndex (goalMajor.lift' ρ)) at levels
    cases levels with
    | proj majorLevels =>
      cases program with
      | rich query =>
        cases annotation with
        | rich child =>
          let ready : ControlledStoredQuery controls frontier (.certificate query) := ⟨child, within, sponsored⟩
          rcases richProjectionProgramStepWitness ready provenance frame captured data closed formed substitutions
            resources henv hscoped sourceBelow sourceClosed paid bank demand member ρ (.proj majorLevels) path
            (same right) normalized with ⟨terminal, readback, witness⟩ | ⟨next, smaller, ⟨witness⟩⟩
          · exact .inl ⟨terminal, witness⟩
          · exact .inr ⟨next, smaller, ⟨.charged witness⟩⟩
      | legacy query => exact (legacyProjectionProgramNoMember query member).elim
  | domain path domainMember continuation =>
    cases program with
    | rich query =>
      cases annotation with
      | rich child =>
        let ready : ControlledStoredQuery controls frontier (.certificate query) := ⟨child, within, sponsored⟩
        obtain ⟨next, smaller, witness⟩ := richTermDomainProgramStepWitness ready provenance frame captured data closed formed substitutions
          resources henv hscoped sourceBelow sourceClosed paid bank member path domainMember continuation demand (same right) normalized
        rcases witness with domain | charged
        · obtain ⟨domain⟩ := domain
          exact .inr ⟨next, smaller, ⟨.domain domain⟩⟩
        · obtain ⟨charged⟩ := charged
          exact .inr ⟨next, smaller, ⟨.charged charged⟩⟩
    | legacy query =>
      cases annotation with
      | legacy child =>
        obtain ⟨next, smaller, ⟨witness⟩⟩ := legacyTermDomainProgramStepWitness child
          (by simpa only [RetainedTypedProgram.certificate, RichCert.stratifiedDepth, RichCert.headDepth] using within)
          sponsored provenance frame captured data closed formed substitutions resources henv hscoped sourceBelow
          paid bank member path domainMember continuation demand (same right) normalized
        exact .inr ⟨next, smaller, ⟨.domain witness⟩⟩
  | body path rowMember atomMember anchor admitted continuation =>
    cases program with
    | rich query =>
      cases annotation with
      | rich child =>
        let ready : ControlledStoredQuery controls frontier (.certificate query) := ⟨child, within, sponsored⟩
        obtain ⟨next, smaller, witness⟩ := richTermBodyProgramStepWitness ready provenance frame captured data closed formed substitutions
          resources henv hscoped sourceBelow sourceClosed paid bank member path rowMember admitted atomMember continuation
          demand (same right) normalized
        rcases witness with body | charged
        · obtain ⟨body⟩ := body
          exact .inr ⟨next, smaller, ⟨.body body⟩⟩
        · obtain ⟨charged⟩ := charged
          exact .inr ⟨next, smaller, ⟨.charged charged⟩⟩
    | legacy query =>
      cases annotation with
      | legacy child =>
        obtain ⟨next, smaller, ⟨witness⟩⟩ := legacyTermBodyProgramStepWitness child
          (by simpa only [RetainedTypedProgram.certificate, RichCert.stratifiedDepth, RichCert.headDepth] using within)
          sponsored provenance frame captured data closed formed substitutions resources henv hscoped sourceBelow
          paid bank member path rowMember admitted atomMember continuation demand (same right) normalized
        exact .inr ⟨next, smaller, ⟨.body witness⟩⟩

/-- Total source normalization retains an actual finite typed transcript. It
preserves the charge-return stack; it does not flatten nested masks or claim
that a source-relative physical projection is already a caller query. -/
theorem RetainedTermProgramState.normalizeProjectionWithTrace
    (state : RetainedTermProgramState env U registry target strata P frontier (.proj goalName goalIndex goalMajor) goalOutput)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (sourceClosed : ∀ next ≤ env, P next) :
    ∃ terminal : RetainedProjectionProgramTerminal env U registry target strata P frontier (.proj goalName goalIndex goalMajor) goalOutput,
      Nonempty (RetainedProjectionProgramTrace env U registry target strata P frontier (.proj goalName goalIndex goalMajor) goalOutput state terminal) := by
  rcases state.projectionStepWithTrace henv hscoped formed sourceClosed with ⟨terminal, ⟨witness⟩⟩ | ⟨next, smaller, ⟨edge⟩⟩
  · exact ⟨terminal, ⟨.terminal witness⟩⟩
  · obtain ⟨terminal, ⟨rest⟩⟩ := next.normalizeProjectionWithTrace henv hscoped formed sourceClosed
    exact ⟨terminal, ⟨.step smaller edge rest⟩⟩
termination_by state.programSize

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
