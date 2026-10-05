import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRetainedApplicationDispatch
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRetainedBodyDispatch
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRetainedDomainProgramDispatch

/-! A complete retained-program transcript. Each edge owns the SAME selected
body execution, domain program, or charged input/context, and each terminal
owns the actual physical operands and lower-call answers. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder EquationStratifiedFuel
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 2200000

inductive RetainedProgramTransition
    (before : RetainedProgramState env U registry target strata P frontier goalFunction goalArgument goalOutput) :
    RetainedProgramState env U registry target strata P frontier goalFunction goalArgument goalOutput → Type where
  | body (witness : RetainedBodyTransitionWitness before next) : RetainedProgramTransition before next
  | domain (witness : RetainedDomainTransitionWitness before next) : RetainedProgramTransition before next
  | charged (witness : RetainedChargedTransitionWitness before next) : RetainedProgramTransition before next

theorem RetainedProgramTransition.readback (edge : RetainedProgramTransition before next) :
    next.demand.readback next.right = before.demand.readback before.right := by
  cases edge with
  | body witness => exact witness.readback
  | domain witness => exact witness.readback
  | charged witness =>
    cases witness with
    | intro annotation sources resources worlds depth smaller demand member path same opening =>
      have result := opening.readback
      exact result.trans (congrArg (fun d => d.readback before.right) same)

inductive RetainedProgramTrace (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (strata : EquationStratification env) (P : VEnv → Prop)
    (frontier : List (World strata.rules.length)) (goalFunction goalArgument : VExpr)
    {goalRank : Nat} (goalOutput : Atom goalRank) :
    RetainedProgramState env U registry target strata P frontier goalFunction goalArgument goalOutput →
    RetainedProgramTerminal env U registry target strata P frontier goalFunction goalArgument goalOutput → Type where
  | terminal (witness : RetainedApplicationTerminalWitness before terminal) :
      RetainedProgramTrace env U registry target strata P frontier goalFunction goalArgument goalOutput before terminal
  | step (smaller : next.programSize < before.programSize)
      (edge : RetainedProgramTransition before next)
      (rest : RetainedProgramTrace env U registry target strata P frontier goalFunction goalArgument goalOutput next terminal) :
      RetainedProgramTrace env U registry target strata P frontier goalFunction goalArgument goalOutput before terminal

theorem RetainedProgramTrace.readback
    {result : RetainedProgramTerminal env U registry target strata P frontier goalFunction goalArgument goalOutput}
    (trace : RetainedProgramTrace env U registry target strata P frontier goalFunction goalArgument goalOutput before result) :
    result.readback = before.demand.readback before.right := by
  induction trace with
  | terminal witness => exact witness.readback
  | step _ edge _ ih => exact ih.trans edge.readback

theorem RetainedProgramState.stepWithTrace
    (state : RetainedProgramState env U registry target strata P frontier goalFunction goalArgument goalOutput)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (sourceClosed : ∀ next ≤ env, P next) :
    (∃ terminal : RetainedProgramTerminal env U registry target strata P frontier goalFunction goalArgument goalOutput,
      Nonempty (RetainedApplicationTerminalWitness state terminal)) ∨
    ∃ next : RetainedProgramState env U registry target strata P frontier goalFunction goalArgument goalOutput,
      next.programSize < state.programSize ∧ Nonempty (RetainedProgramTransition state next) := by
  let originalState := state
  rcases state with ⟨sourceEnv, source, context, expression, assigned, node, provenance, controls,
    locals, left, right, available, frame, captured, data, closed, substitutions, sourceBelow,
    relevant, rank, profile, footprint, program, annotation, within, sponsored, resources,
    selected, member, demand, paid, bank⟩
  obtain ⟨head, ⟨normalized⟩, same⟩ := demand.headNormalized (EqUpToLevels.refl context.forget.levelWF node.sound).1
  cases head with
  | application ρ functionLevels argumentLevels path =>
    cases program with
    | rich query =>
      cases annotation with
      | rich child =>
        let ready : ControlledStoredQuery controls frontier (.certificate query) := ⟨child, within, sponsored⟩
        rcases richApplicationProgramStepWitness ready provenance frame captured data closed formed substitutions
          resources henv hscoped sourceBelow sourceClosed paid bank demand member ρ functionLevels argumentLevels path
          (same right) normalized with ⟨terminal, readback, witness⟩ | ⟨next, smaller, ⟨witness⟩⟩
        · exact .inl ⟨terminal, witness⟩
        · exact .inr ⟨next, smaller, ⟨.charged witness⟩⟩
    | legacy query =>
      cases annotation with
      | legacy child =>
        obtain ⟨terminal, readback, witness⟩ := legacyApplicationProgramStepWitness child
          (by simpa only [RetainedTypedProgram.certificate, RichCert.stratifiedDepth, RichCert.headDepth] using within)
          sponsored provenance frame captured data closed formed substitutions resources henv hscoped sourceBelow
          paid bank demand member ρ functionLevels argumentLevels path (same right) normalized
        exact .inl ⟨terminal, witness⟩
  | domain path domainMember continuation =>
    cases program with
    | rich query =>
      cases annotation with
      | rich child =>
        let ready : ControlledStoredQuery controls frontier (.certificate query) := ⟨child, within, sponsored⟩
        obtain ⟨next, smaller, witness⟩ := richDomainProgramStepWitness ready provenance frame captured data closed formed substitutions
          resources henv hscoped sourceBelow sourceClosed paid bank member path domainMember continuation demand (same right) normalized
        rcases witness with domain | charged
        · obtain ⟨domain⟩ := domain
          exact .inr ⟨next, smaller, ⟨.domain domain⟩⟩
        · obtain ⟨charged⟩ := charged
          exact .inr ⟨next, smaller, ⟨.charged charged⟩⟩
    | legacy query =>
      cases annotation with
      | legacy child =>
        obtain ⟨next, smaller, ⟨witness⟩⟩ := legacyDomainProgramStepWitness child
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
        obtain ⟨next, smaller, witness⟩ := richBodyProgramStepWitness ready provenance frame captured data closed formed substitutions
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
        obtain ⟨next, smaller, ⟨witness⟩⟩ := legacyBodyProgramStepWitness child
          (by simpa only [RetainedTypedProgram.certificate, RichCert.stratifiedDepth, RichCert.headDepth] using within)
          sponsored provenance frame captured data closed formed substitutions resources henv hscoped sourceBelow
          paid bank member path rowMember admitted atomMember continuation demand (same right) normalized
        exact .inr ⟨next, smaller, ⟨.body witness⟩⟩

/-- Total source normalization retains an actual finite typed transcript. It
preserves the charge-return stack; it does not flatten nested masks or claim
that a source-relative physical application is already a caller query. -/
theorem RetainedProgramState.normalizeWithTrace
    (state : RetainedProgramState env U registry target strata P frontier goalFunction goalArgument goalOutput)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (sourceClosed : ∀ next ≤ env, P next) :
    ∃ terminal : RetainedProgramTerminal env U registry target strata P frontier goalFunction goalArgument goalOutput,
      Nonempty (RetainedProgramTrace env U registry target strata P frontier goalFunction goalArgument goalOutput state terminal) := by
  rcases state.stepWithTrace henv hscoped formed sourceClosed with ⟨terminal, ⟨witness⟩⟩ | ⟨next, smaller, ⟨edge⟩⟩
  · exact ⟨terminal, ⟨.terminal witness⟩⟩
  · obtain ⟨terminal, ⟨rest⟩⟩ := next.normalizeWithTrace henv hscoped formed sourceClosed
    exact ⟨terminal, ⟨.step smaller edge rest⟩⟩
termination_by state.programSize

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
