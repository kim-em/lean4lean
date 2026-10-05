import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRetainedProgramApplicationReadback
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRetainedProgramPi
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRetainedProgramLegacyPi
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRetainedDemandHead

/-! Total source-program normalization. The decreasing object is the retained
literal annotation, including raw legacy annotations. Every transition retains
its operand readback. Caller resource reconstruction is a separate consumer. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder EquationStratifiedFuel
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 2200000

theorem RetainedProgramState.stepSource
    (state : RetainedProgramState env U registry target strata P frontier goalFunction goalArgument goalOutput)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (sourceClosed : ∀ next ≤ env, P next) :
    (∃ terminal : RetainedProgramTerminal env U registry target strata P frontier goalFunction goalArgument goalOutput,
      terminal.readback = state.demand.readback state.right) ∨
    ∃ next : RetainedProgramState env U registry target strata P frontier goalFunction goalArgument goalOutput,
      next.programSize < state.programSize ∧
      next.demand.readback next.right = state.demand.readback state.right := by
  rcases state with ⟨sourceEnv, source, context, expression, assigned, node, provenance, controls,
    locals, left, right, available, frame, captured, data, closed, substitutions, sourceBelow,
    relevant, rank, profile, footprint, program, annotation, within, sponsored, resources,
    selected, member, demand, paid, bank⟩
  change (∃ terminal : RetainedProgramTerminal env U registry target strata P frontier goalFunction goalArgument goalOutput, terminal.readback = demand.readback right) ∨
    ∃ next : RetainedProgramState env U registry target strata P frontier goalFunction goalArgument goalOutput, next.programSize < annotation.programSize ∧ next.demand.readback next.right = demand.readback right
  obtain ⟨head, same⟩ := demand.headReadback (EqUpToLevels.refl context.forget.levelWF node.sound).1
  cases head with
  | application ρ functionLevels argumentLevels path =>
    cases program with
    | rich query =>
      cases annotation with
      | rich child =>
        let ready : ControlledStoredQuery controls frontier (.certificate query) :=
          ⟨child, within, sponsored⟩
        exact richApplicationProgramStepReadback ready provenance frame captured data closed formed substitutions
          resources henv hscoped sourceBelow sourceClosed paid bank demand member ρ functionLevels argumentLevels path (same right)
    | legacy query =>
      cases annotation with
      | legacy child =>
        exact .inl (legacyApplicationProgramStepReadback child
          (by simpa only [RetainedTypedProgram.certificate, RichCert.stratifiedDepth, RichCert.headDepth] using within)
          sponsored provenance frame captured data closed formed substitutions resources henv hscoped sourceBelow
          paid bank demand member ρ functionLevels argumentLevels path (same right))
  | domain path domainMember continuation =>
    cases program with
    | rich query =>
      cases annotation with
      | rich child =>
        let ready : ControlledStoredQuery controls frontier (.certificate query) :=
          ⟨child, within, sponsored⟩
        obtain ⟨next, smaller, readback⟩ := richDomainProgramStep ready provenance frame captured data closed formed substitutions
          resources henv hscoped sourceBelow sourceClosed paid bank member path domainMember continuation
        exact .inr ⟨next, smaller, readback.trans (same right)⟩
    | legacy query =>
      cases annotation with
      | legacy child =>
        obtain ⟨next, smaller, readback⟩ := legacyDomainProgramStep child
          (by simpa only [RetainedTypedProgram.certificate, RichCert.stratifiedDepth, RichCert.headDepth] using within)
          sponsored provenance frame captured data closed formed substitutions resources henv hscoped sourceBelow
          paid bank member path domainMember continuation
        exact .inr ⟨next, smaller, readback.trans (same right)⟩
  | body path rowMember atomMember anchor admitted continuation =>
    cases program with
    | rich query =>
      cases annotation with
      | rich child =>
        let ready : ControlledStoredQuery controls frontier (.certificate query) :=
          ⟨child, within, sponsored⟩
        obtain ⟨next, smaller, readback⟩ := richBodyProgramStep ready provenance frame captured data closed formed substitutions
          resources henv hscoped sourceBelow sourceClosed paid bank member path rowMember admitted atomMember continuation
        exact .inr ⟨next, smaller, readback.trans (same right)⟩
    | legacy query =>
      cases annotation with
      | legacy child =>
        obtain ⟨next, smaller, readback⟩ := legacyBodyProgramStep child
          (by simpa only [RetainedTypedProgram.certificate, RichCert.stratifiedDepth, RichCert.headDepth] using within)
          sponsored provenance frame captured data closed formed substitutions resources henv hscoped sourceBelow
          paid bank member path rowMember admitted atomMember continuation
        exact .inr ⟨next, smaller, readback.trans (same right)⟩

/-- Exhaust the retained program. This theorem returns a physical application
in its genuine source frame, with the original requested output and operand
readback. It does not assert a caller-frame query reconstruction. -/
theorem RetainedProgramState.normalizeSource
    (state : RetainedProgramState env U registry target strata P frontier goalFunction goalArgument goalOutput)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (sourceClosed : ∀ next ≤ env, P next) :
    ∃ terminal : RetainedProgramTerminal env U registry target strata P frontier goalFunction goalArgument goalOutput,
      terminal.readback = state.demand.readback state.right := by
  obtain terminal | ⟨next, smaller, readback⟩ := state.stepSource henv hscoped formed sourceClosed
  · exact terminal
  · obtain ⟨terminal, same⟩ := next.normalizeSource henv hscoped formed sourceClosed
    exact ⟨terminal, same.trans readback⟩
termination_by state.programSize

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
