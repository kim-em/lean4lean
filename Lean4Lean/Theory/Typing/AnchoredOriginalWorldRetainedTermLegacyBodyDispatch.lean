import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRetainedTermBodyWitness

/-! Raw legacy programs keep their annotation measure and retain the actual
selected binder transition; no Rich wrapping is used as recursive input. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder EquationStratifiedFuel
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1800000

noncomputable def RetainedTermProgramState.ofLegacy
    {sourceEnv : VEnv} {source : List VExpr} {expression assigned : VExpr}
    {locals : List Nat} {σ τ : Subst} {available : Valuation}
    {relevant : Bool} {n : Nat} {profile : Profile n} {footprint : Footprint} {atom : Atom n}
    {strata : EquationStratification env} {P : VEnv → Prop}
    {context : ContextDerivation sourceEnv U source}
    {node : EndpointState sourceEnv U source expression assigned}
    {controls : OriginalWorldControls strata sourceEnv}
    {frontier : List (World strata.rules.length)}
    {query : LegacyRowBody env U registry target locals σ expression relevant profile footprint}
    (annotation : WorldLegacyRowBodyProvenance strata query)
    (within : WithinAbove controls.cutoff controls.fuel
      (fun control => query.certificate.headDepth (stratifiedHeadPolicy (strata.headOrdinal registry) control)))
    (sponsored : Sponsored frontier annotation.certificate.worlds)
    (provenance : EndpointProvenance context node)
    (frame : OriginalRichFrame sourceEnv env U registry target context locals σ τ available)
    (captured : WorldEnvironmentProvenance strata U (frame.dependencyEnvironment controls.ordered))
    (data : WorldUnaryFrameData P controls frontier frame captured)
    (closed : available.AtomClosed) (substitutions : Ctx.SubstEq env U target σ τ source)
    (resources : footprint.Available available) (sourceBelow : sourceEnv ≤ env)
    (paid : Sponsored frontier [originalCallWorld controls .fundamental node captured])
    (bank : WorldBoundedUnaryCallBank env U registry strata P
      (frontier ++ [originalCallWorld controls .fundamental node captured]))
    (demand : RetainedTermDemand env U registry target goal goalOutput expression atom)
    (member : atom ∈ profile.atoms) :
    RetainedTermProgramState env U registry target strata P frontier goal goalOutput := {
  sourceEnv := sourceEnv, source := source, context := context, expression := expression, assigned := assigned
  node := node, provenance := provenance, controls := controls
  locals := locals, left := σ, right := τ, available := available
  frame := frame, captured := captured, data := data
  closed := closed, substitutions := substitutions, sourceBelow := sourceBelow
  relevant := relevant, rank := _, profile := profile, footprint := footprint
  program := .legacy query, annotation := .legacy annotation
  within := by simpa only [RetainedTypedProgram.certificate, RichCert.stratifiedDepth, RichCert.headDepth] using within
  sponsored := sponsored, resources := resources
  selected := atom, member := member, demand := demand, paid := paid, bank := bank }

theorem legacyTermBodyProgramStepWitness
    {strata : EquationStratification env} {P : VEnv → Prop}
    {context : ContextDerivation sourceEnv U source}
    {node : EndpointState sourceEnv U source (.forallE A B) assigned}
    {controls : OriginalWorldControls strata sourceEnv}
    {frontier : List (World strata.rules.length)}
    {query : LegacyRowBody env U registry target locals σ (.forallE A B) relevant profile footprint}
    (annotation : WorldLegacyRowBodyProvenance strata query)
    (within : WithinAbove controls.cutoff controls.fuel
      (fun control => query.certificate.headDepth (stratifiedHeadPolicy (strata.headOrdinal registry) control)))
    (sponsored : Sponsored frontier annotation.certificate.worlds)
    (provenance : EndpointProvenance context node)
    (frame : OriginalRichFrame sourceEnv env U registry target context locals σ τ available)
    (captured : WorldEnvironmentProvenance strata U (frame.dependencyEnvironment controls.ordered))
    (data : WorldUnaryFrameData P controls frontier frame captured)
    (closed : available.AtomClosed) (formed : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (resources : footprint.Available available)
    (henv : env.Ordered) (hscoped : registry.Scoped) (sourceBelow : sourceEnv ≤ env)
    (paid : Sponsored frontier [originalCallWorld controls .fundamental node captured])
    (bank : WorldBoundedUnaryCallBank env U registry strata P
      (frontier ++ [originalCallWorld controls .fundamental node captured]))
    (selected : atom ∈ profile.atoms)
    {m : Nat} {result : Atom m} {key : Key m} {anchor : VExpr} {resultProfile support : Profile m} {table : List (Key m × Profile m)}
    (path : GeneralOutputPath env U registry target atom
      (show Atom (m+1) from .pi nextDomain nextBody support table))
    (rowMember : (key, resultProfile) ∈ table)
    (admitted : Admitted env U registry target key anchor anchor)
    (member : result ∈ resultProfile.atoms)
    (continuation : RetainedTermDemand env U registry target goal goalOutput B result)
    (incomingDemand : RetainedTermDemand env U registry target goal goalOutput (.forallE A B) atom)
    (sameReadback : continuation.readback (τ.cons anchor) = incomingDemand.readback τ)
    (normalized : RetainedTermHeadNormalization env U registry target goal goalOutput
      incomingDemand (.body path rowMember member anchor admitted continuation)) :
    let state := RetainedTermProgramState.ofLegacy annotation within sponsored provenance frame captured data closed substitutions
      resources sourceBelow paid bank incomingDemand selected
    ∃ next : RetainedTermProgramState env U registry target strata P frontier goal goalOutput,
      next.programSize < annotation.programSize ∧
      Nonempty (RetainedTermBodyTransitionWitness state next) := by
  let state := RetainedTermProgramState.ofLegacy annotation within sponsored provenance frame captured data closed substitutions
    resources sourceBelow paid bank incomingDemand selected
  let budget : WorldPiDomainBudget strata := ⟨annotation.certificate.worlds, fun policy => query.certificate.headDepth policy⟩
  cases annotation with
  | plain child =>
    obtain ⟨selection⟩ := child.selectPiProgramSized (budget := budget) resources _ (Nat.le_refl _) _ (Nat.le_refl _)
      (fun _ member => member) (by intro policy; simp only [budget, LegacyRowBody.certificate, SortableCert.headDepth]; exact Nat.le_refl _) atom selected path rowMember
    obtain ⟨⟨u, v, hu, hv, domainNode, bodyNode, location, prefixEq, cost⟩, route, locationEq⟩ := piPrefix provenance.location
    obtain ⟨domain, same⟩ := (route.locate provenance.location).originalDomains.1
    dsimp only at same route locationEq domain
    subst domainNode
    exact enterLegacyTermBodyStateWitness state rfl selection route within sponsored (fun _ h => h) (by intro policy; simp only [state, RetainedTermProgramState.ofLegacy, RetainedTypedProgram.certificate, RichCert.headDepth]; exact Nat.le_refl _)
      path rowMember admitted member continuation sameReadback normalized henv hscoped formed
  | sortable child =>
    obtain ⟨selection⟩ := child.selectPiProgramSized (budget := budget) resources _ (Nat.le_refl _) _ (Nat.le_refl _)
      (fun _ member => member) (by intro policy; simp only [budget, LegacyRowBody.certificate, SortableCert.headDepth]; exact Nat.le_refl _) atom selected path rowMember
    obtain ⟨⟨u, v, hu, hv, domainNode, bodyNode, location, prefixEq, cost⟩, route, locationEq⟩ := piPrefix provenance.location
    obtain ⟨domain, same⟩ := (route.locate provenance.location).originalDomains.1
    dsimp only at same route locationEq domain
    subst domainNode
    exact enterLegacyTermBodyStateWitness state rfl selection route within sponsored (fun _ h => h) (by intro policy; simp only [state, RetainedTermProgramState.ofLegacy, RetainedTypedProgram.certificate, RichCert.headDepth]; exact Nat.le_refl _)
      path rowMember admitted member continuation sameReadback normalized henv hscoped formed

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
