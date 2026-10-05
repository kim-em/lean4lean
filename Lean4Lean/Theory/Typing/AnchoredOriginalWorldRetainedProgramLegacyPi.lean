import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRetainedLegacyDomainState
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRetainedLegacyBodyState

/-! Execute raw plain/sortable legacy Pi instructions directly, retaining the
raw annotation measure rather than measuring Rich attachment wrappers. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder EquationStratifiedFuel
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1800000

theorem legacyDomainProgramStep
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
    {m : Nat} {result : Atom m} {support : Profile m} {table : List (Key m × Profile m)}
    (path : GeneralOutputPath env U registry target atom
      (show Atom (m+1) from .pi nextDomain nextBody support table))
    (member : result ∈ support.atoms)
    (continuation : RetainedApplicationDemand env U registry target goalFunction goalArgument goalOutput A result) :
    ∃ next : RetainedProgramState env U registry target strata P frontier goalFunction goalArgument goalOutput,
      next.programSize < annotation.programSize ∧
      next.demand.readback next.right = continuation.readback τ := by
  let budget : WorldPiDomainBudget strata := ⟨annotation.certificate.worlds, fun policy => query.certificate.headDepth policy⟩
  cases annotation with
  | plain child =>
    obtain ⟨selection⟩ := child.selectPiLeafSized (budget := budget) resources _ (Nat.le_refl _) _ (Nat.le_refl _)
      (fun _ member => member) (by intro policy; simp only [budget, LegacyRowBody.certificate, SortableCert.headDepth]; exact Nat.le_refl _) atom selected path
    exact selection.enterDomainProgramState (piPrefix provenance.location).route provenance frame captured data
      within sponsored closed substitutions sourceBelow paid bank member continuation
  | sortable child =>
    obtain ⟨selection⟩ := child.selectPiLeafSized (budget := budget) resources _ (Nat.le_refl _) _ (Nat.le_refl _)
      (fun _ member => member) (by intro policy; simp only [budget, LegacyRowBody.certificate, SortableCert.headDepth]; exact Nat.le_refl _) atom selected path
    exact selection.enterDomainProgramState (piPrefix provenance.location).route provenance frame captured data
      within sponsored closed substitutions sourceBelow paid bank member continuation

theorem legacyBodyProgramStep
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
    (continuation : RetainedApplicationDemand env U registry target goalFunction goalArgument goalOutput B result) :
    ∃ next : RetainedProgramState env U registry target strata P frontier goalFunction goalArgument goalOutput,
      next.programSize < annotation.programSize ∧
      next.demand.readback next.right = continuation.readback (τ.cons anchor) := by
  let budget : WorldPiDomainBudget strata := ⟨annotation.certificate.worlds, fun policy => query.certificate.headDepth policy⟩
  cases annotation with
  | plain child =>
    obtain ⟨selection⟩ := child.selectPiProgramSized (budget := budget) resources _ (Nat.le_refl _) _ (Nat.le_refl _)
      (fun _ member => member) (by intro policy; simp only [budget, LegacyRowBody.certificate, SortableCert.headDepth]; exact Nat.le_refl _) atom selected path rowMember
    obtain ⟨⟨u, v, hu, hv, domainNode, bodyNode, location, prefixEq, cost⟩, route, locationEq⟩ := piPrefix provenance.location
    obtain ⟨domain, same⟩ := (route.locate provenance.location).originalDomains.1
    dsimp only at same route locationEq domain
    subst domainNode
    exact selection.enterBodyProgramState route provenance frame captured data
      within sponsored closed formed substitutions henv hscoped sourceBelow paid bank admitted continuation member
  | sortable child =>
    obtain ⟨selection⟩ := child.selectPiProgramSized (budget := budget) resources _ (Nat.le_refl _) _ (Nat.le_refl _)
      (fun _ member => member) (by intro policy; simp only [budget, LegacyRowBody.certificate, SortableCert.headDepth]; exact Nat.le_refl _) atom selected path rowMember
    obtain ⟨⟨u, v, hu, hv, domainNode, bodyNode, location, prefixEq, cost⟩, route, locationEq⟩ := piPrefix provenance.location
    obtain ⟨domain, same⟩ := (route.locate provenance.location).originalDomains.1
    dsimp only at same route locationEq domain
    subst domainNode
    exact selection.enterBodyProgramState route provenance frame captured data
      within sponsored closed formed substitutions henv hscoped sourceBelow paid bank admitted continuation member

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
