import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRetainedTermDomainDispatch
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRetainedTermLegacyBodyDispatch

/-! Exact typed domain-step dispatch over all retained rich and legacy leaves. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder EquationStratifiedFuel
open private appendTerminalPath from Lean4Lean.Theory.Typing.AnchoredOriginalWorldRetainedProgramApplication
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1800000

theorem richTermDomainProgramStepWitness
    {strata : EquationStratification env} {P : VEnv → Prop}
    {context : ContextDerivation sourceEnv U source}
    {node : EndpointState sourceEnv U source (.forallE A B) assigned}
    {controls : OriginalWorldControls strata sourceEnv}
    {frontier : List (World strata.rules.length)}
    {query : RichCert sourceEnv env U registry target node locals σ relevant profile footprint}
    (ready : ControlledStoredQuery controls frontier (.certificate query))
    (provenance : EndpointProvenance context node)
    (frame : OriginalRichFrame sourceEnv env U registry target context locals σ τ available)
    (captured : WorldEnvironmentProvenance strata U (frame.dependencyEnvironment controls.ordered))
    (data : WorldUnaryFrameData P controls frontier frame captured)
    (closed : available.AtomClosed) (formed : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (resources : footprint.Available available)
    (henv : env.Ordered) (hscoped : registry.Scoped) (sourceBelow : sourceEnv ≤ env)
    (sourceClosed : ∀ next ≤ env, P next)
    (paid : Sponsored frontier [originalCallWorld controls .fundamental node captured])
    (bank : WorldBoundedUnaryCallBank env U registry strata P
      (frontier ++ [originalCallWorld controls .fundamental node captured]))
    (selected : atom ∈ profile.atoms)
    {m : Nat} {result : Atom m} {support : Profile m} {table : List (Key m × Profile m)}
    (path : GeneralOutputPath env U registry target atom
      (show Atom (m+1) from .pi nextDomain nextBody support table))
    (member : result ∈ support.atoms)
    (continuation : RetainedTermDemand env U registry target goal goalOutput A result)
    (incomingDemand : RetainedTermDemand env U registry target goal goalOutput (.forallE A B) atom)
    (sameReadback : continuation.readback τ = incomingDemand.readback τ)
    (normalized : RetainedTermHeadNormalization env U registry target goal goalOutput
      incomingDemand (.domain path member continuation)) :
    let state := RetainedTermProgramState.ofRich ready provenance frame captured data closed substitutions
      resources sourceBelow paid bank incomingDemand selected
    ∃ next : RetainedTermProgramState env U registry target strata P frontier goal goalOutput,
      next.programSize < sizeOf (show WorldCertProvenance strata query from ready.annotation) ∧
      (Nonempty (RetainedTermDomainTransitionWitness state next) ∨ Nonempty (RetainedTermChargedTransitionWitness state next)) := by
  let demand := RetainedTermDemand.output path (.domain (B := B) member continuation)
  let state := RetainedTermProgramState.ofRich ready provenance frame captured data closed substitutions
    resources sourceBelow paid bank incomingDemand selected
  let budget : WorldPiDomainBudget strata := ⟨ready.annotation.worlds, fun policy => query.headDepth policy⟩
  obtain ⟨syntaxBudget, origin, annotation, worlds, rooted, smaller, depth⟩ :=
    ready.annotation.piProgramSelection provenance.location resources selected
      (budget := sizeOf (show WorldCertProvenance strata query from ready.annotation)) (Nat.le_refl _)
  rcases origin with ⟨rank, original, leaf, output, syntaxBound⟩
  dsimp only at annotation worlds rooted smaller depth
  cases leaf with
  | native hu hv domain guard rows supplied =>
    cases annotation with
    | native domainAnnotation rowsAnnotation =>
      obtain ⟨route⟩ := rooted
      obtain ⟨pending⟩ := GeneralOutputPath.pendingNativeDomain (appendTerminalPath output path)
      let domainReady := WorldPiProgramLeafProvenance.nativeDomainReady domainAnnotation rowsAnnotation ready worlds depth
      obtain ⟨next, bounded, witness⟩ := enterTermDomainProgramWitness state rfl route (.rich domain) (.rich domainAnnotation)
        domainReady.within domainReady.sponsored (fun i need hm => supplied i need (List.mem_append_left _ hm))
        (fun world hm => worlds (List.mem_append_left _ hm))
        (fun policy => Nat.le_trans (Nat.le_max_left _ _) (depth policy))
        (WorldPiProgramLeafProvenance.nativeDomainSize domainAnnotation rowsAnnotation smaller)
        pending path member continuation sameReadback normalized
      exact ⟨next, bounded, .inl witness⟩
  | legacyCode certificate supplied present =>
    cases annotation with
    | legacyCode child =>
      simp only [WorldPiProgramLeafProvenance.worlds, WorldPiProgramLeafProvenance.retainedSize, RichPiProgramLeaf.headDepth] at worlds smaller depth
      obtain ⟨selection⟩ := child.selectPiLeafSized (budget := budget) supplied _ (by simpa only [RichPiProgramLeaf.programSize] using syntaxBound)
        _ (Nat.le_of_lt smaller) (by exact worlds) (by exact depth) original present (appendTerminalPath output path)
      obtain ⟨next, bounded, witness⟩ := WorldLegacyPiLeafSelection.enterTermDomainWitness state rfl selection
        (piPrefix provenance.location).route ready.within ready.sponsored (fun _ h => h) (fun _ => Nat.le_refl _)
        path member continuation sameReadback normalized
      exact ⟨next, bounded, .inl witness⟩
  | legacyObs observation supplied present =>
    cases annotation with
    | legacyObs child =>
      simp only [WorldPiProgramLeafProvenance.worlds, WorldPiProgramLeafProvenance.retainedSize, RichPiProgramLeaf.headDepth] at worlds smaller depth
      obtain ⟨selection⟩ := child.selectPiLeafSized (budget := budget) supplied _ (by simpa only [RichPiProgramLeaf.programSize] using syntaxBound)
        _ (Nat.le_of_lt smaller) (by exact worlds) (by exact depth) original present (appendTerminalPath output path)
      obtain ⟨next, bounded, witness⟩ := WorldLegacyPiLeafSelection.enterTermDomainWitness state rfl selection
        (piPrefix provenance.location).route ready.within ready.sponsored (fun _ h => h) (fun _ => Nat.le_refl _)
        path member continuation sameReadback normalized
      exact ⟨next, bounded, .inl witness⟩
  | recipe recipe supplied present =>
    cases annotation with
    | recipe child =>
      simp only [WorldPiProgramLeafProvenance.worlds, WorldPiProgramLeafProvenance.retainedSize, RichPiProgramLeaf.headDepth] at worlds smaller depth
      obtain ⟨next, bounded, preserved, witness⟩ := state.openChargedWithWitness child (child.sourcesBelow sourceClosed)
        supplied (by exact worlds) (by exact depth) (by exact smaller)
        (.output output incomingDemand) present output rfl henv hscoped formed
      exact ⟨next, bounded, .inr witness⟩


theorem legacyTermDomainProgramStepWitness
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
    (continuation : RetainedTermDemand env U registry target goal goalOutput A result)
    (incomingDemand : RetainedTermDemand env U registry target goal goalOutput (.forallE A B) atom)
    (sameReadback : continuation.readback τ = incomingDemand.readback τ)
    (normalized : RetainedTermHeadNormalization env U registry target goal goalOutput
      incomingDemand (.domain path member continuation)) :
    let state := RetainedTermProgramState.ofLegacy annotation within sponsored provenance frame captured data closed substitutions
      resources sourceBelow paid bank incomingDemand selected
    ∃ next : RetainedTermProgramState env U registry target strata P frontier goal goalOutput,
      next.programSize < annotation.programSize ∧
      Nonempty (RetainedTermDomainTransitionWitness state next) := by
  let state := RetainedTermProgramState.ofLegacy annotation within sponsored provenance frame captured data closed substitutions
    resources sourceBelow paid bank incomingDemand selected
  let budget : WorldPiDomainBudget strata := ⟨annotation.certificate.worlds, fun policy => query.certificate.headDepth policy⟩
  cases annotation with
  | plain child =>
    obtain ⟨selection⟩ := child.selectPiLeafSized (budget := budget) resources _ (Nat.le_refl _) _ (Nat.le_refl _)
      (fun _ member => member) (by intro policy; simp only [budget, LegacyRowBody.certificate, SortableCert.headDepth]; exact Nat.le_refl _) atom selected path
    exact WorldLegacyPiLeafSelection.enterTermDomainWitness state rfl selection (piPrefix provenance.location).route
      within sponsored (fun _ h => h)
      (by intro policy; simp only [state, RetainedTermProgramState.ofLegacy, RetainedTypedProgram.certificate, RichCert.headDepth]; exact Nat.le_refl _)
      path member continuation sameReadback normalized
  | sortable child =>
    obtain ⟨selection⟩ := child.selectPiLeafSized (budget := budget) resources _ (Nat.le_refl _) _ (Nat.le_refl _)
      (fun _ member => member) (by intro policy; simp only [budget, LegacyRowBody.certificate, SortableCert.headDepth]; exact Nat.le_refl _) atom selected path
    exact WorldLegacyPiLeafSelection.enterTermDomainWitness state rfl selection (piPrefix provenance.location).route
      within sponsored (fun _ h => h)
      (by intro policy; simp only [state, RetainedTermProgramState.ofLegacy, RetainedTypedProgram.certificate, RichCert.headDepth]; exact Nat.le_refl _)
      path member continuation sameReadback normalized

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
