import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRetainedProgramApplication
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRetainedBodyWitness
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRetainedChargedWitness
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldLegacyPiSizedSelection

/-! Joint body selection returns a typed edge retaining the SAME native or
legacy binder packet, or the full original charged opening. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder EquationStratifiedFuel
open private appendTerminalPath from Lean4Lean.Theory.Typing.AnchoredOriginalWorldRetainedProgramApplication
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1800000

theorem richBodyProgramStepWitness
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
    {m : Nat} {result : Atom m} {key : Key m} {anchor : VExpr} {resultProfile support : Profile m} {table : List (Key m × Profile m)}
    (path : GeneralOutputPath env U registry target atom
      (show Atom (m+1) from .pi nextDomain nextBody support table))
    (rowMember : (key, resultProfile) ∈ table)
    (admitted : Admitted env U registry target key anchor anchor)
    (member : result ∈ resultProfile.atoms)
    (continuation : RetainedApplicationDemand env U registry target goalFunction goalArgument goalOutput B result)
    (incomingDemand : RetainedApplicationDemand env U registry target goalFunction goalArgument goalOutput (.forallE A B) atom)
    (sameReadback : continuation.readback (τ.cons anchor) = incomingDemand.readback τ)
    (normalized : RetainedDemandHeadNormalization env U registry target goalFunction goalArgument goalOutput
      incomingDemand (.body path rowMember member anchor admitted continuation)) :
    let state := RetainedProgramState.ofRich ready provenance frame captured data closed substitutions
      resources sourceBelow paid bank incomingDemand selected
    ∃ next : RetainedProgramState env U registry target strata P frontier goalFunction goalArgument goalOutput,
      next.programSize < sizeOf (show WorldCertProvenance strata query from ready.annotation) ∧
      (Nonempty (RetainedBodyTransitionWitness state next) ∨ Nonempty (RetainedChargedTransitionWitness state next)) := by
  let demand := RetainedApplicationDemand.output path (.body (A := A) rowMember member anchor admitted continuation)
  let state := RetainedProgramState.ofRich ready provenance frame captured data closed substitutions
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
      obtain ⟨next, bounded, witness⟩ := enterNativeBodyStateWitness state rfl domainAnnotation rowsAnnotation supplied
        route (by exact worlds) (by exact depth) (by exact smaller)
        (appendTerminalPath output path) path rowMember admitted member continuation sameReadback normalized henv hscoped formed
      exact ⟨next, bounded, .inl witness⟩
  | legacyCode certificate supplied present =>
    cases annotation with
    | legacyCode child =>
      simp only [WorldPiProgramLeafProvenance.worlds, WorldPiProgramLeafProvenance.retainedSize, RichPiProgramLeaf.headDepth] at worlds smaller depth
      obtain ⟨selection⟩ := child.selectPiProgramSized (budget := budget) supplied _ (by simpa only [RichPiProgramLeaf.programSize] using syntaxBound)
        _ (Nat.le_of_lt smaller) (by exact worlds) (by exact depth) original present (appendTerminalPath output path) rowMember
      obtain ⟨⟨u, v, hu, hv, domainNode, bodyNode, location, prefixEq, cost⟩, route, locationEq⟩ := piPrefix provenance.location
      obtain ⟨domain, same⟩ := (route.locate provenance.location).originalDomains.1
      dsimp only at same route locationEq domain
      subst domainNode
      obtain ⟨next, bounded, witness⟩ := enterLegacyBodyStateWitness state rfl selection route ready.within ready.sponsored (fun _ h => h) (fun _ => Nat.le_refl _)
        path rowMember admitted member continuation sameReadback normalized henv hscoped formed
      exact ⟨next, bounded, .inl witness⟩
  | legacyObs observation supplied present =>
    cases annotation with
    | legacyObs child =>
      simp only [WorldPiProgramLeafProvenance.worlds, WorldPiProgramLeafProvenance.retainedSize, RichPiProgramLeaf.headDepth] at worlds smaller depth
      obtain ⟨selection⟩ := child.selectPiProgramSized (budget := budget) supplied _ (by simpa only [RichPiProgramLeaf.programSize] using syntaxBound)
        _ (Nat.le_of_lt smaller) (by exact worlds) (by exact depth) original present (appendTerminalPath output path) rowMember
      obtain ⟨⟨u, v, hu, hv, domainNode, bodyNode, location, prefixEq, cost⟩, route, locationEq⟩ := piPrefix provenance.location
      obtain ⟨domain, same⟩ := (route.locate provenance.location).originalDomains.1
      dsimp only at same route locationEq domain
      subst domainNode
      obtain ⟨next, bounded, witness⟩ := enterLegacyBodyStateWitness state rfl selection route ready.within ready.sponsored (fun _ h => h) (fun _ => Nat.le_refl _)
        path rowMember admitted member continuation sameReadback normalized henv hscoped formed
      exact ⟨next, bounded, .inl witness⟩
  | recipe recipe supplied present =>
    cases annotation with
    | recipe child =>
      simp only [WorldPiProgramLeafProvenance.worlds, WorldPiProgramLeafProvenance.retainedSize, RichPiProgramLeaf.headDepth] at worlds smaller depth
      obtain ⟨next, bounded, preserved, witness⟩ := state.openChargedWithWitness child (child.sourcesBelow sourceClosed)
        supplied (by exact worlds) (by exact depth) (by exact smaller)
        (.output output incomingDemand) present output rfl henv hscoped formed
      exact ⟨next, bounded, .inr witness⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
