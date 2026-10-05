import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRetainedProgramApplication
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRetainedProgramDomain
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRetainedLegacyDomainState
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRetainedReadbackOpening
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRetainedBodyState
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRetainedLegacyBodyState

/-! Execute a Pi demand by selecting a literal annotated native, legacy, or
charged program. Every result is strictly smaller than the input annotation. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder EquationStratifiedFuel
open private appendTerminalPath from Lean4Lean.Theory.Typing.AnchoredOriginalWorldRetainedProgramApplication
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1800000

theorem richDomainProgramStep
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
    (continuation : RetainedApplicationDemand env U registry target goalFunction goalArgument goalOutput A result) :
    ∃ next : RetainedProgramState env U registry target strata P frontier goalFunction goalArgument goalOutput,
      next.programSize < sizeOf (show WorldCertProvenance strata query from ready.annotation) ∧
      next.demand.readback next.right = continuation.readback τ := by
  let demand := RetainedApplicationDemand.output path (.domain (B := B) member continuation)
  let state := RetainedProgramState.ofRich ready provenance frame captured data closed substitutions
    resources sourceBelow paid bank demand selected
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
      exact enterNativeDomainProgramStateExact domainAnnotation rowsAnnotation supplied route provenance
        frame captured data ready worlds depth _ smaller closed substitutions sourceBelow paid bank
        (appendTerminalPath output path) member continuation
  | legacyCode certificate supplied present =>
    cases annotation with
    | legacyCode child =>
      simp only [WorldPiProgramLeafProvenance.worlds, WorldPiProgramLeafProvenance.retainedSize, RichPiProgramLeaf.headDepth] at worlds smaller depth
      obtain ⟨selection⟩ := child.selectPiLeafSized (budget := budget) supplied _ (by simpa only [RichPiProgramLeaf.programSize] using syntaxBound)
        _ (Nat.le_of_lt smaller) (by exact worlds) (by exact depth) original present (appendTerminalPath output path)
      exact selection.enterDomainProgramState (piPrefix provenance.location).route provenance frame captured data
        ready.within ready.sponsored closed substitutions sourceBelow paid bank member continuation
  | legacyObs observation supplied present =>
    cases annotation with
    | legacyObs child =>
      simp only [WorldPiProgramLeafProvenance.worlds, WorldPiProgramLeafProvenance.retainedSize, RichPiProgramLeaf.headDepth] at worlds smaller depth
      obtain ⟨selection⟩ := child.selectPiLeafSized (budget := budget) supplied _ (by simpa only [RichPiProgramLeaf.programSize] using syntaxBound)
        _ (Nat.le_of_lt smaller) (by exact worlds) (by exact depth) original present (appendTerminalPath output path)
      exact selection.enterDomainProgramState (piPrefix provenance.location).route provenance frame captured data
        ready.within ready.sponsored closed substitutions sourceBelow paid bank member continuation
  | recipe recipe supplied present =>
    cases annotation with
    | recipe child =>
      simp only [WorldPiProgramLeafProvenance.worlds, WorldPiProgramLeafProvenance.retainedSize, RichPiProgramLeaf.headDepth] at worlds smaller depth
      exact state.openChargedReadback child (child.sourcesBelow sourceClosed) supplied (by exact worlds) (by exact depth) (by exact smaller)
        (.output output demand) present henv hscoped formed


theorem richBodyProgramStep
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
    (continuation : RetainedApplicationDemand env U registry target goalFunction goalArgument goalOutput B result) :
    ∃ next : RetainedProgramState env U registry target strata P frontier goalFunction goalArgument goalOutput,
      next.programSize < sizeOf (show WorldCertProvenance strata query from ready.annotation) ∧
      next.demand.readback next.right = continuation.readback (τ.cons anchor) := by
  let demand := RetainedApplicationDemand.output path (.body (A := A) rowMember member anchor admitted continuation)
  let state := RetainedProgramState.ofRich ready provenance frame captured data closed substitutions
    resources sourceBelow paid bank demand selected
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
      exact enterNativeBodyProgramState domainAnnotation rowsAnnotation supplied route provenance
        frame captured data ready worlds depth _ smaller closed formed substitutions henv hscoped sourceBelow paid bank
        (appendTerminalPath output path) rowMember admitted member continuation
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
      exact selection.enterBodyProgramState route provenance frame captured data
        ready.within ready.sponsored closed formed substitutions henv hscoped sourceBelow paid bank admitted continuation member
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
      exact selection.enterBodyProgramState route provenance frame captured data
        ready.within ready.sponsored closed formed substitutions henv hscoped sourceBelow paid bank admitted continuation member
  | recipe recipe supplied present =>
    cases annotation with
    | recipe child =>
      simp only [WorldPiProgramLeafProvenance.worlds, WorldPiProgramLeafProvenance.retainedSize, RichPiProgramLeaf.headDepth] at worlds smaller depth
      exact state.openChargedReadback child (child.sourcesBelow sourceClosed) supplied (by exact worlds) (by exact depth) (by exact smaller)
        (.output output demand) present henv hscoped formed

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
