import Lean4Lean.Theory.Typing.AnchoredOriginalWorldGradedApplication
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldPiDomainPreservation
import Lean4Lean.Theory.Typing.AnchoredOriginalPiPrefix
import Lean4Lean.Theory.Typing.AnchoredFunctionDomain

/-! Select the actual function demand and its assigned-domain support together.
The grade adapter is retained, and domain alignment and the original domain
certificate use one and the same finite minimal support. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
open private raiseQueryAnnotation from Lean4Lean.Theory.Typing.AnchoredOriginalWorldRecipeVariableBodyCompile
open private Exposure.literalPi_domain exposureInsertion from Lean4Lean.Theory.Typing.AnchoredFunctionDomain
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1800000

structure RichFunctionDemandFactor
    (sourceEnv env : VEnv) (U : Nat) (registry : CanonicalHead.Registry) (target : List VExpr)
    {source : List VExpr} {expression assigned : VExpr}
    (node : EndpointState sourceEnv U source expression assigned)
    (locals : List Nat) (σ : Subst) (available : Valuation)
    (requestedKey : Key n) (requestedOutput : Atom n) where
  rank : Nat
  bound : n ≤ rank
  key : Key rank
  output : Atom rank
  footprint : Footprint
  observation : RichObs sourceEnv env U registry target node locals σ (Profile.fn key output) footprint
  resources : footprint.Available available
  keys : GeneralKeyProgram env U registry target key (AdapterNormal.key (raiseKey rank bound requestedKey))
  outputAdapter : GeneralNormalAtomAdapter env U registry target output (raiseAtom rank bound requestedOutput)
  live : Profile.Live env U registry target (Profile.fn key output)

/-- Factor the same raw observer before making the proper function call.
No argument query or admission is needed to identify its literal key. -/
theorem RichGradedResult.functionDemandWorld
    {strata : EquationStratification env}
    {controls : OriginalWorldControls strata controlSource}
    {frontier : List (World strata.rules.length)}
    {key : Key n} {output : Atom n}
    (query : RichGradedResult sourceEnv env U registry target node locals σ available (Profile.fn key output))
    (ready : ControlledStoredQuery controls frontier (.observation query.observation))
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U)) :
    ∃ factor : RichFunctionDemandFactor sourceEnv env U registry target node locals σ available key output,
    ∃ next : ControlledStoredQuery controls frontier (.observation factor.observation),
      next.annotation.worlds = ready.annotation.worlds ∧
      factor.footprint = query.footprint ∧
      ∀ policy, factor.observation.headDepth policy = query.observation.headDepth policy := by
  let N := query.rank - 1
  have high : query.rank ≤ N + 1 := by have := query.bound; dsimp [N]; omega
  have bound : n ≤ N := by have := query.bound; dsimp [N]; omega
  let raised := query.raiseTo henv hscoped formed (N+1) high
  have adapter : GeneralNormalProfileAdapter env U registry target raised.raw
      (Profile.fn (raiseKey N bound key) (raiseAtom N bound output)) := by
    have outer := (functionGradeView (env := env) (U := U) (registry := registry)
      (Γ := target) bound key output).toGeneralAdapter henv hscoped formed
    have previous := raised.adapter
    change GeneralNormalProfileAdapter env U registry target raised.raw
      (raiseProfile (N+1) (Nat.succ_le_succ bound) (.singleton (.fn key output))) at previous
    rw [raiseProfile_singleton] at previous
    exact GeneralProfileAdapter.comp previous (.cons (List.mem_singleton_self _) outer (.nil _))
  obtain ⟨normal, member, ⟨selected⟩⟩ := adapter.origin (List.mem_singleton_self _)
  obtain ⟨original, originalMember, normalEq⟩ := List.mem_map.mp member
  subst normal
  obtain ⟨actualKey, actualOutput, normalOrigin, ⟨keys⟩, ⟨result⟩⟩ := selected.fn_inv
  have fixed : AdapterNormal.atom (n := N+1) (.fn actualKey actualOutput) = .fn actualKey actualOutput := by
    rw [← normalOrigin, AdapterNormal.atom_idem]
  change AtomData.fn (AdapterNormal.key actualKey) (AdapterNormal.atom actualOutput) =
    AtomData.fn actualKey actualOutput at fixed
  have outputFixed := (AtomData.fn.inj fixed).2
  let profileEq := congrArg Profile.singleton normalOrigin
  let observed := RichObs.view (RichObs.select raised.observation originalMember) (AdapterNormal.view henv original)
  let observation := (congrArg (fun profile => RichObs sourceEnv env U registry target node locals σ
    profile query.footprint) profileEq).mp observed
  obtain ⟨raisedAnnotation, raisedWorlds⟩ := raiseQueryAnnotation query.observation ready.annotation high
  let annotation : WorldObsProvenance strata observation :=
    .castProfile profileEq (.view (.select raisedAnnotation originalMember) (AdapterNormal.view henv original))
  have selectedLive := (AdapterNormal.view henv original).live henv hscoped formed
    (raised.live original originalMember)
  rw [normalOrigin] at selectedLive
  let factor : RichFunctionDemandFactor sourceEnv env U registry target node locals σ available key output := {
    rank := N, bound := bound, key := actualKey, output := actualOutput
    footprint := query.footprint, observation := observation, resources := query.resources
    keys := keys, outputAdapter := by
      change GeneralAtomAdapter env U registry target (AdapterNormal.atom actualOutput)
        (AdapterNormal.atom (raiseAtom N bound output))
      rw [outputFixed]
      exact result
    live := Profile.Live.singleton_iff.mpr selectedLive }
  have depth : ∀ policy, factor.observation.headDepth policy = query.observation.headDepth policy := by
    intro policy
    change observation.headDepth policy = _
    dsimp only [observation]
    rw [RichObs.headDepth_mp policy rfl rfl profileEq rfl]
    simp only [observed, RichObs.headDepth, raised, RichGradedResult.raiseTo, RichObs.headDepth_raise]
  let next : ControlledStoredQuery controls frontier (.observation factor.observation) := {
    annotation := annotation
    within := fun control active => by
      change factor.observation.headDepth _ ≤ _
      rw [depth]
      exact ready.within control active
    sponsored := by
      change Sponsored frontier raisedAnnotation.worlds
      rw [raisedWorlds]
      exact ready.sponsored }
  refine ⟨factor, next, ?_, rfl, depth⟩
  change annotation.worlds = ready.annotation.worlds
  exact raisedWorlds

/-- One selected support controls both the raw domain alignment and the
syntactic domain extraction. Selection comes from the actual covering Pi row. -/
private theorem selectedDomainAlignment
    {support : Profile (n+1)} {domain : Profile n} {rows : List (Key n × Profile n)}
    {key : Key n}
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (whole : TypeRelated env U registry target (.forallE A B) (.forallE A B) support)
    (member : (.pi prototypeDomain prototypeBody domain rows) ∈ support.atoms)
    (rowMember : (key, result) ∈ rows)
    (inputTyped : key.input.HasType domain) :
    ∃ selected : Profile n, Minimal key.input selected ∧ selected ≤ domain ∧
      TypeConversion env U target key.domain A ∧
      TypeRelated env U registry target key.domain A selected := by
  obtain ⟨selected, basis⟩ := Basis.exists inputTyped
  have minimal := Basis.minimal basis
  obtain ⟨typed, bounded⟩ := Basis.valid basis
  have code := whole target .refl (.refl formed) (.pi prototypeDomain prototypeBody domain rows)
    (by simpa only [Profile.rename_refl] using member)
  simp only [lift'_refl] at code
  obtain ⟨display⟩ := code
  have domainEq := Exposure.literalPi_domain display.leftExposure
  have insertion := exposureInsertion henv display.leftExposure
  obtain ⟨localSupport, localTyped, _, _, raw, bridge⟩ := display.rowDomains key result rowMember
  have focused := TypeRelated.focusMinimal henv (minimal.rename display.map)
    (Profile.rename_le_iff.mpr bounded) (TypeRelated.left_diagonal display.domainRelated)
  have aligned := (focused.composeMinimal henv (minimal.rename display.map)
    localTyped (TypeRelated.symm henv localTyped.wf_type bridge)).symm henv
      ((Profile.rename_hasType_iff.mpr typed).wf_type)
  change TypeRelated env U registry display.context (key.domain.lift' display.map)
    display.leftDomain (selected.rename display.map) at aligned
  rw [domainEq] at aligned raw
  exact ⟨selected, minimal, bounded, insertion.pathBack henv raw,
    insertion.codeBack henv hscoped aligned⟩

/-- Consume the actual proper-F answer for the selected literal function.
The returned certificate is at the computed original Pi domain, and the
finite support types exactly this key's input, with its real raw alignment. -/
theorem RichSupportedValue.functionDomainWorld
    {strata : EquationStratification env}
    {controls : OriginalWorldControls strata controlSource}
    {frontier : List (World strata.rules.length)}
    {node : EndpointState sourceEnv U source function (.forallE A B)}
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    (location : Located root node)
    {key : Key n} {output : Atom n}
    (answer : RichSupportedValue sourceEnv env U registry target node locals σ τ available (Profile.fn key output))
    (ready : ControlledStoredQuery controls frontier (.certificate answer.certificate))
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U)) :
    let selectedPrefix := piPrefix (.assignedFormation location)
    ∃ support : Profile n,
    ∃ result : RichDomainCertificate env U registry target selectedPrefix.view.domain locals σ available support,
    ∃ resultReady : ControlledStoredQuery controls frontier (.certificate result.certificate),
      key.input.HasType support ∧ support.HasType (.sort true) ∧
      TypeConversion env U target key.domain (A.subst σ) ∧
      TypeRelated env U registry target key.domain (A.subst σ) support ∧
      resultReady.annotation.worlds ⊆ ready.annotation.worlds ∧
      ∀ policy, result.certificate.headDepth policy ≤ answer.certificate.headDepth policy := by
  let selectedPrefix := piPrefix (.assignedFormation location)
  obtain ⟨prototypeDomain, prototypeBody, domainSupport, rows, resultType,
    member, _wf, _keyWF, inputTyped, rowMember, _outputTyped⟩ :=
    answer.typed.fn_inv (List.mem_singleton_self _)
  have whole : TypeRelated env U registry target (.forallE (A.subst σ) (B.subst σ.lift))
      (.forallE (A.subst σ) (B.subst σ.lift)) answer.support := by
    simpa only [subst] using answer.typeCode
  obtain ⟨support, minimal, bounded, path, aligned⟩ :=
    selectedDomainAlignment henv hscoped formed whole member rowMember inputTyped
  let selected := RichCert.select answer.certificate member
  let selectedReady : ControlledStoredQuery controls frontier (.certificate selected) := {
    annotation := .select ready.annotation member
    within := fun control active => by
      simpa only [selected, StoredOriginalQuery.headDepth, RichCert.headDepth] using ready.within control active
    sponsored := ready.sponsored }
  obtain ⟨domain, domainReady, worlds, depth⟩ := selected.piDomain_controlled selectedPrefix.view.domainWF
    selectedPrefix.view.bodyWF selectedPrefix.route answer.resources selectedReady
  obtain ⟨footprint, certificate, annotation, resources, focusedWorlds, focusedDepth⟩ :=
    domain.certificate.codeAction_worlds_depth domainReady.annotation (.focusMinimal minimal bounded) domain.resources
  let result : RichDomainCertificate env U registry target selectedPrefix.view.domain locals σ available support :=
    ⟨footprint, certificate, resources⟩
  let next : ControlledStoredQuery controls frontier (.certificate result.certificate) := {
    annotation := annotation
    within := fun control active => Nat.le_trans (focusedDepth _) (domainReady.within control active)
    sponsored := fun world member => domainReady.sponsored world (focusedWorlds member) }
  exact ⟨support, result, next, minimal.typed, minimal.formation, path, aligned,
    (fun _ member => worlds (focusedWorlds member)),
    (fun policy => by
      have bounded := Nat.le_trans (focusedDepth policy) (depth policy)
      simpa only [selected, RichCert.headDepth] using bounded)⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
