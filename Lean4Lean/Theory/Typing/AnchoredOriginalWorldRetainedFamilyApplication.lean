import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRetainedFamilyTerminalEnrichment
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldQueryOperations

/-! Apply the actual controlled enlarged family plan to its original
argument query. Every observer and annotation is constructed together. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
open private raiseKey_admitted append_available from
  Lean4Lean.Theory.Typing.AnchoredOriginalRichGradedApplication
open private oneDomain_eq from
  Lean4Lean.Theory.Typing.AnchoredOriginalRetainedFamilyTerminalEnrichment
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000

private def observationCast
    {strata : EquationStratification env} {controls : OriginalWorldControls strata controlSource}
    {frontier : List (World strata.rules.length)}
    {query : RichObs sourceEnv env U registry target node locals σ (profile : Profile n) footprint}
    (equal : profile = next)
    (ready : ControlledStoredQuery controls frontier (.observation query)) :
    ControlledStoredQuery controls frontier (.observation (equal ▸ query)) := by
  cases equal
  exact ready

private theorem applicationWorld
    {strata : EquationStratification env}
    (controls : OriginalWorldControls strata controlSource)
    (frontier : List (World strata.rules.length))
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    {key : Key n} {output : Atom n}
    {functionNode : EndpointState sourceEnv U source f (.forallE A B)}
    {argumentNode : EndpointState sourceEnv U source a A}
    (domain : EndpointState sourceEnv U source A (.sort u))
    (codomain : EndpointState sourceEnv U (A :: source) B (.sort v))
    (resultNode : EndpointState sourceEnv U source (B.inst a) (.sort v))
    (hu : u.WF U) (hv : v.WF U)
    (function : RichGradedResult sourceEnv env U registry target functionNode locals σ available (Profile.fn key output))
    (argument : RichGradedResult sourceEnv env U registry target argumentNode locals σ available rawInput)
    (functionReady : ControlledStoredQuery controls frontier (.observation function.observation))
    (argumentReady : ControlledStoredQuery controls frontier (.observation argument.observation))
    (arguments : GeneralNormalProfileAdapter env U registry target rawInput key.input)
    (admitted : Admitted env U registry target key (a.subst σ) (a.subst σ)) :
    ∃ result : RichGradedResult sourceEnv env U registry target
        (.app hu hv domain codomain functionNode argumentNode resultNode) locals σ available (.singleton output),
      Nonempty (ControlledStoredQuery controls frontier (.observation result.observation)) := by
  let N := max function.rank (argument.rank + 1)
  have hN : 0 < N := by dsimp [N]; omega
  let M := N - 1
  have hNM : M + 1 = N := by dsimp [M]; omega
  have hfn : function.rank ≤ M + 1 := by dsimp [M, N]; omega
  have harg : argument.rank ≤ M := by dsimp [M, N]; omega
  have hn : n ≤ M := by have := function.bound; dsimp [M, N]; omega
  let hf := function.raiseTo henv hscoped formed (M + 1) hfn
  let ha := argument.raiseTo henv hscoped formed M harg
  obtain ⟨hfReady⟩ := functionReady.raise hfn
  obtain ⟨haReady⟩ := argumentReady.raise harg
  let highKey := raiseKey M hn key
  let highOutput := raiseAtom M hn output
  have functionAdapter : GeneralNormalProfileAdapter env U registry target hf.raw
      (Profile.fn highKey highOutput) := by
    have outer := (functionGradeView (env := env) (U := U) (registry := registry)
      (Γ := target) hn key output).toGeneralAdapter henv hscoped formed
    have h := hf.adapter
    change GeneralNormalProfileAdapter env U registry target hf.raw
      (raiseProfile (M + 1) (Nat.succ_le_succ hn) (.singleton (.fn key output))) at h
    rw [raiseProfile_singleton] at h
    exact GeneralProfileAdapter.comp h (.cons (List.mem_singleton_self _) outer (.nil _))
  have argumentAdapter : GeneralNormalProfileAdapter env U registry target ha.raw highKey.input :=
    GeneralProfileAdapter.comp ha.adapter
      (GeneralNormalProfileAdapter.raise henv hscoped formed hn arguments)
  obtain ⟨normal, member, ⟨adapter⟩⟩ := functionAdapter.origin (List.mem_singleton_self _)
  obtain ⟨original, originalMember, normalEq⟩ := List.mem_map.mp member
  subst normal
  obtain ⟨rawKey, rawOutput, normalOrigin, ⟨keys⟩, ⟨resultAdapter⟩⟩ := adapter.fn_inv
  have fixed : AdapterNormal.atom (n := M + 1) (.fn rawKey rawOutput) = .fn rawKey rawOutput := by
    rw [← normalOrigin, AdapterNormal.atom_idem]
  change AtomData.fn (AdapterNormal.key rawKey) (AdapterNormal.atom rawOutput) =
    AtomData.fn rawKey rawOutput at fixed
  have keyFixed := (AtomData.fn.inj fixed).1
  have outputFixed := (AtomData.fn.inj fixed).2
  have inputFixed : AdapterNormal.profile rawKey.input = rawKey.input := congrArg KeyData.input keyFixed
  let viewed := RichObs.view (RichObs.select hf.observation originalMember) (AdapterNormal.view henv original)
  let viewedReady : ControlledStoredQuery controls frontier (.observation viewed) := {
    annotation := .view (.select hfReady.annotation originalMember) _
    within := by simpa only [viewed, StoredOriginalQuery.headDepth, RichObs.headDepth, hf, RichGradedResult.raiseTo] using hfReady.within
    sponsored := hfReady.sponsored }
  obtain ⟨chosen, ⟨chosenReady⟩⟩ : ∃ chosen : RichObs sourceEnv env U registry target functionNode locals σ
      (Profile.fn rawKey rawOutput) hf.footprint,
      Nonempty (ControlledStoredQuery controls frontier (.observation chosen)) := by
    have profileEq : Profile.fn rawKey rawOutput = Profile.singleton (AdapterNormal.atom original) :=
      congrArg Profile.singleton normalOrigin.symm
    rw [profileEq]
    exact ⟨viewed, ⟨viewedReady⟩⟩
  have actualArguments : GeneralNormalProfileAdapter env U registry target ha.raw rawKey.input := by
    change GeneralProfileAdapter env U registry target (AdapterNormal.profile ha.raw) (AdapterNormal.profile rawKey.input)
    rw [inputFixed]
    exact GeneralProfileAdapter.comp argumentAdapter keys.arguments
  have resultAdapter' : GeneralNormalAtomAdapter env U registry target rawOutput highOutput := by
    change GeneralAtomAdapter env U registry target (AdapterNormal.atom rawOutput) (AdapterNormal.atom highOutput)
    rw [outputFixed]
    exact resultAdapter
  have rawLive := hf.live original originalMember
  have selectedLive := (AdapterNormal.view henv original).live henv hscoped formed rawLive
  rw [normalOrigin] at selectedLive
  have highAdmission : Admitted env U registry target highKey (a.subst σ) (a.subst σ) :=
    raiseKey_admitted hn henv admitted
  have actualAdmission := keys.pull henv hscoped formed selectedLive.1
    (AdapterNormal.normalizeAdmission henv hscoped formed highAdmission)
  let produced := RichObs.app (domain := domain) (body := codomain) (result := resultNode)
    hu hv chosen ha.observation actualArguments actualAdmission
  let producedReady : ControlledStoredQuery controls frontier (.observation produced) := {
    annotation := .app hu hv chosenReady.annotation haReady.annotation actualArguments actualAdmission
    within := by
      intro control active
      simpa only [produced, StoredOriginalQuery.headDepth, RichObs.headDepth, ha, RichGradedResult.raiseTo] using
        Nat.max_le.mpr ⟨chosenReady.within control active, haReady.within control active⟩
    sponsored := chosenReady.sponsored.merge haReady.sponsored }
  exact ⟨{
    rank := M
    bound := hn
    raw := .singleton rawOutput
    footprint := _
    observation := produced
    adapter := by
      rw [raiseProfile_singleton]
      exact .cons (List.mem_singleton_self _) resultAdapter' (.nil _)
    resources := append_available hf.resources ha.resources
    live := Profile.Live.singleton_iff.mpr selectedLive.2 }, ⟨producedReady⟩⟩

private theorem bareFamilyWorld
    {strata : EquationStratification env}
    (controls : OriginalWorldControls strata sourceEnv)
    (frontier : List (World strata.rules.length))
    (origin : ConstantHeaderOrigin sourceEnv name info)
    (lookup : env.constants name = some info)
    (notDefinition : registry.definitions name = none)
    (notNative : registry.natives name = none) (notQuotient : name ≠ ``Quot.lift)
    (seedWF : ∀ level ∈ seedLevels, level.WF U)
    (seedLength : seedLevels.length = info.uvars)
    (levelsWF : ∀ level ∈ levels, level.WF U)
    (equivalent : List.Forall₂ (· ≈ ·) seedLevels levels)
    (signature : ConstantTelescope (info.type.instL seedLevels))
    (typeClosed : info.type.Closed)
    (result : RichFamilyPlanResult env U registry target (origin.familyHeader seedWF).reference name seedLevels signature
      .nil (.ref (origin.familyHeader seedWF).reference) realization [] (fun _ => []) atom)
    (ready : result.WorldControlled controls frontier)
    (caller : EndpointState sourceEnv U source callerExpression callerAssigned)
    (captured : WorldEnvironmentProvenance strata U environment) (phase : RichPhase)
    (paid : Sponsored frontier [originalCallWorld controls phase caller captured])
    {node : EndpointState sourceEnv U source (.const name levels) assigned} :
    ∃ observation : RichObs sourceEnv env U registry target node locals σ (.singleton atom) [],
      Nonempty (ControlledStoredQuery controls frontier (.observation observation)) := by
  rcases result with ⟨footprint, plan, resources, support, typeFootprint, certificate, typeResources, typed⟩
  have footprintEmpty : footprint = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    rintro ⟨i, need⟩ member
    exact nomatch resources i need member
  have typeEmpty : typeFootprint = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    rintro ⟨i, need⟩ member
    exact nomatch typeResources i need member
  subst footprint
  subst typeFootprint
  let headerControls : OriginalWorldControls strata origin.source :=
    ⟨origin.ordered, controls.cutoff, controls.cutoffBound,
      controls.sourceCutoff.source_mono origin.sourceBelow, controls.fuel⟩
  let headerSite : WorldQuerySite (registry := registry) (target := target) strata
      (.ref (origin.familyHeader seedWF).reference) [] realization :=
    .empty headerControls (.ofLocation .here .nil) realization
  have headerBelow : WorldBelow strata.rules.length
      (originalCallWorld headerControls .fundamental (.ref (origin.familyHeader seedWF).reference) .nil)
      (originalCallWorld controls phase caller captured) := by
    apply Below.root (EquationControlMeasure.constantsDecrease (origin.count_lt controls.ordered) _ _ _ _ _)
    intro child member
    cases member
  have headerPaid : Sponsored frontier headerSite.worlds := by
    intro child member
    change child ∈ [originalCallWorld headerControls .fundamental (.ref (origin.familyHeader seedWF).reference) .nil] at member
    cases List.mem_singleton.mp member
    obtain ⟨sponsor, present, bound⟩ := paid _ (List.mem_singleton_self _)
    exact ⟨sponsor, present, EquationWorldClosureOrder.trans (r := @EquationControlMeasure.Less strata.rules.length) EquationControlMeasure.less_trans headerBelow bound⟩
  let observation : RichObs sourceEnv env U registry target node locals σ (.singleton atom) [] :=
    .family origin lookup notDefinition notNative notQuotient seedWF seedLength levelsWF equivalent
      signature typeClosed certificate typed plan
  let annotation : WorldObsProvenance strata observation :=
    .family origin lookup notDefinition notNative notQuotient seedWF seedLength levelsWF equivalent
      signature typeClosed certificate typed plan ready.code.annotation ready.plan headerSite
  refine ⟨observation, ⟨{ annotation := annotation, within := ?_, sponsored := ?_ }⟩⟩
  · intro control active
    simpa only [observation, StoredOriginalQuery.headDepth, RichObs.headDepth] using
      Nat.max_le.mpr ⟨ready.planWithin control active, ready.code.within control active⟩
  · exact (headerPaid.merge ready.code.sponsored).merge ready.planSponsored

private def ofCastWorld
    {strata : EquationStratification env}
    {controls : OriginalWorldControls strata controlSource}
    {frontier : List (World strata.rules.length)}
    {node : EndpointState sourceEnv U source expression assigned}
    (expressionEq : expression = nextExpression) (typeEq : assigned = nextType)
    {certificate : RichCert sourceEnv env U registry target (node.cast expressionEq typeEq)
      locals σ relevant profile footprint}
    (ready : ControlledStoredQuery controls frontier (.certificate certificate)) :
    ControlledStoredQuery controls frontier (.certificate (RichCert.ofCast expressionEq typeEq certificate)) := by
  cases expressionEq
  cases typeEq
  exact ready

/-- Rebuild the actual retained family application from the operative
captured entries. The result contains the enlarged request and its SAME
controlled original observer, with no semantic family-answer supplier. -/
theorem RetainedRichFamilySeed.oneParameterApplicationWorld
    {strata : EquationStratification env}
    (controls : OriginalWorldControls strata sourceEnv)
    (frontier : List (World strata.rules.length))
    {root : EndpointRef sourceEnv U source rootExpression rootType}
    (seed : RetainedRichFamilySeed root env registry target name levels)
    {sourceDomain : EndpointState sourceEnv U source A (.sort u)}
    {sourceBody : EndpointState sourceEnv U (A :: source) B (.sort v)}
    {function : EndpointState sourceEnv U source (.const name levels) (.forallE A B)}
    {argument : EndpointState sourceEnv U source a A}
    {result : EndpointState sourceEnv U source (B.inst a) (.sort v)}
    {headerDomain : EndpointRef seed.origin.source U [] C (.sort cu)}
    {headerBody : EndpointState seed.origin.source U [C] seed.signature.result (.sort dv)}
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    (henv : env.Ordered) (hscoped : registry.Scoped) (below : sourceEnv ≤ env)
    (formed : OnCtx target (env.IsType U))
    (hu : u.WF U) (hv : v.WF U) (hcu : cu.WF U) (hdv : dv.WF U)
    (domains : seed.signature.domains = [C])
    (resultSort : seed.signature.result = .sort level) (relevance : Relevant level relevant)
    (location : Located (seed.origin.familyHeader seed.seedWF).reference (.ref headerDomain))
    (lineage : location.contextDerivation .nil = .nil)
    (route : PrefixRoute seed.origin.source U [] (.forallE C seed.signature.result)
      ((EndpointState.ref (seed.origin.familyHeader seed.seedWF).reference).cast
        (oneDomain_eq seed.signature domains) rfl)
      (.pi hcu hdv (.ref headerDomain) headerBody))
    (entries : RichGroupedCapture (field := field) (major := major) headerDomain env registry target
      [] realization (fun _ => []) ownerInitial rawCapture leftValue rightValue)
    (entriesReady : ∀ entry ∈ entries, Nonempty (ControlledStoredQuery controls frontier
      (.certificate entry.answer.aligned.certificate)))
    (present : (⟨n, input⟩ : Need) ∈ entries.needs)
    (argumentQuery : RichGradedResult sourceEnv env U registry target argument locals σ available input)
    (argumentReady : ControlledStoredQuery controls frontier (.observation argumentQuery.observation))
    (anchorEq : leftValue = a.subst σ)
    (caller : EndpointState sourceEnv U source callerExpression callerAssigned)
    (captured : WorldEnvironmentProvenance strata U environment) (phase : RichPhase)
    (paid : Sponsored frontier [originalCallWorld controls phase caller captured]) :
    ∃ request : DataRequest (Profile n),
      request.input = input ∧ request.anchor = a.subst σ ∧
      (∃ entry ∈ entries, request.support.sortFlags = entry.answer.value.support.sortFlags) ∧
      RankedData.RequestAdmission env U (relations env U registry n) target request (a.subst σ) (a.subst σ) ∧
      ∃ query : RichGradedResult sourceEnv env U registry target
        (.app hu hv sourceDomain sourceBody function argument result) locals σ available
        (.singleton (n := n+1) (.family ⟨name, seed.seed, relevant, [request]⟩)),
        Nonempty (ControlledStoredQuery controls frontier (.observation query.observation)) := by
  obtain ⟨request, inputEq, requestAnchor, retainedSupport, admission, plan, ⟨planReady⟩⟩ :=
    entries.oneParameterPlanWorld controls frontier (header := (seed.origin.familyHeader seed.seedWF).reference)
      (signature := seed.signature) (name := name) (levels := seed.seed) (body := headerBody)
      henv below formed hcu hdv domains resultSort relevance location lineage entriesReady present
  let originalPlan := plan.restoreRoute route
  let originalReady : originalPlan.WorldControlled controls frontier := {
    plan := planReady.plan
    planWithin := planReady.planWithin
    planSponsored := planReady.planSponsored
    code := {
      annotation := .route route planReady.code.annotation
      within := by simpa only [originalPlan, RichFamilyPlanResult.restoreRoute,
        StoredOriginalQuery.headDepth, RichCert.headDepth] using planReady.code.within
      sponsored := planReady.code.sponsored } }
  let actualPlan : RichFamilyPlanResult env U registry target
      (seed.origin.familyHeader seed.seedWF).reference name seed.seed seed.signature .nil
      (.ref (seed.origin.familyHeader seed.seedWF).reference) realization [] (fun _ => [])
      (n := n+2) (.fn (Key.pad request.toKeyData) (.family ⟨name, seed.seed, relevant, [request]⟩)) :=
    { originalPlan with certificate := RichCert.ofCast (oneDomain_eq seed.signature domains) rfl originalPlan.certificate }
  let actualReady : actualPlan.WorldControlled controls frontier :=
    ⟨originalReady.plan, originalReady.planWithin, originalReady.planSponsored,
      ofCastWorld (oneDomain_eq seed.signature domains) rfl originalReady.code⟩
  obtain ⟨observation, ⟨observationReady⟩⟩ := bareFamilyWorld controls frontier seed.origin seed.lookup seed.notDefinition
    seed.notNative seed.notQuotient seed.seedWF seed.seedLength seed.levelsWF seed.equivalent seed.signature seed.typeClosed
    actualPlan actualReady caller captured phase paid (node := function) (locals := locals) (σ := σ)
  have admitted : Admitted env U registry target request.toKeyData leftValue leftValue :=
    ⟨admission.1, admission.2.1, request.support, admission.2.2.1, admission.2.2.2.1,
      admission.2.2.2.2.1, admission.2.2.2.2.2.1, admission.2.2.2.2.2.2⟩
  have padded := Admitted.pad henv admitted
  have anchorAdmitted : Admitted env U registry target (Key.pad request.toKeyData)
      (Key.pad request.toKeyData).anchor (Key.pad request.toKeyData).anchor := by
    simpa only [Key.pad, requestAnchor] using padded
  let functionQuery : RichGradedResult sourceEnv env U registry target function locals σ available
      (Profile.fn (Key.pad request.toKeyData) (.family ⟨name, seed.seed, relevant, [request]⟩)) := {
    rank := n+2
    bound := Nat.le_refl _
    raw := Profile.fn (Key.pad request.toKeyData) (.family ⟨name, seed.seed, relevant, [request]⟩)
    footprint := []
    observation := observation
    adapter := by rw [raiseProfile_self]; exact .refl _
    resources := fun _ _ impossible => nomatch impossible
    live := Profile.Live.singleton_iff.mpr ⟨anchorAdmitted, trivial⟩ }
  obtain ⟨argumentPadReady⟩ := argumentReady.raise (Nat.le_max_left argumentQuery.rank (n+1))
  obtain ⟨output, outputReady⟩ := applicationWorld controls frontier henv hscoped formed sourceDomain sourceBody result hu hv
    functionQuery (argumentQuery.pad henv hscoped formed) observationReady argumentPadReady
    (by change GeneralNormalProfileAdapter env U registry target input.pad request.input.pad
        rw [inputEq]; exact .refl _)
    (by simpa only [anchorEq] using padded)
  exact ⟨request, inputEq, requestAnchor.trans anchorEq, retainedSupport,
    (by simpa only [anchorEq] using admission), output, outputReady⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
