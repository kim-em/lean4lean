import Lean4Lean.Theory.Typing.AnchoredOriginalTemplateComparison
import Lean4Lean.Theory.Typing.AnchoredOriginalRichCodeHeadDepth

/-! Binary template application at independent original occurrences. The two
functions may have different original Pi domains and codomains. The argument
bridge is typed raw equality, rather than equality of syntax. All output
syntax is reconstructed at the actual right application's own children. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open private append_available raiseKey_admitted from
  Lean4Lean.Theory.Typing.AnchoredOriginalRichGradedApplication
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
set_option maxRecDepth 4096

private theorem RichObs.headDepth_profileRec (current : Name → Nat → Nat)
    {α : Sort _} {a b : α} (equal : a = b) (profiles : α → Profile n)
    (query : RichObs sourceEnv env U registry target node locals σ (profiles a) footprint) :
    (equal ▸ query : RichObs sourceEnv env U registry target node locals σ (profiles b) footprint).headDepth current =
      query.headDepth current := by
  cases equal
  rfl

theorem RichObs.factor_application_headDepth
    (henv : env.Ordered)
    (functionObservation : RichObs sourceEnv env U registry Γ function locals σ
      (functionDemand : Profile (n + 1)) functionFootprint)
    (functionAdapter : GeneralNormalProfileAdapter env U registry Γ functionDemand
      (Profile.fn requestedKey requestedOutput))
    (argumentObservation : RichObs sourceEnv env U registry Γ argument locals σ
      (argumentDemand : Profile n) argumentFootprint)
    (argumentAdapter : GeneralNormalProfileAdapter env U registry Γ argumentDemand requestedKey.input) :
    ∃ factor : RichApplicationFactor sourceEnv env U registry Γ function argument locals σ
      requestedKey requestedOutput functionDemand argumentDemand functionFootprint argumentFootprint,
      (∀ current, factor.functionObservation.headDepth current = functionObservation.headDepth current) ∧
      (∀ current, factor.argumentObservation.headDepth current = argumentObservation.headDepth current) := by
  obtain ⟨normal, member, ⟨adapter⟩⟩ := functionAdapter.origin (List.mem_singleton_self _)
  obtain ⟨original, originalMember, normalEq⟩ := List.mem_map.mp member
  subst normal
  obtain ⟨key, output, normalOrigin, ⟨keys⟩, ⟨result⟩⟩ := adapter.fn_inv
  have fixed : AdapterNormal.atom (n := n + 1) (.fn key output) = .fn key output := by
    rw [← normalOrigin, AdapterNormal.atom_idem]
  change AtomData.fn (AdapterNormal.key key) (AdapterNormal.atom output) = AtomData.fn key output at fixed
  have keyFixed := (AtomData.fn.inj fixed).1
  have outputFixed := (AtomData.fn.inj fixed).2
  have inputFixed : AdapterNormal.profile key.input = key.input := congrArg KeyData.input keyFixed
  let selectedObservation := normalOrigin ▸ RichObs.view (RichObs.select functionObservation originalMember)
    (AdapterNormal.view henv original)
  have arguments : GeneralNormalProfileAdapter env U registry Γ argumentDemand key.input := by
    change GeneralProfileAdapter env U registry Γ (AdapterNormal.profile argumentDemand)
      (AdapterNormal.profile key.input)
    rw [inputFixed]
    exact GeneralProfileAdapter.comp argumentAdapter keys.arguments
  have result' : GeneralNormalAtomAdapter env U registry Γ output requestedOutput := by
    change GeneralAtomAdapter env U registry Γ (AdapterNormal.atom output) (AdapterNormal.atom requestedOutput)
    rw [outputFixed]
    exact result
  refine ⟨⟨key, output, original, originalMember, normalOrigin, selectedObservation,
    argumentObservation, arguments, keys, result'⟩, ?_, fun _ => rfl⟩
  intro current
  simpa only [RichObs.headDepth] using RichObs.headDepth_profileRec current normalOrigin Profile.singleton
    (RichObs.view (RichObs.select functionObservation originalMember) (AdapterNormal.view henv original))


theorem RichGradedResult.app_headDepth
    (henv : env.Ordered) (hscoped : registry.Scoped) (hΓ : OnCtx Γ (env.IsType U))
    (_closed : available.AtomClosed)
    {key : Key n} {output : Atom n}
    {functionNode : EndpointState sourceEnv U source f (.forallE A B)}
    {argumentNode : EndpointState sourceEnv U source a A}
    (domain : EndpointState sourceEnv U source A (.sort u))
    (codomain : EndpointState sourceEnv U (A :: source) B (.sort v))
    (resultNode : EndpointState sourceEnv U source (B.inst a) (.sort v))
    (hu : u.WF U) (hv : v.WF U)
    (function : RichGradedResult sourceEnv env U registry Γ functionNode locals σ available (Profile.fn key output))
    (argument : RichGradedResult sourceEnv env U registry Γ argumentNode locals σ available rawInput)
    (arguments : GeneralNormalProfileAdapter env U registry Γ rawInput key.input)
    (admitted : Admitted env U registry Γ key (a.subst σ) (a.subst σ)) :
    ∃ result : RichGradedResult sourceEnv env U registry Γ
      (.app hu hv domain codomain functionNode argumentNode resultNode) locals σ available (.singleton output),
      ∀ current, result.observation.headDepth current =
        max (function.observation.headDepth current) (argument.observation.headDepth current) := by
  let N := max function.rank (argument.rank + 1)
  have hN : 0 < N := by dsimp [N]; omega
  let M := N - 1
  have hNM : M + 1 = N := by dsimp [M]; omega
  have hfn : function.rank ≤ M + 1 := by dsimp [M, N]; omega
  have harg : argument.rank ≤ M := by dsimp [M, N]; omega
  have hn : n ≤ M := by have := function.bound; dsimp [M, N]; omega
  let hf := function.raiseTo henv hscoped hΓ (M + 1) hfn
  let ha := argument.raiseTo henv hscoped hΓ M harg
  let highKey := raiseKey M hn key
  let highOutput := raiseAtom M hn output
  have functionAdapter : GeneralNormalProfileAdapter env U registry Γ hf.raw
      (Profile.fn highKey highOutput) := by
    have outer := (functionGradeView (env := env) (U := U) (registry := registry)
      (Γ := Γ) hn key output).toGeneralAdapter henv hscoped hΓ
    have h := hf.adapter
    change GeneralNormalProfileAdapter env U registry Γ hf.raw
      (raiseProfile (M + 1) (Nat.succ_le_succ hn) (.singleton (.fn key output))) at h
    rw [raiseProfile_singleton] at h
    exact GeneralProfileAdapter.comp h (.cons (List.mem_singleton_self _) outer (.nil _))
  have argumentAdapter : GeneralNormalProfileAdapter env U registry Γ ha.raw highKey.input :=
    GeneralProfileAdapter.comp ha.adapter
      (GeneralNormalProfileAdapter.raise henv hscoped hΓ hn arguments)
  obtain ⟨factor, functionDepth, argumentDepth⟩ := RichObs.factor_application_headDepth henv hf.observation functionAdapter
    ha.observation argumentAdapter
  have rawLive := hf.live factor.rawOrigin factor.origin
  have selectedLive := (AdapterNormal.view henv factor.rawOrigin).live henv hscoped hΓ rawLive
  rw [factor.normalOrigin] at selectedLive
  have highAdmission : Admitted env U registry Γ highKey (a.subst σ) (a.subst σ) := by
    exact raiseKey_admitted hn henv admitted
  have actualAdmission := factor.keys.pull henv hscoped hΓ selectedLive.1
    (AdapterNormal.normalizeAdmission henv hscoped hΓ highAdmission)
  let produced := RichObs.app (domain := domain) (body := codomain) (result := resultNode) hu hv factor.functionObservation factor.argumentObservation
    factor.argumentAdapter actualAdmission
  have resultAdapter : GeneralNormalProfileAdapter env U registry Γ (.singleton factor.output)
      (raiseProfile M hn (.singleton output)) := by
    rw [raiseProfile_singleton]
    exact .cons (List.mem_singleton_self _) factor.outputAdapter (.nil _)
  refine ⟨{
    rank := M
    bound := hn
    raw := .singleton factor.output
    footprint := _
    observation := produced
    adapter := resultAdapter
    resources := append_available
      hf.resources ha.resources
    live := Profile.Live.singleton_iff.mpr selectedLive.2 }, ?_⟩
  intro current
  simp only [produced, RichObs.headDepth, functionDepth, argumentDepth,
    hf, ha, RichGradedResult.raiseTo, RichObs.headDepth_raise]


/-- The frozen left key is admitted by the right argument using the actual
paired child evidence. The right function's independent assigned Pi is not
identified with the left Pi. -/
theorem templateApplicationAdmissions
    {key : Key n} {output : Atom n}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (formed : OnCtx target (env.IsType U))
    (functionRelated : Related env U registry target f g (.forallE A B)
      (Profile.fn key output) functionSupport)
    (argumentRelated : Related env U registry target a b A rawInput argumentSupport)
    (arguments : GeneralNormalProfileAdapter env U registry target rawInput key.input)
    (argumentRaw : env.IsDefEq U target a b A)
    (admitted : Admitted env U registry target key a a) :
    Admitted env U registry target key a b ∧ Admitted env U registry target key b b := by
  obtain ⟨support, inputTyped, supportFormed, path, bridge⟩ :=
    functionRelated.fn_domain_alignment henv hscoped formed
  have sourceCode := (bridge.symm henv inputTyped.wf_type).left_diagonal
  have keyCode := bridge.left_diagonal
  have adapted := arguments.termMap henv hscoped formed inputTyped sourceCode argumentRelated
  have paired := Related.convert henv inputTyped (bridge.symm henv inputTyped.wf_type) adapted
  have pairedRaw := path.symm.cast argumentRaw
  obtain ⟨anchorRaw, _, _, _, _, _, anchor, _⟩ := admitted
  have anchor' := Related.retag henv inputTyped keyCode anchor
  have rightAnchor := Related.trans henv hscoped anchor' paired
  have rightSelf := (Related.symm henv rightAnchor).left_diagonal
  exact ⟨⟨anchorRaw, pairedRaw, support, inputTyped, supportFormed, keyCode, anchor', paired⟩,
    ⟨anchorRaw.trans pairedRaw, pairedRaw.hasType.2, support, inputTyped, supportFormed,
      keyCode, rightAnchor, rightSelf⟩⟩

/-- Rebuild the actual right application from the independently returned
children. Its original domain/codomain are `C`/`E`, while the paired value and
raw equality use the left original `A`/`B`. No whole assigned comparison or
literal equality between argument instantiations is an input. -/
theorem templateApplicationFromChildren
    {key : Key n} {output : Atom n}
    {leftFunction : EndpointState leftEnv U leftSource f (.forallE A B)}
    {leftArgument : EndpointState leftEnv U leftSource a A}
    {rightFunction : EndpointState rightEnv U rightSource g (.forallE C E)}
    {rightArgument : EndpointState rightEnv U rightSource b C}
    (leftDomain : EndpointState leftEnv U leftSource A (.sort leftDomainLevel))
    (leftBody : EndpointState leftEnv U (A :: leftSource) B (.sort leftBodyLevel))
    (leftResult : EndpointState leftEnv U leftSource (B.inst a) (.sort leftBodyLevel))
    (leftDomainWF : leftDomainLevel.WF U) (leftBodyWF : leftBodyLevel.WF U)
    (rightDomain : EndpointState rightEnv U rightSource C (.sort rightDomainLevel))
    (rightBody : EndpointState rightEnv U (C :: rightSource) E (.sort rightBodyLevel))
    (rightResult : EndpointState rightEnv U rightSource (E.inst b) (.sort rightBodyLevel))
    (rightDomainWF : rightDomainLevel.WF U) (rightBodyWF : rightBodyLevel.WF U)
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (formed : OnCtx target (env.IsType U)) (rightClosed : rightAvailable.AtomClosed)
    (sourceAnswer : RichSupportedValue leftEnv env U registry target
      (.app leftDomainWF leftBodyWF leftDomain leftBody leftFunction leftArgument leftResult)
      leftLocals σ σ leftAvailable (.singleton output))
    (functionRelated : Related env U registry target (f.subst σ) (g.subst τ)
      ((VExpr.forallE A B).subst σ) (Profile.fn key output) functionSupport)
    (argumentRelated : Related env U registry target (a.subst σ) (b.subst τ)
      (A.subst σ) rawInput argumentSupport)
    (functionRaw : env.IsDefEq U target (f.subst σ) (g.subst τ) ((VExpr.forallE A B).subst σ))
    (argumentRaw : env.IsDefEq U target (a.subst σ) (b.subst τ) (A.subst σ))
    (functionQuery : RichGradedResult rightEnv env U registry target rightFunction
      rightLocals τ rightAvailable (Profile.fn key output))
    (argumentQuery : RichGradedResult rightEnv env U registry target rightArgument
      rightLocals τ rightAvailable rawInput)
    (arguments : GeneralNormalProfileAdapter env U registry target rawInput key.input)
    (admitted : Admitted env U registry target key (a.subst σ) (a.subst σ)) :
    ∃ rightQuery : RichGradedResult rightEnv env U registry target
        (.app rightDomainWF rightBodyWF rightDomain rightBody rightFunction rightArgument rightResult)
        rightLocals τ rightAvailable (.singleton output),
      Related env U registry target ((VExpr.app f a).subst σ) ((VExpr.app g b).subst τ)
        ((B.inst a).subst σ) (.singleton output) sourceAnswer.support ∧
      env.IsDefEq U target ((VExpr.app f a).subst σ) ((VExpr.app g b).subst τ) ((B.inst a).subst σ) ∧
      ∀ policy, rightQuery.observation.headDepth policy =
        max (functionQuery.observation.headDepth policy) (argumentQuery.observation.headDepth policy) := by
  have functionPair : Related env U registry target (f.subst σ) (g.subst τ)
      (.forallE (A.subst σ) (B.subst σ.lift)) (Profile.fn key output) functionSupport := by
    simpa only [subst] using functionRelated
  obtain ⟨paired, rightAdmission⟩ := templateApplicationAdmissions henv hscoped formed
    functionPair argumentRelated arguments argumentRaw admitted
  obtain ⟨rightQuery, depth⟩ := RichGradedResult.app_headDepth henv hscoped formed rightClosed
    rightDomain rightBody rightResult rightDomainWF rightBodyWF
    functionQuery argumentQuery arguments rightAdmission
  refine ⟨rightQuery, ?_, ?_, depth⟩
  · simpa only [subst, subst_inst, inst_lift_cons] using
      Related.apply (B := B.subst σ.lift) henv hscoped formed sourceAnswer.typed
        (by simpa only [subst_inst, inst_lift_cons] using sourceAnswer.typeCode)
        functionPair paired
  · have functionRaw' : env.IsDefEq U target (f.subst σ) (g.subst τ)
        (.forallE (A.subst σ) (B.subst σ.lift)) := by
      simpa only [subst] using functionRaw
    simpa only [subst, subst_inst, inst_lift_cons] using IsDefEq.appDF functionRaw' argumentRaw

/-- The shared binary-template motive is closed under application. The
source support is the actual unary F answer at the left application; each
cross-template child result retains its own independent original endpoints.
No assigned-type path is inferred from the existence of those typings. -/
theorem TemplateComparisonResult.application
    {key : Key n} {output : Atom n}
    {leftFunction : EndpointState leftEnv U leftSource f (.forallE A B)}
    {leftArgument : EndpointState leftEnv U leftSource a A}
    {rightFunction : EndpointState rightEnv U rightSource g (.forallE C E)}
    {rightArgument : EndpointState rightEnv U rightSource b C}
    (leftDomain : EndpointState leftEnv U leftSource A (.sort leftDomainLevel))
    (leftBody : EndpointState leftEnv U (A :: leftSource) B (.sort leftBodyLevel))
    (leftResult : EndpointState leftEnv U leftSource (B.inst a) (.sort leftBodyLevel))
    (leftDomainWF : leftDomainLevel.WF U) (leftBodyWF : leftBodyLevel.WF U)
    (rightDomain : EndpointState rightEnv U rightSource C (.sort rightDomainLevel))
    (rightBody : EndpointState rightEnv U (C :: rightSource) E (.sort rightBodyLevel))
    (rightResult : EndpointState rightEnv U rightSource (E.inst b) (.sort rightBodyLevel))
    (rightDomainWF : rightDomainLevel.WF U) (rightBodyWF : rightBodyLevel.WF U)
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (formed : OnCtx target (env.IsType U)) (rightClosed : rightAvailable.AtomClosed)
    (sourceAnswer : RichSupportedValue leftEnv env U registry target
      (.app leftDomainWF leftBodyWF leftDomain leftBody leftFunction leftArgument leftResult)
      leftLocals σ σ leftAvailable (.singleton output))
    (functionAnswer : TemplateComparisonResult env U registry target leftFunction rightFunction
      leftLocals rightLocals σ τ leftAvailable rightAvailable (Profile.fn key output))
    (argumentAnswer : TemplateComparisonResult env U registry target leftArgument rightArgument
      leftLocals rightLocals σ τ leftAvailable rightAvailable rawInput)
    (arguments : GeneralNormalProfileAdapter env U registry target rawInput key.input)
    (admitted : Admitted env U registry target key (a.subst σ) (a.subst σ)) :
    ∃ answer : TemplateComparisonResult env U registry target
        (.app leftDomainWF leftBodyWF leftDomain leftBody leftFunction leftArgument leftResult)
        (.app rightDomainWF rightBodyWF rightDomain rightBody rightFunction rightArgument rightResult)
        leftLocals rightLocals σ τ leftAvailable rightAvailable (.singleton output),
      answer.source = sourceAnswer ∧
      ∀ policy, answer.rightQuery.observation.headDepth policy =
        max (functionAnswer.rightQuery.observation.headDepth policy)
          (argumentAnswer.rightQuery.observation.headDepth policy) := by
  obtain ⟨query, related, raw, depth⟩ := templateApplicationFromChildren
    leftDomain leftBody leftResult leftDomainWF leftBodyWF
    rightDomain rightBody rightResult rightDomainWF rightBodyWF
    henv hscoped formed rightClosed sourceAnswer functionAnswer.related argumentAnswer.related
    functionAnswer.raw argumentAnswer.raw functionAnswer.rightQuery argumentAnswer.rightQuery arguments admitted
  exact ⟨⟨sourceAnswer, related, raw, query⟩, rfl, depth⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
