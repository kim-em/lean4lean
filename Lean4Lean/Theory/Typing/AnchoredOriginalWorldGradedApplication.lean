import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRecipeApplicationCompile
import Lean4Lean.Theory.Typing.AnchoredOriginalTemplateApplication

/-! Consume the actual graded function returned by lower equality. The raw
function profile is factored with its real General adapter; it is never
identified with the requested function profile. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
open private append_available raiseKey_admitted from Lean4Lean.Theory.Typing.AnchoredOriginalRichGradedApplication
open private raiseQueryAnnotation from Lean4Lean.Theory.Typing.AnchoredOriginalWorldRecipeVariableBodyCompile
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1200000

theorem RichObs.factor_application_annotated
    {strata : EquationStratification env}
    (henv : env.Ordered)
    (functionObservation : RichObs sourceEnv env U registry Γ function locals σ
      (functionDemand : Profile (n + 1)) functionFootprint)
    (functionAdapter : GeneralNormalProfileAdapter env U registry Γ functionDemand
      (Profile.fn requestedKey requestedOutput))
    (argumentObservation : RichObs sourceEnv env U registry Γ argument locals σ
      (argumentDemand : Profile n) argumentFootprint)
    (argumentAdapter : GeneralNormalProfileAdapter env U registry Γ argumentDemand requestedKey.input)
    (functionAnnotation : WorldObsProvenance strata functionObservation)
    (argumentAnnotation : WorldObsProvenance strata argumentObservation) :
    ∃ factor : RichApplicationFactor sourceEnv env U registry Γ function argument locals σ
      requestedKey requestedOutput functionDemand argumentDemand functionFootprint argumentFootprint,
      ∃ fnAnnotation : WorldObsProvenance strata factor.functionObservation,
      ∃ argAnnotation : WorldObsProvenance strata factor.argumentObservation,
      fnAnnotation.worlds = functionAnnotation.worlds ∧
      argAnnotation.worlds = argumentAnnotation.worlds ∧
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
  let profileEq := congrArg Profile.singleton normalOrigin
  let selected := RichObs.view (RichObs.select functionObservation originalMember)
    (AdapterNormal.view henv original)
  let selectedObservation := (congrArg (fun p => RichObs sourceEnv env U registry Γ function
    locals σ p functionFootprint) profileEq).mp selected
  let selectedAnnotation : WorldObsProvenance strata selectedObservation :=
    .castProfile profileEq (.view (.select functionAnnotation originalMember) (AdapterNormal.view henv original))
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
    argumentObservation, arguments, keys, result'⟩, selectedAnnotation, argumentAnnotation,
    rfl, rfl, ?_, fun _ => rfl⟩
  intro current
  dsimp only [selectedObservation]
  rw [RichObs.headDepth_mp current rfl rfl profileEq rfl]
  simp only [selected, RichObs.headDepth]



/-- The literal operands selected by graded application factorization.
The directional output adapter is retained; no physical origin is selected
again from the existential output certificate. -/
structure RichApplicationOperandFactor
    (env : VEnv) (registry : CanonicalHead.Registry) (target : List VExpr)
    (functionNode : EndpointState sourceEnv U source f (.forallE A B))
    (argumentNode : EndpointState sourceEnv U source a A)
    (locals : List Nat) (σ : Subst) (available : Valuation) (requested : Atom n) where
  rank : Nat
  bound : n ≤ rank
  key : Key rank
  output : Atom rank
  functionFootprint : Footprint
  argumentFootprint : Footprint
  function : RichObs sourceEnv env U registry target functionNode locals σ (Profile.fn key output) functionFootprint
  rawInput : Profile rank
  argument : RichObs sourceEnv env U registry target argumentNode locals σ rawInput argumentFootprint
  arguments : GeneralNormalProfileAdapter env U registry target rawInput key.input
  admitted : Admitted env U registry target key (a.subst σ) (a.subst σ)
  outputAdapter : GeneralNormalAtomAdapter env U registry target output (raiseAtom rank bound requested)
  resources : (functionFootprint ++ argumentFootprint).Available available
  live : Profile.Live env U registry target (Profile.singleton output)

/-- Attach the already selected literal operands to their actual caller
application occurrence. This performs no new query traversal or choice. -/
def RichApplicationOperandFactor.origin
    {functionNode : EndpointState sourceEnv U source f (.forallE A B)}
    {argumentNode : EndpointState sourceEnv U source a A}
    (factor : RichApplicationOperandFactor env registry target functionNode argumentNode locals σ available requested)
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {domain : EndpointState sourceEnv U source A (.sort u)}
    {body : EndpointState sourceEnv U (A :: source) B (.sort v)}
    {result : EndpointState sourceEnv U source (B.inst a) (.sort v)}
    {hu : u.WF U} {hv : v.WF U}
    (location : Located root (.app hu hv domain body functionNode argumentNode result)) :
    RichAppOrigin root env registry target source locals σ f a :=
  ⟨A, B, u, v, hu, hv, domain, body, functionNode, argumentNode, result, location,
    factor.rank, factor.key, factor.output, factor.functionFootprint, factor.argumentFootprint,
    factor.function, factor.rawInput, factor.argument, factor.arguments, factor.admitted⟩

noncomputable def RichApplicationOperandFactor.graded
    {functionNode : EndpointState sourceEnv U source f (.forallE A B)}
    {argumentNode : EndpointState sourceEnv U source a A}
    (factor : RichApplicationOperandFactor env registry target functionNode argumentNode locals σ available requested)
    (domain : EndpointState sourceEnv U source A (.sort u))
    (body : EndpointState sourceEnv U (A :: source) B (.sort v))
    (result : EndpointState sourceEnv U source (B.inst a) (.sort v))
    (hu : u.WF U) (hv : v.WF U) :
    RichGradedResult sourceEnv env U registry target
      (.app hu hv domain body functionNode argumentNode result) locals σ available (.singleton requested) where
  rank := factor.rank
  bound := factor.bound
  raw := .singleton factor.output
  footprint := factor.functionFootprint ++ factor.argumentFootprint
  observation := .app hu hv factor.function factor.argument factor.arguments factor.admitted
  adapter := by
    rw [raiseProfile_singleton]
    exact .cons (List.mem_singleton_self _) factor.outputAdapter (.nil _)
  resources := factor.resources
  live := factor.live

structure RichApplicationOperandFactor.Controlled
    {strata : EquationStratification env}
    (factor : RichApplicationOperandFactor env registry target functionNode argumentNode locals σ available requested)
    (controls : OriginalWorldControls strata controlSource)
    (frontier : List (EquationWorldClosureOrder.World strata.rules.length)) where
  function : ControlledStoredQuery controls frontier (.observation factor.function)
  argument : ControlledStoredQuery controls frontier (.observation factor.argument)

def RichApplicationOperandFactor.Controlled.graded
    {strata : EquationStratification env}
    {functionNode : EndpointState sourceEnv U source f (.forallE A B)}
    {argumentNode : EndpointState sourceEnv U source a A}
    {factor : RichApplicationOperandFactor env registry target functionNode argumentNode locals σ available requested}
    {controls : OriginalWorldControls strata controlSource}
    {frontier : List (EquationWorldClosureOrder.World strata.rules.length)}
    (ready : factor.Controlled controls frontier)
    (domain : EndpointState sourceEnv U source A (.sort u))
    (body : EndpointState sourceEnv U (A :: source) B (.sort v))
    (result : EndpointState sourceEnv U source (B.inst a) (.sort v))
    (hu : u.WF U) (hv : v.WF U) :
    ControlledStoredQuery controls frontier (.observation (factor.graded domain body result hu hv).observation) where
  annotation := .app hu hv ready.function.annotation ready.argument.annotation factor.arguments factor.admitted
  within := by
    intro control active
    simpa only [RichApplicationOperandFactor.graded, StoredOriginalQuery.headDepth, RichObs.headDepth] using
      Nat.max_le.mpr ⟨ready.function.within control active, ready.argument.within control active⟩
  sponsored := by
    intro world member
    exact (List.mem_append.mp member).elim (ready.function.sponsored world) (ready.argument.sponsored world)


theorem RichGradedResult.appOperandsAnnotated
    {strata : EquationStratification env}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hΓ : OnCtx Γ (env.IsType U))
    (_closed : available.AtomClosed)
    {key : Key n} {output : Atom n}
    {functionNode : EndpointState sourceEnv U source f (.forallE A B)}
    {argumentNode : EndpointState sourceEnv U source a A}
    (_domain : EndpointState sourceEnv U source A (.sort u))
    (_codomain : EndpointState sourceEnv U (A :: source) B (.sort v))
    (_resultNode : EndpointState sourceEnv U source (B.inst a) (.sort v))
    (_hu : u.WF U) (_hv : v.WF U)
    (function : RichGradedResult sourceEnv env U registry Γ functionNode locals σ available (Profile.fn key output))
    (argument : RichGradedResult sourceEnv env U registry Γ argumentNode locals σ available rawInput)
    (arguments : GeneralNormalProfileAdapter env U registry Γ rawInput key.input)
    (admitted : Admitted env U registry Γ key (a.subst σ) (a.subst σ))
    (functionAnnotation : WorldObsProvenance strata function.observation)
    (argumentAnnotation : WorldObsProvenance strata argument.observation) :
    ∃ factor : RichApplicationOperandFactor env registry Γ functionNode argumentNode locals σ available output,
      ∃ fnAnnotation : WorldObsProvenance strata factor.function,
      ∃ argAnnotation : WorldObsProvenance strata factor.argument,
      fnAnnotation.worlds ++ argAnnotation.worlds = functionAnnotation.worlds ++ argumentAnnotation.worlds ∧
      factor.functionFootprint ++ factor.argumentFootprint = function.footprint ++ argument.footprint ∧
      ∀ current, max (factor.function.headDepth current) (factor.argument.headDepth current) =
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
  obtain ⟨hfAnnotation, hfWorlds⟩ := raiseQueryAnnotation function.observation functionAnnotation hfn
  obtain ⟨haAnnotation, haWorlds⟩ := raiseQueryAnnotation argument.observation argumentAnnotation harg
  obtain ⟨factor, fnAnnotation, argAnnotation, fnWorlds, argWorlds, functionDepth, argumentDepth⟩ :=
    RichObs.factor_application_annotated henv hf.observation functionAdapter
      ha.observation argumentAdapter hfAnnotation haAnnotation
  have rawLive := hf.live factor.rawOrigin factor.origin
  have selectedLive := (AdapterNormal.view henv factor.rawOrigin).live henv hscoped hΓ rawLive
  rw [factor.normalOrigin] at selectedLive
  have highAdmission : Admitted env U registry Γ highKey (a.subst σ) (a.subst σ) := by
    exact raiseKey_admitted hn henv admitted
  have actualAdmission := factor.keys.pull henv hscoped hΓ selectedLive.1
    (AdapterNormal.normalizeAdmission henv hscoped hΓ highAdmission)
  let operands : RichApplicationOperandFactor env registry Γ functionNode argumentNode locals σ available output := {
    rank := M, bound := hn, key := factor.key, output := factor.output
    functionFootprint := _, argumentFootprint := _
    function := factor.functionObservation, rawInput := ha.raw, argument := factor.argumentObservation
    arguments := factor.argumentAdapter, admitted := actualAdmission
    outputAdapter := factor.outputAdapter
    resources := append_available hf.resources ha.resources
    live := Profile.Live.singleton_iff.mpr selectedLive.2 }
  refine ⟨operands, fnAnnotation, argAnnotation, ?_, rfl, ?_⟩
  · rw [fnWorlds, argWorlds, hfWorlds, haWorlds]
  · intro current
    simp only [operands, functionDepth, argumentDepth, hf, ha,
      RichGradedResult.raiseTo, RichObs.headDepth_raise]

theorem RichGradedResult.appAnnotated
    {strata : EquationStratification env}
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
    (admitted : Admitted env U registry Γ key (a.subst σ) (a.subst σ))
    (functionAnnotation : WorldObsProvenance strata function.observation)
    (argumentAnnotation : WorldObsProvenance strata argument.observation) :
    ∃ result : RichGradedResult sourceEnv env U registry Γ
      (.app hu hv domain codomain functionNode argumentNode resultNode) locals σ available (.singleton output),
      ∃ annotation : WorldObsProvenance strata result.observation,
      annotation.worlds = functionAnnotation.worlds ++ argumentAnnotation.worlds ∧
      result.footprint = function.footprint ++ argument.footprint ∧
      ∀ current, result.observation.headDepth current =
        max (function.observation.headDepth current) (argument.observation.headDepth current) := by
  obtain ⟨factor, fnAnnotation, argAnnotation, worlds, footprint, depth⟩ :=
    RichGradedResult.appOperandsAnnotated henv hscoped hΓ _closed domain codomain resultNode hu hv
      function argument arguments admitted functionAnnotation argumentAnnotation
  exact ⟨factor.graded domain codomain resultNode hu hv,
    .app hu hv fnAnnotation argAnnotation factor.arguments factor.admitted,
    worlds, footprint, fun policy => by
      simpa only [RichApplicationOperandFactor.graded, RichObs.headDepth] using depth policy⟩

/-- Controls on the same literal operands used by application construction. -/
theorem RichGradedResult.appControlledOperands
    {strata : EquationStratification env}
    {frontier : List (EquationWorldClosureOrder.World strata.rules.length)}
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx Γ (env.IsType U))
    (closed : available.AtomClosed)
    {key : Key n} {output : Atom n}
    {functionNode : EndpointState sourceEnv U source f (.forallE A B)}
    {argumentNode : EndpointState sourceEnv U source a A}
    (domain : EndpointState sourceEnv U source A (.sort u))
    (body : EndpointState sourceEnv U (A :: source) B (.sort v))
    (resultNode : EndpointState sourceEnv U source (B.inst a) (.sort v))
    (hu : u.WF U) (hv : v.WF U)
    (function : RichGradedResult sourceEnv env U registry Γ functionNode locals σ available (Profile.fn key output))
    (argument : RichGradedResult sourceEnv env U registry Γ argumentNode locals σ available rawInput)
    (arguments : GeneralNormalProfileAdapter env U registry Γ rawInput key.input)
    (admitted : Admitted env U registry Γ key (a.subst σ) (a.subst σ))
    (controls : OriginalWorldControls strata controlSource)
    (functionReady : ControlledStoredQuery controls frontier (.observation function.observation))
    (argumentReady : ControlledStoredQuery controls frontier (.observation argument.observation)) :
    ∃ factor : RichApplicationOperandFactor env registry Γ functionNode argumentNode locals σ available output,
    ∃ ready : factor.Controlled controls frontier,
      ready.function.annotation.worlds ++ ready.argument.annotation.worlds =
        functionReady.annotation.worlds ++ argumentReady.annotation.worlds ∧
      factor.functionFootprint ++ factor.argumentFootprint = function.footprint ++ argument.footprint ∧
      ∀ policy, max (factor.function.headDepth policy) (factor.argument.headDepth policy) =
        max (function.observation.headDepth policy) (argument.observation.headDepth policy) := by
  obtain ⟨factor, fnAnnotation, argAnnotation, worlds, footprint, depth⟩ :=
    RichGradedResult.appOperandsAnnotated henv hscoped formed closed domain body resultNode hu hv
      function argument arguments admitted functionReady.annotation argumentReady.annotation
  have within : ∀ control, controls.cutoff < control →
      max (factor.function.headDepth (stratifiedHeadPolicy (strata.headOrdinal registry) control))
          (factor.argument.headDepth (stratifiedHeadPolicy (strata.headOrdinal registry) control)) ≤ controls.fuel control := by
    intro control active
    rw [depth]
    exact Nat.max_le.mpr ⟨functionReady.within control active, argumentReady.within control active⟩
  have sponsored : EquationWorldClosureOrder.Sponsored frontier (fnAnnotation.worlds ++ argAnnotation.worlds) := by
    rw [worlds]
    exact functionReady.sponsored.merge argumentReady.sponsored
  refine ⟨factor, ⟨⟨fnAnnotation, ?_, ?_⟩, ⟨argAnnotation, ?_, ?_⟩⟩, worlds, footprint, depth⟩
  · intro control active
    exact Nat.le_trans (Nat.le_max_left _ _) (within control active)
  · intro world member
    exact sponsored world (List.mem_append_left _ member)
  · intro control active
    exact Nat.le_trans (Nat.le_max_right _ _) (within control active)
  · intro world member
    exact sponsored world (List.mem_append_right _ member)


/-- The ordinary destination application keeps both exact child sponsor
lists and their inherited control policies, despite raw function grade changes. -/
theorem RichGradedResult.appControlled
    {strata : EquationStratification env}
    {frontier : List (EquationWorldClosureOrder.World strata.rules.length)}
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (closed : available.AtomClosed)
    {key : Key n} {output : Atom n}
    {functionNode : EndpointState sourceEnv U source f (.forallE A B)}
    {argumentNode : EndpointState sourceEnv U source a A}
    (domain : EndpointState sourceEnv U source A (.sort u))
    (body : EndpointState sourceEnv U (A :: source) B (.sort v))
    (resultNode : EndpointState sourceEnv U source (B.inst a) (.sort v))
    (hu : u.WF U) (hv : v.WF U)
    (function : RichGradedResult sourceEnv env U registry target functionNode locals σ available (Profile.fn key output))
    (argument : RichGradedResult sourceEnv env U registry target argumentNode locals σ available rawInput)
    (arguments : GeneralNormalProfileAdapter env U registry target rawInput key.input)
    (admitted : Admitted env U registry target key (a.subst σ) (a.subst σ))
    (controls : OriginalWorldControls strata controlSource)
    (functionReady : ControlledStoredQuery controls frontier (.observation function.observation))
    (argumentReady : ControlledStoredQuery controls frontier (.observation argument.observation)) :
    ∃ result : RichGradedResult sourceEnv env U registry target
      (.app hu hv domain body functionNode argumentNode resultNode) locals σ available (.singleton output),
    ∃ ready : ControlledStoredQuery controls frontier (.observation result.observation),
      ready.annotation.worlds = functionReady.annotation.worlds ++ argumentReady.annotation.worlds ∧
      result.footprint = function.footprint ++ argument.footprint ∧
      ∀ policy, result.observation.headDepth policy =
        max (function.observation.headDepth policy) (argument.observation.headDepth policy) := by
  obtain ⟨result, annotation, worlds, footprint, depth⟩ :=
    RichGradedResult.appAnnotated henv hscoped formed closed domain body resultNode hu hv
      function argument arguments admitted functionReady.annotation argumentReady.annotation
  refine ⟨result, ⟨annotation, ?_, ?_⟩, worlds, footprint, depth⟩
  · intro control active
    change result.observation.headDepth _ ≤ _
    rw [depth]
    exact Nat.max_le.mpr ⟨functionReady.within control active, argumentReady.within control active⟩
  · intro world member
    change world ∈ annotation.worlds at member
    rw [worlds] at member
    exact (List.mem_append.mp member).elim
      (functionReady.sponsored world) (argumentReady.sponsored world)

/-- A sorted application output is actual ordinary destination code. Its
finite control proof is derived from the same chosen graded application. -/
theorem RichGradedResult.appCodeControlled
    {strata : EquationStratification env}
    {frontier : List (EquationWorldClosureOrder.World strata.rules.length)}
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (closed : available.AtomClosed)
    {key : Key n} {output : Atom n}
    {functionNode : EndpointState sourceEnv U source f (.forallE A B)}
    {argumentNode : EndpointState sourceEnv U source a A}
    (domain : EndpointState sourceEnv U source A (.sort u))
    (body : EndpointState sourceEnv U (A :: source) B (.sort v))
    (resultNode : EndpointState sourceEnv U source (B.inst a) (.sort v))
    (hu : u.WF U) (hv : v.WF U)
    (function : RichGradedResult sourceEnv env U registry target functionNode locals σ available (Profile.fn key output))
    (argument : RichGradedResult sourceEnv env U registry target argumentNode locals σ available rawInput)
    (arguments : GeneralNormalProfileAdapter env U registry target rawInput key.input)
    (admitted : Admitted env U registry target key (a.subst σ) (a.subst σ))
    (sorted : (Profile.singleton output).HasType (.sort relevant))
    (controls : OriginalWorldControls strata controlSource)
    (functionReady : ControlledStoredQuery controls frontier (.observation function.observation))
    (argumentReady : ControlledStoredQuery controls frontier (.observation argument.observation)) :
    ∃ footprint, ∃ certificate : RichCert sourceEnv env U registry target
      (.app hu hv domain body functionNode argumentNode resultNode) locals σ relevant (.singleton output) footprint,
    ∃ ready : ControlledStoredQuery controls frontier (.certificate certificate),
      footprint.Available available ∧
      ready.annotation.worlds ⊆ functionReady.annotation.worlds ++ argumentReady.annotation.worlds := by
  obtain ⟨result, resultReady, worlds, _, _⟩ :=
    RichGradedResult.appControlled henv hscoped formed closed domain body resultNode hu hv
      function argument arguments admitted controls functionReady argumentReady
  obtain ⟨footprint, certificate, ready, resources, included⟩ :=
    result.code_controlled henv controls resultReady sorted
  refine ⟨footprint, certificate, ready, resources, ?_⟩
  intro world member
  rw [← worlds]
  exact included member

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
