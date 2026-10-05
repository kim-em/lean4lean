import Lean4Lean.Theory.Typing.AnchoredOriginalRichApplicationSeeding
import Lean4Lean.Theory.Typing.AnchoredOriginalRichVariableQueries
import Lean4Lean.Theory.Typing.AnchoredSortableEtaAdapter
import Lean4Lean.Theory.Typing.AnchoredOriginalGeneratedResourceCaps

/-! The full rich eta-body query computes a finite request at its actual
original lifted-function child. Only the literal bound-variable query is
normalized into a variable trace. Projected function/type metadata stays in
its original rich query, ready for the strictly smaller source-lift replay. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000
set_option Elab.async false

/-- Actual eta function provenance together with contravariant finite input
adaptation and the complete covariant output action. -/
structure RichEtaFunctionRequest
    (root : EndpointRef sourceEnv U rootSource rootExpression rootType)
    (env : VEnv) (registry : CanonicalHead.Registry) (target : List VExpr)
    (source : List VExpr) (locals : List Nat) (σ : Subst) (available : Valuation)
    (f : VExpr) (lambdaKey : Key n) (output : Atom n) where
  origin : RichAppOrigin root env registry target source locals σ f (.bvar 0)
  rank : Nat
  bound : n ≤ rank
  key : Key rank
  rawOutput : Atom rank
  footprint : Footprint
  function : RichObs sourceEnv env U registry target origin.functionNode locals σ
    (Profile.fn key rawOutput) footprint
  resources : footprint.Available available
  admitted : Admitted env U registry target key (σ 0) (σ 0)
  arguments : GeneralNormalProfileAdapter env U registry target
    (raiseProfile rank bound lambdaKey.input) key.input
  outputAction : AtomAction env U registry target rawOutput (raiseAtom rank bound output)

private noncomputable def selectGeneral {p q : Profile n}
    (included : List.Subset q.atoms p.atoms) :
    GeneralNormalProfileAdapter env U registry target p q :=
  GeneralProfileAdapter.select (fun _ h => by
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp h
    exact List.mem_map.mpr ⟨a, included ha, rfl⟩)

/-- This uses the actual input cap of the fresh common binder, so selection,
code actions, and grading may change the literal variable query footprint
without assuming that its demands were present in the old pack verbatim. -/
theorem RichObs.etaFunctionRequest
    {node : EndpointState sourceEnv U source (.app f (.bvar 0)) assigned}
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    (query : RichObs sourceEnv env U registry target node locals σ
      (.singleton (output : Atom n)) footprint)
    (location : Located root node)
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (formed : OnCtx target (env.IsType U))
    (closed : available.AtomClosed) (resources : footprint.Available available)
    (lambdaKey : Key n)
    (headCap : ∀ need ∈ available 0, Need.Fits lambdaKey.input need) :
    ∃ request : RichEtaFunctionRequest root env registry target source locals σ available f lambdaKey output,
      request.origin.RootedAt node := by
  obtain ⟨origin, ⟨path⟩, included, rooted⟩ :=
    query.applicationOriginRooted location (List.mem_singleton_self _)
  have functionAvailable : origin.functionFootprint.Available available :=
    fun index need member => resources index need (included (List.mem_append_left _ member))
  have argumentAvailable : origin.argumentFootprint.Available available :=
    fun index need member => resources index need (included (List.mem_append_right _ member))
  obtain ⟨required, ⟨argumentQuery⟩, argumentResources⟩ :=
    origin.argument.variableQuery closed argumentAvailable
  let argument := argumentQuery.variableTrace
  have hbounds : ∀ index need, (index, need) ∈ required → need.rank ≤ n := by
    intro index need member
    have equal := argument.indices member
    subst index
    exact (headCap need (argumentResources 0 need member)).1
  have hinput : List.Subset (required.atGrade n).atoms lambdaKey.input.atoms := by
    intro atom member
    obtain ⟨⟨index, need⟩, present, selected⟩ := List.mem_flatMap.mp member
    have equal := argument.indices present
    subst index
    exact (headCap need (argumentResources 0 need present)).2 atom selected
  let N := max path.height argument.height
  have hp : path.height ≤ N := Nat.le_max_left _ _
  have ha : argument.height ≤ N := Nat.le_max_right _ _
  have hn : n ≤ N := Nat.le_trans path.bounds.2 hp
  have hr : origin.rank ≤ N := Nat.le_trans path.bounds.1 hp
  have lifted := origin.function.raise (Nat.succ_le_succ hr)
  simp only [Profile.fn, raiseProfile_singleton] at lifted
  have exposed := RichObs.view lifted (functionGradeView hr origin.key origin.output)
  have variableAdapter := argument.normalize henv hscoped formed N ha
  have selected : GeneralNormalProfileAdapter env U registry target
      (raiseProfile N hn lambdaKey.input) (required.atGrade N) := by
    rw [Footprint.atGrade_raise hn hbounds]
    exact selectGeneral (raiseProfile_subset hn hinput)
  have argumentAdapter := GeneralNormalProfileAdapter.raise henv hscoped formed hr origin.arguments
  have arguments := selected.comp (variableAdapter.comp argumentAdapter)
  refine ⟨{
    origin := origin
    rank := N
    bound := hn
    key := raiseKey N hr origin.key
    rawOutput := raiseAtom N hr origin.output
    footprint := origin.functionFootprint
    function := by simpa only [Profile.fn, raiseProfile_singleton] using exposed
    resources := functionAvailable
    admitted := Admitted.raise henv hr origin.admitted
    arguments := arguments
    outputAction := path.normalize N hp }, rooted⟩

/-- Route determinism recovers the exact original function child, even
when the incoming eta-body query had conversion and code wrappers. -/
theorem RichEtaFunctionRequest.originalFunctionQuery
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {domain : EndpointState sourceEnv U source A (.sort u)}
    {body : EndpointState sourceEnv U (A :: source) B (.sort v)}
    {function : EndpointState sourceEnv U source f (.forallE A B)}
    {argument : EndpointState sourceEnv U source (.bvar 0) A}
    {result : EndpointState sourceEnv U source (B.inst (.bvar 0)) (.sort v)}
    (hu : u.WF U) (hv : v.WF U)
    (request : RichEtaFunctionRequest root env registry target source locals σ available f lambdaKey output)
    {first : EndpointState sourceEnv U source (.app f (.bvar 0)) assigned}
    (route : PrefixRoute sourceEnv U source (.app f (.bvar 0)) first
      (.app hu hv domain body function argument result))
    (rooted : request.origin.RootedAt first) :
    Nonempty (RichObs sourceEnv env U registry target function locals σ
      (Profile.fn request.key request.rawOutput) request.footprint) := by
  obtain ⟨originRoute⟩ := rooted
  have equal := originRoute.structural_unique (by trivial) route (by trivial)
  cases request with
  | mk origin rank bound key rawOutput footprint query resources admitted arguments action =>
    cases origin with
    | mk A' B' u' v' hu' hv' domain' codomain' functionNode argumentNode result' location
        originRank originKey originOutput functionFootprint argumentFootprint functionQuery rawInput
        argumentQuery originArguments originAdmitted =>
      simp only [RichAppOrigin.node] at equal
      obtain ⟨_, _, _, domainEq, _, bodyEq, _, _, _, _, _, functionEq, _, _⟩ :=
        EndpointState.app.hinj rfl rfl rfl rfl equal.1 equal.2
      cases domainEq
      cases bodyEq
      have functionEq := eq_of_heq functionEq
      cases functionEq
      exact ⟨query⟩

/-- The finite eta input program is computed from the actual lifted-function
semantics and original lambda guard. It does not request an enlarged input
at a frozen old domain. -/
theorem RichEtaFunctionRequest.adapter
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (formed : OnCtx target (env.IsType U))
    {lambdaKey : Key n} {output : Atom n} {domainSupport : Profile n}
    (request : RichEtaFunctionRequest root env registry target source locals σ available f lambdaKey output)
    (anchorEq : σ 0 = lambdaKey.anchor)
    {support : Profile (request.rank + 1)}
    (guard : LambdaGuard env U registry target realization A lambdaKey domainSupport)
    (related : Related env U registry target left right (.forallE (A.subst realization) bodyType)
      (Profile.fn request.key request.rawOutput) support) :
    Nonempty (GeneralNormalProfileAdapter env U registry target
      (Profile.fn request.key request.rawOutput)
      (raiseProfile (request.rank + 1) (Nat.succ_le_succ request.bound)
        (Profile.fn lambdaKey output))) := by
  classical
  obtain ⟨oldSupport, oldTyped, oldFormed, oldPath, oldBridge⟩ :=
    related.fn_domain_alignment henv hscoped formed
  let highKey := raiseKey request.rank request.bound lambdaKey
  have highGuard := guard.raise henv request.bound
  let anchored := reanchorKey request.key lambdaKey.anchor
  let actual := domainKey anchored (A.subst realization)
  let widened := domainKey highKey (A.subst realization)
  have admitted : Admitted env U registry target request.key lambdaKey.anchor lambdaKey.anchor :=
    anchorEq ▸ request.admitted
  have reanchor : GeneralNormalAtomAdapter (n := request.rank + 1) env U registry target
      (.fn request.key request.rawOutput) (.fn anchored request.rawOutput) :=
    (AtomView.reanchor (output := request.rawOutput) admitted).toGeneralAdapter henv hscoped formed
  have domain : GeneralNormalAtomAdapter (n := request.rank + 1) env U registry target
      (.fn anchored request.rawOutput) (.fn actual request.rawOutput) :=
    (AtomView.domainRekey (key := anchored) (output := request.rawOutput)
      oldPath oldTyped oldFormed oldBridge).toGeneralAdapter henv hscoped formed
  have seed := Admitted.rekey henv highGuard.path highGuard.inputTyped highGuard.formed
    highGuard.domains highGuard.anchor
  have normalSeed := AdapterNormal.normalizeAdmission henv hscoped formed seed
  have input : GeneralNormalAtomAdapter (n := request.rank + 1) env U registry target
      (.fn actual request.rawOutput) (.fn widened request.rawOutput) :=
    .fn (.input (.supplied normalSeed) request.arguments) (.refl _)
  have restore : GeneralNormalAtomAdapter (n := request.rank + 1) env U registry target
      (.fn widened request.rawOutput) (.fn highKey request.rawOutput) :=
    (AtomView.domainRekey (key := widened) (output := request.rawOutput)
      highGuard.path.symm highGuard.inputTyped highGuard.formed
      (highGuard.domains.symm henv highGuard.inputTyped.wf_type)).toGeneralAdapter henv hscoped formed
  have result : GeneralNormalAtomAdapter (n := request.rank + 1) env U registry target
      (.fn highKey request.rawOutput) (.fn highKey (raiseAtom request.rank request.bound output)) :=
    .fn (.refl _) (request.outputAction.toGeneralAdapter henv hscoped formed)
  have lower := ((functionGradeView (env := env) (U := U) (registry := registry)
    (Γ := target) request.bound lambdaKey output).inverse henv).toGeneralAdapter henv hscoped formed
  have adapter := reanchor.comp (domain.comp (input.comp (restore.comp (result.comp lower))))
  simp only [Profile.fn, raiseProfile_singleton]
  exact ⟨.cons (List.mem_singleton_self _) adapter (.nil _)⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
