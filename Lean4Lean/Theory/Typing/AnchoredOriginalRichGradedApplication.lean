import Lean4Lean.Theory.Typing.AnchoredOriginalProjectionSortableSubstitution
import Lean4Lean.Theory.Typing.AnchoredSortableGradedAction
import Lean4Lean.Theory.Typing.AnchoredOriginalRichNativeDepthFuture

/-! Actual endpoint-indexed source reconstruction for generalized application
and action. Returned queries retain their original source nodes, finite
footprints, and contravariant argument programs. No semantic producer is a
field of the reconstruction. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
set_option backward.isDefEq.respectTransparency false

noncomputable def RichObs.raise {n N : Nat} {profile : Profile n}
    (source : RichObs sourceEnv env U registry target node locals σ profile footprint)
    (bound : n ≤ N) :
    RichObs sourceEnv env U registry target node locals σ (raiseProfile N bound profile) footprint := by
  induction N with
  | zero => have equal : n = 0 := by omega
            subst n; exact source
  | succ N ih =>
    by_cases equal : n = N + 1
    · subst n; simpa only [raiseProfile_self] using source
    · have previous : n ≤ N := by omega
      simpa only [raiseProfile_step previous] using RichObs.pad (ih previous)

noncomputable def RichGradedResult.raiseTo
    (henv : env.Ordered) (hscoped : registry.Scoped) (hΓ : OnCtx Γ (env.IsType U))
    (result : RichGradedResult sourceEnv env U registry Γ node locals σ available requested)
    (N : Nat) (bound : result.rank ≤ N) :
    RichGradedResult sourceEnv env U registry Γ node locals σ available requested where
  rank := N
  bound := Nat.le_trans result.bound bound
  raw := raiseProfile N bound result.raw
  footprint := result.footprint
  observation := result.observation.raise bound
  adapter := by simpa only [raiseProfile_trans] using
    GeneralNormalProfileAdapter.raise henv hscoped hΓ bound result.adapter
  resources := result.resources
  live := (raiseProfile_live_iff bound result.raw).mpr result.live

structure RichApplicationFactor (sourceEnv env : VEnv) (U : Nat)
    (registry : CanonicalHead.Registry) (Γ : List VExpr)
    {source : List VExpr} {f a functionType argumentType : VExpr}
    (function : EndpointState sourceEnv U source f functionType)
    (argument : EndpointState sourceEnv U source a argumentType)
    (locals : List Nat) (σ : Subst)
    (requestedKey : Key n) (requestedOutput : Atom n)
    (functionDemand : Profile (n + 1)) (argumentDemand : Profile n)
    (functionFootprint argumentFootprint : Footprint) where
  key : Key n
  output : Atom n
  rawOrigin : Atom (n + 1)
  origin : rawOrigin ∈ functionDemand.atoms
  normalOrigin : AdapterNormal.atom rawOrigin = .fn key output
  functionObservation : RichObs sourceEnv env U registry Γ function locals σ
    (Profile.fn key output) functionFootprint
  argumentObservation : RichObs sourceEnv env U registry Γ argument locals σ
    argumentDemand argumentFootprint
  argumentAdapter : GeneralNormalProfileAdapter env U registry Γ argumentDemand key.input
  keys : GeneralKeyProgram env U registry Γ key (AdapterNormal.key requestedKey)
  outputAdapter : GeneralNormalAtomAdapter env U registry Γ output requestedOutput

private theorem RichObs.nativeDepth_profileRec (current : Name → Bool)
    {α : Sort _} {a b : α} (equal : a = b) (profiles : α → Profile n)
    (query : RichObs sourceEnv env U registry target node locals σ (profiles a) footprint) :
    (equal ▸ query : RichObs sourceEnv env U registry target node locals σ (profiles b) footprint).nativeDepth current =
      query.nativeDepth current := by
  cases equal
  rfl

theorem RichObs.factor_application_nativeDepth
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
      (∀ current, factor.functionObservation.nativeDepth current = functionObservation.nativeDepth current) ∧
      (∀ current, factor.argumentObservation.nativeDepth current = argumentObservation.nativeDepth current) := by
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
  simpa only [RichObs.nativeDepth] using RichObs.nativeDepth_profileRec current normalOrigin Profile.singleton
    (RichObs.view (RichObs.select functionObservation originalMember) (AdapterNormal.view henv original))

theorem RichObs.factor_application
    (henv : env.Ordered)
    (functionObservation : RichObs sourceEnv env U registry Γ function locals σ
      (functionDemand : Profile (n + 1)) functionFootprint)
    (functionAdapter : GeneralNormalProfileAdapter env U registry Γ functionDemand
      (Profile.fn requestedKey requestedOutput))
    (argumentObservation : RichObs sourceEnv env U registry Γ argument locals σ
      (argumentDemand : Profile n) argumentFootprint)
    (argumentAdapter : GeneralNormalProfileAdapter env U registry Γ argumentDemand requestedKey.input) :
    Nonempty (RichApplicationFactor sourceEnv env U registry Γ function argument locals σ
      requestedKey requestedOutput functionDemand argumentDemand functionFootprint argumentFootprint) := by
  obtain ⟨factor, _, _⟩ := RichObs.factor_application_nativeDepth henv functionObservation functionAdapter
    argumentObservation argumentAdapter
  exact ⟨factor⟩

private theorem append_available {first second : Footprint} {available : Valuation}
    (left : first.Available available) (right : second.Available available) :
    (first ++ second).Available available := by
  intro i need hm
  exact (List.mem_append.mp hm).elim (left i need) (right i need)

private theorem raiseKey_admitted {n N : Nat} (h : n ≤ N)
    (henv : env.Ordered) {key : Key n}
    (admitted : Admitted env U registry Γ key x y) :
    Admitted env U registry Γ (raiseKey N h key) x y := by
  induction N with
  | zero =>
    have he : n = 0 := by omega
    subst n
    simpa only [raiseKey_self] using admitted
  | succ N ih =>
    by_cases he : n = N + 1
    · subst n; simpa only [raiseKey_self] using admitted
    · have hn : n ≤ N := by omega
      rw [raiseKey_step hn]
      exact Admitted.pad henv (ih hn)

/-- Raising the profile changes no declaration unfolding in its actual query. -/
theorem RichObs.nativeDepth_raise (current : Name → Bool)
    {n N : Nat} {profile : Profile n}
    (source : RichObs sourceEnv env U registry target node locals σ profile footprint)
    (bound : n ≤ N) : (source.raise bound).nativeDepth current = source.nativeDepth current := by
  induction N with
  | zero =>
    have equal : n = 0 := by omega
    subst n
    rfl
  | succ N ih =>
    by_cases equal : n = N + 1
    · subst n
      simp only [RichObs.raise, dif_pos]
      exact RichObs.nativeDepth_mpr current rfl rfl (raiseProfile_self ..).symm rfl _ source
    · have previous : n ≤ N := by omega
      simp only [RichObs.raise, dif_neg equal]
      refine (RichObs.nativeDepth_mpr current rfl rfl
        (raiseProfile_step previous profile).symm rfl _ _).trans ?_
      change (RichObs.pad (source.raise previous)).nativeDepth current = _
      simpa only [RichObs.nativeDepth] using ih previous

theorem RichGradedResult.nativeDepth_raiseTo (current : Name → Bool)
    (henv : env.Ordered) (hscoped : registry.Scoped) (hΓ : OnCtx Γ (env.IsType U))
    (result : RichGradedResult sourceEnv env U registry Γ node locals σ available requested)
    (N : Nat) (bound : result.rank ≤ N) :
    (result.raiseTo henv hscoped hΓ N bound).observation.nativeDepth current =
      result.observation.nativeDepth current :=
  result.observation.nativeDepth_raise current bound

/-- Align the two finite raw grades, then consume the actual returned function
row. The function's finite liveness supplies the raw guard; its assigned type
is not reconstructed or interpreted during syntax substitution. -/
theorem RichGradedResult.app_nativeDepth
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
      ∀ current, result.observation.nativeDepth current =
        max (function.observation.nativeDepth current) (argument.observation.nativeDepth current) := by
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
  obtain ⟨factor, functionDepth, argumentDepth⟩ := RichObs.factor_application_nativeDepth henv hf.observation functionAdapter
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
  simp only [produced, RichObs.nativeDepth, functionDepth, argumentDepth,
    hf, ha, RichGradedResult.nativeDepth_raiseTo]

theorem RichGradedResult.app
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
    Nonempty (RichGradedResult sourceEnv env U registry Γ
      (.app hu hv domain codomain functionNode argumentNode resultNode) locals σ available (.singleton output)) := by
  obtain ⟨result, _⟩ := RichGradedResult.app_nativeDepth henv hscoped hΓ _closed domain codomain resultNode hu hv
    function argument arguments admitted
  exact ⟨result⟩


theorem RichGradedResult.action
    (henv : env.Ordered) (hscoped : registry.Scoped) (hΓ : OnCtx Γ (env.IsType U))
    {a b : Atom n} (action : AtomAction env U registry Γ a b)
    (result : RichGradedResult sourceEnv env U registry Γ node locals σ available (.singleton a)) :
    Nonempty (RichGradedResult sourceEnv env U registry Γ node locals σ available (.singleton b)) := by
  refine ⟨{ result with adapter := ?_ }⟩
  have step := (action.raise result.bound).toGeneralAdapter henv hscoped hΓ
  have first := result.adapter
  rw [raiseProfile_singleton] at first ⊢
  exact GeneralProfileAdapter.comp first (.cons (List.mem_singleton_self _) step (.nil _))

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
