import Lean4Lean.Theory.Typing.AnchoredOriginalSortableBudgetBetaForward
import Lean4Lean.Theory.Typing.AnchoredOriginalSortableDepthFactor
import Lean4Lean.Theory.Typing.AnchoredOriginalSortableDepthArguments

/-! Bounded backward beta expansion retains the original instantiated endpoint
and computes all cuts before invoking the fixed original argument clause. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure OriginalTail
open OriginalEndpointFactor OriginalFactorCut
set_option backward.isDefEq.respectTransparency false

private theorem one_realized (argument : VExpr) (σ : Subst) :
    (Subst.one argument).comp σ = σ.cons (argument.subst σ) := by
  funext i
  cases i <;> rfl

theorem SortableObs.betaExpandAtomBudgeted
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered)
    {source target : List VExpr} {locals : List Nat} {σ : Subst}
    {available : Valuation} {A body argument : VExpr} {output : Atom n} {footprint : Footprint}
    {sourceEnv : VEnv}
    (instantiated : EndpointRef sourceEnv U source (body.inst argument) assigned)
    (argumentChild : HereditaryBudgeted.Transfer budgets env U registry target locals σ σ available argument argument A)
    (rawArgument : env.HasType U source argument A)
    (_closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (observation : SortableObs env U registry target locals σ (body.inst argument) (.singleton output) footprint)
    (bounded : HereditaryBudgeted.Within budgets observation.nativeDepth)
    (resources : footprint.Available available) :
    ∃ required, ∃ result : SortableObs env U registry target locals σ (.app (.lam A body) argument)
      (.singleton output) required,
      required.Available available ∧ HereditaryBudgeted.Within budgets result.nativeDepth := by
  have factored := OriginalFactorCut.SortableObs.factorInstAtStart_allDepth (body := body) (argument := argument) observation
    (.ref instantiated) .here locals (Locals.push locals)
  rw [one_realized] at factored
  obtain ⟨bodyFootprint, bodyObservation, factor, factorDepth⟩ := factored
  obtain ⟨arguments, argumentsDepth⟩ := factor.arguments_allDepth available resources n
  obtain ⟨argResult⟩ := argumentChild arguments.observation
    (fun current fuel member => Nat.le_trans (argumentsDepth current)
      (Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (factorDepth current))
        (bounded current fuel member))) arguments.argumentAvailable
  let domain := argResult.requestedCertificate
  have typed := argResult.requestedTyped
  have related := argResult.requestedRelated henv hTarget
  have code := TypeRelated.lower henv argResult.bound argResult.typeCode
  have raw := rawArgument.subst henv substitutions hTarget
  let key : Key arguments.rank := ⟨A.subst σ, argument.subst σ, arguments.input⟩
  have admitted : Admitted env U registry target key key.anchor key.anchor :=
    ⟨raw, raw, _, typed, domain.formed, code, related, related⟩
  have guard : LambdaGuard env U registry target σ A key _ :=
    ⟨typed, domain.formed, .refl, code, admitted⟩
  let bodyHigh : SortableObs env U registry target (Locals.push locals) (σ.cons key.anchor) body
      (.singleton (raiseAtom arguments.rank arguments.bound output)) bodyFootprint :=
    cast (congrArg (fun p => SortableObs env U registry target (Locals.push locals)
      (σ.cons key.anchor) body p bodyFootprint) (raiseProfile_singleton arguments.bound output))
      (bodyObservation.raise arguments.bound)
  have bodyDepth (current : Name → Bool) : bodyHigh.nativeDepth current = bodyObservation.nativeDepth current :=
    (SortableObs.nativeDepth_cast current (raiseProfile_singleton arguments.bound output) _ _).trans
      (bodyObservation.nativeDepth_raise current arguments.bound)
  let fn := SortableObs.lam domain guard bodyHigh arguments.pack (fun _ h => h)
  let app := SortableObs.app fn arguments.observation (.refl _) admitted
  let app' : SortableObs env U registry target locals σ (.app (.lam A body) argument)
      (raiseProfile arguments.rank arguments.bound (.singleton output))
      ((argResult.typeFootprint ++ arguments.outside) ++ arguments.argumentFootprint) :=
    cast (congrArg (fun p => SortableObs env U registry target locals σ (.app (.lam A body) argument)
      p ((argResult.typeFootprint ++ arguments.outside) ++ arguments.argumentFootprint))
      (raiseProfile_singleton arguments.bound output).symm) app
  refine ⟨_, app'.lower arguments.bound, ?_, ?_⟩
  · intro i need hm
    rcases List.mem_append.mp hm with hm | hm
    · exact (List.mem_append.mp hm).elim
        (argResult.typeAvailable i need) (arguments.outsideAvailable i need)
    · exact arguments.argumentAvailable i need hm
  · intro current fuel member
    have appDepth : app'.nativeDepth current = app.nativeDepth current :=
      SortableObs.nativeDepth_cast current (raiseProfile_singleton arguments.bound output).symm _ _
    have hd := argResult.certificateBound current fuel member
    have hb := Nat.le_trans (Nat.le_max_left _ _) (Nat.le_trans (factorDepth current) (bounded current fuel member))
    have ha := Nat.le_trans (argumentsDepth current)
      (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_trans (factorDepth current) (bounded current fuel member)))
    simp only [SortableObs.nativeDepth_lower, appDepth, app, fn, SortableObs.nativeDepth,
      bodyDepth, domain, SortableComputationalTransferResult.requestedCertificate,
      SortableCert.nativeDepth_lower]
    exact Nat.max_le.mpr ⟨Nat.max_le.mpr ⟨hd, hb⟩, ha⟩

private theorem SortableObs.subprofile_allDepth
    (observation : SortableObs env U registry target locals σ expression (input : Profile n) footprint)
    (selected : Profile n) (included : ∀ atom ∈ selected.atoms, atom ∈ input.atoms) :
    ∃ required, ∃ result : SortableObs env U registry target locals σ expression selected required,
      required.Atomizes footprint ∧ ∀ current, result.nativeDepth current ≤ observation.nativeDepth current := by
  induction selected with
  | nil => exact ⟨[], .legacy .empty, (fun _ _ h => nomatch h), by
      intro current; simp only [SortableObs.nativeDepth, Obs.nativeDepth]; exact Nat.zero_le _⟩
  | cons head tail ih =>
    obtain ⟨first, firstBound⟩ := observation.atom_allDepth (included head List.mem_cons_self)
    obtain ⟨rest, last, selection, lastBound⟩ := ih (fun atom hm => included atom (List.mem_cons_of_mem _ hm))
    exact ⟨first.footprint ++ rest, .union first.observation last,
      first.atomizes.append selection, by
      intro current
      simpa only [SortableObs.nativeDepth] using Nat.max_le.mpr ⟨firstBound current, lastBound current⟩⟩

theorem SortableObs.betaExpandBudgeted
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered)
    {source target : List VExpr} {locals : List Nat} {σ : Subst}
    {available : Valuation} {A body argument : VExpr} {demand : Profile n} {footprint : Footprint}
    {sourceEnv : VEnv}
    (instantiated : EndpointRef sourceEnv U source (body.inst argument) assigned)
    (argumentChild : HereditaryBudgeted.Transfer budgets env U registry target locals σ σ available argument argument A)
    (rawArgument : env.HasType U source argument A)
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (observation : SortableObs env U registry target locals σ (body.inst argument) demand footprint)
    (bounded : HereditaryBudgeted.Within budgets observation.nativeDepth)
    (resources : footprint.Available available) :
    ∃ required, ∃ result : SortableObs env U registry target locals σ (.app (.lam A body) argument)
      demand required, required.Available available ∧ HereditaryBudgeted.Within budgets result.nativeDepth := by
  induction demand generalizing footprint with
  | nil => exact ⟨[], .legacy .empty, (fun _ _ h => nomatch h), by intro current fuel member; simp only [SortableObs.nativeDepth, Obs.nativeDepth]; exact Nat.zero_le _⟩
  | cons atom rest ih =>
    obtain ⟨selected, selectedDepth⟩ := observation.atom_allDepth List.mem_cons_self
    obtain ⟨firstFootprint, first, firstAvailable, firstDepth⟩ := selected.observation.betaExpandAtomBudgeted henv
      instantiated argumentChild rawArgument closed hTarget substitutions
      (fun current fuel member => Nat.le_trans (selectedDepth current) (bounded current fuel member))
      (selected.atomizes.available_closed resources closed)
    obtain ⟨tailFootprint, tail, selection, tailDepth⟩ := observation.subprofile_allDepth rest (fun _ h => List.mem_cons_of_mem _ h)
    obtain ⟨lastFootprint, last, lastAvailable, lastDepth⟩ := ih tail
      (fun current fuel member => Nat.le_trans (tailDepth current) (bounded current fuel member))
      (selection.available_closed resources closed)
    exact ⟨firstFootprint ++ lastFootprint, .union first last,
      (fun i need hm => (List.mem_append.mp hm).elim (firstAvailable i need) (lastAvailable i need)),
      by
        intro current fuel member
        simpa only [SortableObs.nativeDepth] using Nat.max_le.mpr ⟨firstDepth current fuel member, lastDepth current fuel member⟩⟩

theorem HereditaryBudgeted.Result.betaExpandBudgeted
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered)
    {source target : List VExpr} {locals : List Nat} {σ τ : Subst}
    {available : Valuation} {A B body argument : VExpr} {demand : Profile n}
    {sourceEnv : VEnv}
    (instantiated : EndpointRef sourceEnv U source (body.inst argument) assigned)
    (argumentChild : HereditaryBudgeted.Transfer budgets env U registry target locals τ τ available argument argument A)
    (rawBody : env.HasType U (A :: source) body B)
    (rawArgument : env.HasType U source argument A)
    (formedInstantiated : env.HasType U source (B.inst argument) (.sort bodyLevel))
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (result : HereditaryBudgeted.Result budgets env U registry target locals σ τ available
      (body.inst argument) (body.inst argument) (B.inst argument) demand) :
    Nonempty (HereditaryBudgeted.Result budgets env U registry target locals σ τ available
      (body.inst argument) (.app (.lam A body) argument) (B.inst argument) demand) := by
  obtain ⟨footprint, observation, resources, observationDepth⟩ := result.observation.betaExpandBudgeted henv
    instantiated argumentChild rawArgument closed hTarget (substitutions.right henv hTarget) result.observationBound result.resources
  have beta := IsDefEq.beta rawBody rawArgument
  have typePair := formedInstantiated.substDF henv substitutions.wf hTarget substitutions
  have rightBeta := IsDefEq.defeqDF typePair.symm
    (beta.subst henv (substitutions.right henv hTarget) hTarget)
  have leftTyped := beta.hasType.2.subst henv substitutions.left hTarget
  have step : HeadBeta ((VExpr.app (.lam A body) argument).subst τ)
      ((body.inst argument).subst τ) := by
    simpa only [mkApps, List.foldl_cons, List.foldl_nil, subst, subst_inst] using
      (HeadBeta.contract (A := A.subst τ) (body := body.subst τ.lift)
        (argument := argument.subst τ) (trailing := []))
  exact ⟨{
    rank := result.rank
    bound := result.bound
    raw := result.raw
    footprint := footprint
    observation := observation
    adapter := result.adapter
    resources := resources
    support := result.support
    typeFootprint := result.typeFootprint
    typeCertificate := result.typeCertificate
    typeAvailable := result.typeAvailable
    typed := result.typed
    rawTyped := result.rawTyped
    typeCode := result.typeCode
    related := Related.headBeta henv .refl step leftTyped rightBeta result.related
    rawRelated := Related.headBeta henv step step rightBeta rightBeta result.rawRelated
    live := result.live
    observationBound := observationDepth
    certificateBound := result.certificateBound }⟩


end Lean4Lean.AnchoredSource.Adapted
