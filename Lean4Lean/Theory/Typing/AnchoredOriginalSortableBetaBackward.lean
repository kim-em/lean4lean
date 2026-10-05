import Lean4Lean.Theory.Typing.AnchoredOriginalSortableBetaForward
import Lean4Lean.Theory.Typing.AnchoredOriginalSortableArguments

/-! Backward beta expansion factors the query at the retained original
instantiated endpoint. The computed mixed cuts are admitted by the actual
argument induction clause, then rebuilt as a rich lambda/application query. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure OriginalTail
open OriginalEndpointFactor OriginalFactorCut
set_option backward.isDefEq.respectTransparency false

private theorem one_realized (argument : VExpr) (σ : Subst) :
    (Subst.one argument).comp σ = σ.cons (argument.subst σ) := by
  funext i
  cases i <;> rfl

theorem SortableObs.betaExpandAtomOriginal
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered)
    {source target : List VExpr} {locals : List Nat} {σ : Subst}
    {available : Valuation} {A body argument : VExpr} {output : Atom n} {footprint : Footprint}
    {sourceEnv : VEnv}
    (instantiated : EndpointRef sourceEnv U source (body.inst argument) assigned)
    (argumentChild : SortableComputationalTransfer env U registry target locals σ σ available argument argument A)
    (rawArgument : env.HasType U source argument A)
    (_closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (observation : SortableObs env U registry target locals σ (body.inst argument) (.singleton output) footprint)
    (resources : footprint.Available available) :
    ∃ required, Nonempty (SortableObs env U registry target locals σ (.app (.lam A body) argument)
      (.singleton output) required) ∧ required.Available available := by
  obtain ⟨bodyFootprint, ⟨bodyObservation⟩, ⟨factor⟩⟩ :=
    OriginalFactorCut.SortableObs.factorInstAtStart observation (.ref instantiated) .here locals (Locals.push locals)
  simp only [one_realized] at bodyObservation
  obtain ⟨arguments⟩ := factor.arguments available resources n
  obtain ⟨argResult⟩ :=
    argumentChild
      arguments.observation arguments.argumentAvailable
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
  have bodyHigh := bodyObservation.raise arguments.bound
  rw [raiseProfile_singleton] at bodyHigh
  have fn := SortableObs.lam domain guard bodyHigh arguments.pack (fun _ h => h)
  have app := SortableObs.app fn arguments.observation (.refl _) admitted
  have app' : SortableObs env U registry target locals σ (.app (.lam A body) argument)
      (raiseProfile arguments.rank arguments.bound (.singleton output))
      ((argResult.typeFootprint ++ arguments.outside) ++ arguments.argumentFootprint) := by
    rw [raiseProfile_singleton]
    exact app
  refine ⟨_, ⟨app'.lower arguments.bound⟩, ?_⟩
  intro i need hm
  rcases List.mem_append.mp hm with hm | hm
  · exact (List.mem_append.mp hm).elim
      (argResult.typeAvailable i need) (arguments.outsideAvailable i need)
  · exact arguments.argumentAvailable i need hm

theorem SortableObs.betaExpandOriginal
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered)
    {source target : List VExpr} {locals : List Nat} {σ : Subst}
    {available : Valuation} {A body argument : VExpr} {demand : Profile n} {footprint : Footprint}
    {sourceEnv : VEnv}
    (instantiated : EndpointRef sourceEnv U source (body.inst argument) assigned)
    (argumentChild : SortableComputationalTransfer env U registry target locals σ σ available argument argument A)
    (rawArgument : env.HasType U source argument A)
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (observation : SortableObs env U registry target locals σ (body.inst argument) demand footprint)
    (resources : footprint.Available available) :
    ∃ required, Nonempty (SortableObs env U registry target locals σ (.app (.lam A body) argument)
      demand required) ∧ required.Available available := by
  induction demand generalizing footprint with
  | nil => exact ⟨[], ⟨.legacy .empty⟩, fun _ _ h => nomatch h⟩
  | cons atom rest ih =>
    obtain ⟨selected⟩ := observation.atom List.mem_cons_self
    obtain ⟨firstFootprint, ⟨first⟩, firstAvailable⟩ := selected.observation.betaExpandAtomOriginal henv
      instantiated argumentChild rawArgument closed hTarget substitutions
      (selected.atomizes.available_closed resources closed)
    obtain ⟨tailFootprint, ⟨tail⟩, selection⟩ := observation.subprofile
      (selected := rest) (fun _ h => List.mem_cons_of_mem _ h)
    obtain ⟨lastFootprint, ⟨last⟩, lastAvailable⟩ := ih tail
      (selection.available_closed resources closed)
    exact ⟨firstFootprint ++ lastFootprint, ⟨.union first last⟩,
      fun i need hm => (List.mem_append.mp hm).elim (firstAvailable i need) (lastAvailable i need)⟩

theorem SortableComputationalTransferResult.betaExpandOriginal
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered)
    {source target : List VExpr} {locals : List Nat} {σ τ : Subst}
    {available : Valuation} {A B body argument : VExpr} {demand : Profile n}
    {sourceEnv : VEnv}
    (instantiated : EndpointRef sourceEnv U source (body.inst argument) assigned)
    (argumentChild : SortableComputationalTransfer env U registry target locals τ τ available argument argument A)
    (rawBody : env.HasType U (A :: source) body B)
    (rawArgument : env.HasType U source argument A)
    (formedInstantiated : env.HasType U source (B.inst argument) (.sort bodyLevel))
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (result : SortableComputationalTransferResult env U registry target locals σ τ available
      (body.inst argument) (body.inst argument) (B.inst argument) demand) :
    Nonempty (SortableComputationalTransferResult env U registry target locals σ τ available
      (body.inst argument) (.app (.lam A body) argument) (B.inst argument) demand) := by
  obtain ⟨footprint, ⟨observation⟩, resources⟩ := result.observation.betaExpandOriginal henv
    instantiated argumentChild rawArgument closed hTarget (substitutions.right henv hTarget) result.resources
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
    live := result.live }⟩


end Lean4Lean.AnchoredSource.Adapted
