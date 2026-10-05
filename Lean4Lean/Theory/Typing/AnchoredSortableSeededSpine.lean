import Lean4Lean.Theory.Typing.AnchoredOriginalSortableApplicationPreparation

/-! A retained source argument seed is merged with all native formation
cuts before its actual original argument theorem is invoked. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

structure SortableArgumentSeed (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (locals : List Nat) (σ : Subst) (available : Valuation)
    (argument : VExpr) where
  rank : Nat
  demand : Profile rank
  footprint : Footprint
  observation : SortableObs env U registry target locals σ argument demand footprint
  resources : footprint.Available available

/-- An actual finite package for each argument occurrence, in source order.
A conversion does not replace or reinterpret these original source leaves. -/
inductive SortableSpineSeeds (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (locals : List Nat) (σ : Subst) (available : Valuation) : VExpr → Type where
  | constant : SortableSpineSeeds env U registry target locals σ available (.const name levels)
  | app (function : SortableSpineSeeds env U registry target locals σ available f)
      (argument : SortableArgumentSeed env U registry target locals σ available a) :
      SortableSpineSeeds env U registry target locals σ available (.app f a)

structure SortableSeededApplicationInput (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (locals : List Nat) (σ : Subst) (available : Valuation)
    (A B a : VExpr) (result : Profile n) (before : Footprint) where
  residual : SortableCert env U registry target locals σ (B.inst a) true result before
  seed : SortableArgumentSeed env U registry target locals σ available a
  required : Footprint
  collected : SortableFactoredArguments env U registry target locals σ available a required (max n seed.rank)
  support : Profile collected.rank
  domainFootprint : Footprint
  domain : SortableCert env U registry target locals σ A true support domainFootprint
  domainAvailable : domainFootprint.Available available
  guard : LambdaGuard env U registry target σ A
    ⟨A.subst σ, a.subst σ,
      (raiseProfile collected.rank (Nat.le_trans (Nat.le_max_right _ _) collected.bound) seed.demand).union collected.input⟩ support
  body : SortableCert env U registry target (Locals.push locals) (σ.cons (a.subst σ)) B true
    (raiseProfile collected.rank (Nat.le_trans (Nat.le_max_left _ _) collected.bound) result) required

namespace SortableSeededApplicationInput
variable (frame : SortableSeededApplicationInput env U registry target locals σ available A B a result before)

def input : Profile frame.collected.rank :=
  (raiseProfile frame.collected.rank (Nat.le_trans (Nat.le_max_right _ _) frame.collected.bound)
    frame.seed.demand).union frame.collected.input

def key : Key frame.collected.rank := ⟨A.subst σ, a.subst σ, frame.input⟩

def profile : Profile (frame.collected.rank + 1) :=
  .pi (A.subst σ) (B.subst σ.lift) frame.support
    [(frame.key, raiseProfile frame.collected.rank
      (Nat.le_trans (Nat.le_max_left _ _) frame.collected.bound) result)]

def footprint : Footprint := frame.domainFootprint ++ frame.collected.outside

/-- Both the original body seed and every actual type cut are literally
included in the final key input. No key was fixed before their union. -/
theorem seedCovered : ∀ atom ∈ (raiseProfile frame.collected.rank
    (Nat.le_trans (Nat.le_max_right _ _) frame.collected.bound) frame.seed.demand).atoms,
    atom ∈ frame.key.input.atoms := fun _ member => List.mem_append_left _ member

theorem cutsCovered : ∀ atom ∈ frame.collected.input.atoms,
    atom ∈ frame.key.input.atoms := fun _ member => List.mem_append_right _ member

noncomputable def argumentObservation : SortableObs env U registry target locals σ a frame.input
    (frame.seed.footprint ++ frame.collected.argumentFootprint) :=
  .union (frame.seed.observation.raise (Nat.le_trans (Nat.le_max_right _ _) frame.collected.bound))
    frame.collected.observation

theorem argumentResources :
    (frame.seed.footprint ++ frame.collected.argumentFootprint).Available available := by
  intro i need member
  exact (List.mem_append.mp member).elim (frame.seed.resources i need) (frame.collected.argumentAvailable i need)

noncomputable def certificate : SortableCert env U registry target locals σ (.forallE A B) true frame.profile frame.footprint := by
  have bodies : SortableRows env U registry target locals σ A B true frame.support
      [(frame.key, raiseProfile frame.collected.rank
        (Nat.le_trans (Nat.le_max_left _ _) frame.collected.bound) result)] frame.collected.outside := by
    simpa only [List.append_nil, key, input] using
      SortableRows.cons frame.guard frame.body frame.collected.pack frame.cutsCovered SortableRows.nil
  exact .piLiteral frame.domain bodies

theorem resources : frame.footprint.Available available := by
  intro i need member
  exact (List.mem_append.mp member).elim (frame.domainAvailable i need) (frame.collected.outsideAvailable i need)

end SortableSeededApplicationInput



namespace OriginalFactorCut
open OriginalClosureMeasure OriginalEndpointFactor OriginalTail

private theorem one_comp (a : VExpr) (σ : Subst) :
    (Subst.one a).comp σ = σ.cons (a.subst σ) := by
  funext i; cases i <;> rfl

/-- Merge every retained seed and every actual result cut before the fixed
argument theorem supplies its true assigned-type certificate. -/
theorem SortableCert.prepareSeededApplication
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {node : EndpointState sourceEnv U source (.app function argument) assigned}
    {start : Located root node} (view : AppView start)
    (initial : ContextDerivation sourceEnv U rootSource)
    (henv : env.Ordered) (below : sourceEnv ≤ env)
    (closed : available.AtomClosed) (formed : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (tails : SortableTailPairedFits env registry target
      (view.location.contextDerivation initial) locals σ σ available)
    (argumentF : StateHereditaryFundamental env registry
      ((Located.appArgument view.location).contextDerivation initial) view.argument)
    (seed : SortableArgumentSeed env U registry target locals σ available argument)
    {n : Nat} {result : Profile n} {before : Footprint}
    (certificate : SortableCert env U registry target locals σ
      (view.codomainExpression.inst argument) true result before)
    (resources : before.Available available) :
    ∃ frame : SortableSeededApplicationInput env U registry target locals σ available
      view.domainExpression view.codomainExpression argument result before, frame.seed = seed := by
  obtain ⟨required, ⟨body⟩, ⟨cuts⟩⟩ := SortableCert.factorInstAtStart certificate
    view.result (.appResult view.location) locals (Locals.push locals)
  obtain ⟨collected⟩ := cuts.arguments available resources (max n seed.rank)
  rw [one_comp] at body
  have seedBound := Nat.le_trans (Nat.le_max_right n seed.rank) collected.bound
  have resultBound := Nat.le_trans (Nat.le_max_left n seed.rank) collected.bound
  have merged := SortableObs.union (seed.observation.raise seedBound) collected.observation
  have present : (seed.footprint ++ collected.argumentFootprint).Available available :=
    fun i need member => (List.mem_append.mp member).elim
      (seed.resources i need) (collected.argumentAvailable i need)
  obtain ⟨answer⟩ := argumentF target locals σ σ available closed formed substitutions tails merged present
  have typed := lowerProfile.hasType answer.bound answer.typed
  have related := lowerProfile.related answer.bound henv formed answer.related
  have domain := answer.typeCertificate.lower collected.rank answer.bound
  have code := answer.typeCode.lower henv answer.bound
  have raw := (view.argument.sound.defeq.mono below).substDF henv substitutions.wf formed substitutions
  exact ⟨{
    residual := certificate
    seed := seed
    required := required
    collected := collected
    support := _, domainFootprint := answer.typeFootprint, domain := domain
    domainAvailable := answer.typeAvailable
    guard := ⟨typed, domain.formed, .refl, code,
      ⟨raw, raw, _, typed, domain.formed, code, related, related⟩⟩
    body := body.raise resultBound }, rfl⟩

end OriginalFactorCut
end Lean4Lean.AnchoredSource.Adapted
