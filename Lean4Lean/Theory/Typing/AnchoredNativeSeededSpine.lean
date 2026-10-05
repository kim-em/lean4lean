import Lean4Lean.Theory.Typing.AnchoredNativeSpineCertificate

/-! A finite original observation seed for each actual argument is merged
with inverse-substitution type cuts BEFORE invoking the original argument
child. These are finite source records, not semantic callbacks. Producing the
seeds from an initial native capture ledger remains a separate obligation. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

structure NativeArgumentSeed (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (locals : List Nat) (σ : Subst) (available : Valuation)
    (argument : VExpr) where
  rank : Nat
  demand : Profile rank
  footprint : Footprint
  observation : Obs env U registry target locals σ argument demand footprint
  resources : footprint.Available available

/-- An actual finite package for each argument occurrence, in source order.
A conversion does not replace or reinterpret these original source leaves. -/
inductive NativeSpineSeeds (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (locals : List Nat) (σ : Subst) (available : Valuation) : VExpr → Type where
  | constant : NativeSpineSeeds env U registry target locals σ available (.const name levels)
  | app (function : NativeSpineSeeds env U registry target locals σ available f)
      (argument : NativeArgumentSeed env U registry target locals σ available a) :
      NativeSpineSeeds env U registry target locals σ available (.app f a)

structure SeededApplicationCodeInput (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (locals : List Nat) (σ : Subst) (available : Valuation)
    (A B a : VExpr) (result : Profile n) (before : Footprint) where
  residual : CodeCert env U registry target locals σ (B.inst a) result before
  seed : NativeArgumentSeed env U registry target locals σ available a
  required : Footprint
  cuts : InstFootprint env U registry target locals σ a 0 before required
  collected : FactoredArguments env U registry target locals σ available a required (max n seed.rank)
  support : Profile collected.rank
  domainFootprint : Footprint
  domain : CodeCert env U registry target locals σ A support domainFootprint
  domainAvailable : domainFootprint.Available available
  guard : LambdaGuard env U registry target σ A
    ⟨A.subst σ, a.subst σ,
      (raiseProfile collected.rank (Nat.le_trans (Nat.le_max_right _ _) collected.bound) seed.demand).union collected.input⟩ support
  body : CodeCert env U registry target (Locals.push locals) (σ.cons (a.subst σ)) B
    (raiseProfile collected.rank (Nat.le_trans (Nat.le_max_left _ _) collected.bound) result) required

namespace SeededApplicationCodeInput
variable (frame : SeededApplicationCodeInput env U registry target locals σ available A B a result before)

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

noncomputable def argumentObservation : Obs env U registry target locals σ a frame.input
    (frame.seed.footprint ++ frame.collected.argumentFootprint) :=
  .union (frame.seed.observation.raise (Nat.le_trans (Nat.le_max_right _ _) frame.collected.bound))
    frame.collected.observation

theorem argumentResources :
    (frame.seed.footprint ++ frame.collected.argumentFootprint).Available available := by
  intro i need member
  exact (List.mem_append.mp member).elim (frame.seed.resources i need) (frame.collected.argumentAvailable i need)

def certificate : CodeCert env U registry target locals σ (.forallE A B) frame.profile frame.footprint := by
  have bodies : PiRows env U registry target locals σ A B frame.support
      [(frame.key, raiseProfile frame.collected.rank
        (Nat.le_trans (Nat.le_max_left _ _) frame.collected.bound) result)] frame.collected.outside := by
    simpa only [List.append_nil, key, input] using
      PiRows.cons frame.guard frame.body frame.collected.pack frame.cutsCovered PiRows.nil
  refine .seed (.pi frame.domain PiGuard.literal bodies) (Profile.HasType.pi_iff.mpr ⟨?_, ?_⟩)
  · refine Profile.WF.pi_iff.mpr ⟨frame.domain.formed, ?_⟩
    intro key output member
    cases List.mem_singleton.mp member
    exact ⟨frame.guard.inputTyped, frame.body.formed.wf_value⟩
  · intro key output member
    cases List.mem_singleton.mp member
    exact frame.body.formed

theorem resources : frame.footprint.Available available := by
  intro i need member
  exact (List.mem_append.mp member).elim (frame.domainAvailable i need) (frame.collected.outsideAvailable i need)

end SeededApplicationCodeInput

private theorem one_comp (a : VExpr) (σ : Subst) :
    (Subst.one a).comp σ = σ.cons (a.subst σ) := by
  funext i; cases i <;> rfl

/-- The original argument theorem is invoked exactly once, on the union of
the actual original seed and all collected type cuts, at their common grade. -/
theorem CodeCert.seededApplicationInput
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hle : sourceEnv ≤ env)
    {source target : List VExpr} {locals : List Nat} {σ : Subst} {available : Valuation}
    {A B a : VExpr}
    (argument : OriginalTypePayload sourceEnv env U registry source a A)
    (seed : NativeArgumentSeed env U registry target locals σ available a)
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (fits : PairedFits env U registry source target locals σ σ available)
    {result : Profile n} {before : Footprint}
    (certificate : CodeCert env U registry target locals σ (B.inst a) result before)
    (resources : before.Available available) :
    ∃ frame : SeededApplicationCodeInput env U registry target locals σ available A B a result before,
      frame.seed = seed := by
  obtain ⟨required, ⟨body⟩, ⟨cuts⟩⟩ := certificate.factorInst B a 0 rfl σ rfl locals (Locals.push locals)
  simp only [Subst.liftN, one_comp] at body
  obtain ⟨packed⟩ := cuts.arguments available resources (max n seed.rank)
  have seedBound := Nat.le_trans (Nat.le_max_right n seed.rank) packed.bound
  have resultBound := Nat.le_trans (Nat.le_max_left n seed.rank) packed.bound
  have merged := Obs.union (seed.observation.raise seedBound) packed.observation
  have mergedAvailable : (seed.footprint ++ packed.argumentFootprint).Available available := by
    intro i need member
    exact (List.mem_append.mp member).elim (seed.resources i need) (packed.argumentAvailable i need)
  obtain ⟨value⟩ := (argument.2 target locals σ σ available closed hTarget substitutions fits).1
    merged mergedAvailable
  have raw := (argument.1.defeq.mono hle).substDF henv substitutions.wf hTarget substitutions
  have related := value.requestedRelated henv hTarget
  have domain := value.requestedCertificate
  have code := TypeRelated.lower henv value.bound value.typeCode
  exact ⟨{
    residual := certificate
    seed := seed
    required := required
    cuts := cuts
    collected := packed
    support := lowerProfile packed.rank value.bound value.support
    domainFootprint := value.typeFootprint
    domain := domain
    domainAvailable := value.typeAvailable
    guard := ⟨value.requestedTyped, domain.formed, .refl, code,
      ⟨raw, raw, _, value.requestedTyped, domain.formed, code, related, related⟩⟩
    body := body.raise resultBound }, rfl⟩

inductive NativeSeededSpineCertificate (sourceEnv env : VEnv) (U : Nat)
    (registry : CanonicalHead.Registry) (source target : List VExpr)
    (locals : List Nat) (σ : Subst) (available : Valuation) (name : Name) (levels : List VLevel) :
    (expression assigned : VExpr) → {n : Nat} → Profile n → Footprint → Type where
  | constant {info : VConstant}
      (lookup : sourceEnv.constants name = some info)
      (formation : SourcePiFormation (OriginalTypePayload sourceEnv env U registry)
        source (info.type.instL levels))
      (certificate : CodeCert env U registry target locals σ (info.type.instL levels) profile footprint)
      (resources : footprint.Available available) :
      NativeSeededSpineCertificate sourceEnv env U registry source target locals σ available name levels
        (.const name levels) (info.type.instL levels) profile footprint
  | application
      (frame : SeededApplicationCodeInput env U registry target locals σ available A B a result before)
      (function : NativeSeededSpineCertificate sourceEnv env U registry source target locals σ available name levels
        f (.forallE A B) frame.profile frame.footprint) :
      NativeSeededSpineCertificate sourceEnv env U registry source target locals σ available name levels
        (.app f a) (B.inst a) result before
  | conversion
      {original : sourceEnv.IsDefEqStrong U source A B (.sort level)}
      (edge : OriginalPayload sourceEnv env U registry original)
      (certificate : CodeCert env U registry target locals σ B profile footprint)
      (transfer : CodeTransferResult env U registry target locals σ σ available B A profile)
      (term : NativeSeededSpineCertificate sourceEnv env U registry source target locals σ available name levels
        expression A profile transfer.footprint) :
      NativeSeededSpineCertificate sourceEnv env U registry source target locals σ available name levels
        expression B profile footprint

/-- Recover the original seeds literally, so no application seed can silently
be dropped by the backward certificate construction. -/
def NativeSeededSpineCertificate.seeds
    (spine : NativeSeededSpineCertificate sourceEnv env U registry source target locals σ available
      name levels expression assigned profile footprint) :
    NativeSpineSeeds env U registry target locals σ available expression :=
  match spine with
  | .constant .. => .constant
  | .application frame function => .app function.seeds frame.seed
  | .conversion _ _ _ term => term.seeds

/-- Complete original-tree recursion with finite source seeds. The returned
backward derivation contains exactly the supplied seeds, including through
all outer and intermediate conversion nodes. -/
theorem HasTypeStrong.seededSpineCertificate
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hle : sourceEnv ≤ env)
    (earlier : ∀ {Γ left right type} (H : sourceEnv.IsDefEqStrong U Γ left right type),
      OriginalPayload sourceEnv env U registry H)
    {source target : List VExpr} {locals : List Nat} {σ : Subst} {available : Valuation}
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (fits : PairedFits env U registry source target locals σ σ available)
    {expression assigned : VExpr} {structural : Bool} {name : Name} {levels : List VLevel}
    (original : sourceEnv.HasTypeStrong U source expression assigned structural)
    (head : expression.getAppFnArgs.1 = .const name levels)
    (seeds : NativeSpineSeeds env U registry target locals σ available expression)
    {profile : Profile n} {footprint : Footprint}
    (certificate : CodeCert env U registry target locals σ assigned profile footprint)
    (resources : footprint.Available available) :
    ∃ spine : NativeSeededSpineCertificate sourceEnv env U registry source target locals σ available name levels
      expression assigned profile footprint, spine.seeds = seeds := by
  induction original generalizing n footprint with
  | const lookup hw hl hu closedType type ihClosed ihType =>
    simp only [VExpr.getAppFnArgs_const] at head
    cases head
    cases seeds
    exact ⟨.constant lookup (earlier type.refl).leftFormation certificate resources, rfl⟩
  | app hu hv domain codomain whole function argument result ihD ihC ihW ihF ihA ihR =>
    cases seeds with
    | app functionSeeds argumentSeed =>
      obtain ⟨frame, seedEq⟩ := certificate.seededApplicationInput henv hle
        ⟨argument.refl, (earlier argument.refl).joint⟩ argumentSeed closed hTarget substitutions fits resources
      obtain ⟨tail, tailEq⟩ := ihF substitutions fits
        (by simpa only [VExpr.getAppFnArgs_app] using head) functionSeeds frame.certificate frame.resources
      exact ⟨.application frame tail, by simp only [NativeSeededSpineCertificate.seeds, tailEq, seedEq]⟩
  | base _ ih => exact ih substitutions fits head seeds certificate resources
  | defeq hu conversion leftType rightType term ihL ihR ih =>
    obtain ⟨transfer⟩ := certificate.transfer_graded henv hscoped hTarget closed
      ((earlier conversion).joint.symm target locals σ σ available closed hTarget substitutions fits).1 resources
    obtain ⟨tail, same⟩ := ih substitutions fits head seeds transfer.certificate transfer.available
    exact ⟨.conversion (earlier conversion) certificate transfer tail, same⟩
  | bvar | sort' | elim | proj | lam | forallE =>
    simp only [VExpr.getAppFnArgs] at head
    contradiction

theorem NativeSeededSpineCertificate.rootCode
    (spine : NativeSeededSpineCertificate sourceEnv env U registry source target locals σ available
      name levels expression assigned profile footprint) :
    ∃ info, sourceEnv.constants name = some info ∧
      SourcePiFormation (OriginalTypePayload sourceEnv env U registry) source (info.type.instL levels) ∧
      ∃ rank, ∃ support : Profile rank, ∃ required,
        Nonempty (CodeCert env U registry target locals σ (info.type.instL levels) support required) ∧
        required.Available available := by
  induction spine with
  | constant lookup formation certificate resources => exact ⟨_, lookup, formation, _, _, _, ⟨certificate⟩, resources⟩
  | application frame function ih => exact ih
  | conversion edge certificate transfer term ih => exact ih

theorem NativeSeededSpineCertificate.closedRootCode
    (spine : NativeSeededSpineCertificate sourceEnv env U registry source target locals σ available
      name levels expression assigned profile footprint)
    {info : VConstant} (lookup : sourceEnv.constants name = some info)
    (closed : (info.type.instL levels).Closed) :
    ∃ rank, ∃ support : Profile rank,
      Nonempty (CodeCert env U registry target [] σ (info.type.instL levels) support []) := by
  obtain ⟨actual, found, formation, rank, support, required, ⟨certificate⟩, resources⟩ := spine.rootCode
  have equal : actual = info := Option.some.inj (found.symm.trans lookup)
  cases equal
  have empty : required = [] := by
    cases required with
    | nil => rfl
    | cons head tail =>
      obtain ⟨i, need⟩ := head
      have impossible := certificate.scoped closed i need List.mem_cons_self
      omega
  subst required
  exact ⟨rank, support, ⟨certificate.closedSource closed [] σ⟩⟩

end Lean4Lean.AnchoredSource.Adapted
