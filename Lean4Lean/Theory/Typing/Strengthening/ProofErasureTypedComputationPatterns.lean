import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypedComputationCompleteness

/-! # Isolating proposition-source singleton pattern coverage

Actual stored patterns have empty checks. Their guarded ordinary-core version
already computes unless the recursor has a large target and a zero source level.
Only that exceptional branch remains in computation-chain completeness.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params] {D : PureObservation.Definitions}

/-- Missing singleton coverage: realize the actual registered pattern equation
when its recursor eliminates a proposition into a large target. Both endpoints
are typed, but no family comparison, native recovery or joining certificate is
assumed. These are precisely the raw patterns excluded by the ordinary guard. -/
def TypedSingletonPatternChainClosure (D : PureObservation.Definitions) : Prop :=
  ∀ {Γ p} {r : p.RHS × p.Check} {e A ls captures data},
    OnCtx Γ (env.IsType univs) → env.pats p r →
    env.recursorRegistry p.headConst = some data → data.largeTarget = true →
    (data.schema.sourceLevel data.owner data.levels).inst ls ≈ .zero →
    p.Matches e ls captures → env.HasType univs Γ e A →
    env.HasType univs Γ (r.1.apply ls captures) A →
    TypedComputationEq D Γ e (r.1.apply ls captures) A

/-- A registered pattern outside the proposition-source large-elimination
branch computes already at stage zero. Its empty stored checks need no chains. -/
theorem TypedComputationEq.pattern_nonzero
    (hs : D.Sound env univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hguard : ∀ {p r}, GuardedIotaPattern env p r → Pat p r)
    (hΓ : OnCtx Γ (env.IsType univs)) (hp : env.pats p r)
    (hl : env.recursorRegistry p.headConst = some data)
    (hz : ¬ (data.largeTarget = true ∧ (data.schema.sourceLevel data.owner data.levels).inst ls ≈ .zero))
    (hm : p.Matches e ls captures) (ht : env.HasType univs Γ e A) :
    TypedComputationEq D Γ e (r.1.apply ls captures) A := by
  obtain ⟨_, _, _, _, data', rfl, hl', _, _, hG⟩ := henv.pats_guarded hp
  rw [SimplePattern.iota_headConst, hl'] at hl
  cases Option.some.inj hl
  exact TypedComputationEq.of_pattern_trace hs hcon hΓ ht
    (.pattern (r := (r.1, data.guard _)) (hguard hG) hm (InductiveSignature.RecursorData.guard_OK.mpr hz))

/-- The sole missing raw-pattern case is proposition-source large elimination.
Well-formedness supplies the guarded registration and disposes of all other
patterns; no arbitrary checked-capture completeness is needed. -/
theorem TypedSingletonPatternChainClosure.pattern_closure
    (hs : D.Sound env univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hguard : ∀ {p r}, GuardedIotaPattern env p r → Pat p r)
    (HS : TypedSingletonPatternChainClosure D) : TypedPatternChainClosure D := by
  intro Γ p r e A ls captures chk hΓ hp hm ht hr _ _
  obtain ⟨_, _, _, _, data, he, hl, _, _, _⟩ := henv.pats_guarded hp
  have hl' : env.recursorRegistry p.headConst = some data := by
    rw [he, SimplePattern.iota_headConst]; exact hl
  by_cases hz : data.largeTarget = true ∧ (data.schema.sourceLevel data.owner data.levels).inst ls ≈ .zero
  · exact HS hΓ hp hl' hz.1 hz.2 hm ht hr
  · exact TypedComputationEq.pattern_nonzero hs hcon hguard hΓ hp hl' hz hm ht

/-- Singleton pattern coverage implies ordinary computation-chain completeness
for the concrete presentation. The singleton premise and type-fork joining are
still open; this theorem claims no strict reduction of the strengthening goal. -/
theorem TypedComputationEq.of_defeq_of_singleton_closure
    (heq : env.HasCanonicalEq)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hqpat : QuotRegistered env → Pat quotPattern (quotPatternRHS, quotPatternCheck))
    (hguard : ∀ {p r}, GuardedIotaPattern env p r → Pat p r)
    (HS : TypedSingletonPatternChainClosure EnvironmentCore.definitions)
    (hΓ : OnCtx Γ (env.IsType univs)) (H : env.IsDefEq univs Γ a b A) :
    TypedComputationEq EnvironmentCore.definitions Γ a b A :=
  TypedComputationEq.of_defeq_of_pattern_closure heq hcon hqpat
    (HS.pattern_closure EnvironmentCore.sound hcon hguard) hΓ H

end Lean4Lean.VEnv.Strengthening
