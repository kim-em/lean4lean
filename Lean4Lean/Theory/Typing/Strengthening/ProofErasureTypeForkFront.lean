import Lean4Lean.Theory.Typing.Strengthening.ProofErasureComputationalHistory
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCommonCoverageFront

/-! # Type-fork joining suffices for the proposition front

Declaration-history completeness now turns ordinary type equalities into
computation chains without separate pattern or declaration assumptions. The
remaining fork-joining premise turns these chains into joins; typed computation
descent then gives the proposition front. Fork joining itself is still open.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params]

/-- Type-fork joining gives computational joins for every ordinary type
equality in the concrete presentation. No pattern, declaration-history or
generic data-domain coverage hypothesis remains. -/
theorem type_conversion_join_of_type_forks
    (heq : env.HasCanonicalEq) (HF : TypeForkJoin EnvironmentCore.definitions)
    (hregistry : recursorData = env.recursorRegistry)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hqpat : QuotRegistered env → Pat quotPattern (quotPatternRHS, quotPatternCheck))
    (hguard : ∀ {p r}, GuardedIotaPattern env p r → Pat p r) :
    StaticStructureTypeConversionJoin EnvironmentCore.definitions := by
  intro Γ A B u hΓ H
  exact (computational_typing_of_history heq HF hregistry hcon hqpat hguard hΓ H).1.type_join
    heq EnvironmentCore.sound HF hΓ

/-- The remaining type-fork joining premise implies proposition strengthening.
This is a sufficiency theorem, not a proof of fork joining or of strict
smallness relative to the original proposition-front obligation. -/
theorem propositionFront_of_type_forks
    (heq : env.HasCanonicalEq) (HF : TypeForkJoin EnvironmentCore.definitions)
    (hregistry : recursorData = env.recursorRegistry)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hqpat : QuotRegistered env → Pat quotPattern (quotPatternRHS, quotPatternCheck))
    (hguard : ∀ {p r}, GuardedIotaPattern env p r → Pat p r) : PropositionFront :=
  StaticStructureTypeConversionJoin.propositionFront heq EnvironmentCore.sound
    (type_conversion_join_of_type_forks heq HF hregistry hcon hqpat hguard)

omit [Params] in
/-- In the canonical concrete presentation, the only remaining hypothesis is
type-fork joining. No presentation-coverage assumptions need to be supplied. -/
theorem canonical_propositionFront_of_type_forks {E : VEnv}
    (hE : E.WF) (heq : E.HasCanonicalEq) (U : Nat)
    (HF : letI := hE.params U; TypeForkJoin EnvironmentCore.definitions) :
    letI := hE.params U; PropositionFront := by
  letI := hE.params U
  intro Γ Q P R hΓ hQ hP hR H
  exact propositionFront_of_type_forks heq HF rfl (fun H => H)
    (fun H => .inr (.inl (.intro H))) (fun H => .inr (.inr H)) hΓ hQ hP hR H

end Lean4Lean.VEnv.Strengthening
