import Lean4Lean.Theory.Typing.Strengthening.ProofErasureConstructorDemandUnitArrows
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureNativeUnitProfile

/-! # Canonical arguments for arbitrary finite unit-arrow profiles

Normalize the caller's fresh variable before substituting the supplied argument.
This removes all computational demands on that argument for literal simple unit
headers. It does not expose an ordinarily convertible header, or preserve native
recovery through arbitrary computation of the caller.
-/
namespace Lean4Lean.VEnv.Strengthening.ConstructorDemand
open _root_.Lean4Lean Params ProofShape
variable [Params] {D : PureObservation.Definitions}

/-- The closed constant function at a simple unit profile; function domains
may themselves have arbitrary finite order. -/
def UnitArrows.canonical (s uc : Name) : UnitArrows → ProofShape
  | .unit => .const uc []
  | .arrow A B => .lam (A.raw s) (B.canonical s uc)

omit [Params] in
/-- Literal simple headers do not change under weakening at any depth. -/
theorem UnitArrows.raw_liftN (A : UnitArrows) : (A.raw s).liftN n k = A.raw s := by
  induction A generalizing k with
  | unit => rfl
  | arrow A B ihA ihB => simp only [raw, ProofShape.liftN, ihA, ihB]

omit [Params] in
/-- The canonical value is closed even underneath its function binders. -/
theorem UnitArrows.canonical_liftN (A : UnitArrows) :
    (A.canonical s uc).liftN n k = A.canonical s uc := by
  induction A generalizing k with
  | unit => rfl
  | arrow A B _ ihB => simp only [canonical, ProofShape.liftN, raw_liftN, ihB]

omit [Params] in
/-- Substitution cannot change the canonical value or its annotations. -/
theorem UnitArrows.canonical_subst (A : UnitArrows) :
    (A.canonical s uc).subst σ = A.canonical s uc := by
  induction A generalizing σ with
  | unit => rfl
  | arrow A B _ ihB => simp only [canonical, ProofShape.subst, raw_subst, ihB]

variable (hi : env.projections s (PositiveHeaderRegistration.info 0 [] s uc))
variable (hS : env.HasType univs [] (.const s []) (.sort (.succ .zero)))
local notation "U" => unitCarrier hi hS
include hi hS

/-- Every finite simple unit type supplies a concrete dependent profile.
No exposure or directed-conversion premise remains in this construction. -/
theorem UnitArrows.profile (A : UnitArrows) (hΓ : OnCtx Γ (env.IsType univs)) :
    NativeUnitProfile D s uc (proofEraseCtx Γ) (A.raw s) (A.canonical s uc) := by
  induction A generalizing Γ with
  | unit => exact .unit
  | arrow A B _ ihB =>
    have hA : env.HasType univs Γ (A.control U).expr (.sort (A.control U).level) :=
      HeterogeneousControl.ControlType.typed A.wf
    have hΓA : OnCtx ((A.control U).expr :: Γ) (env.IsType univs) := ⟨hΓ, _, hA⟩
    have EΓ : proofEraseCtx ((A.control U).expr :: Γ) = A.raw s :: proofEraseCtx Γ := by
      simp only [proofEraseCtx, A.erase hi hS hΓ]
    have SD : DomainSort (proofEraseCtx Γ) (A.raw s) (A.control U).level :=
      ⟨Γ, _, hΓ, rfl, hA, A.erase hi hS hΓ⟩
    have hp : ¬ (A.control U).level ≈ .zero := by
      intro E
      exact (A.control U).level_ne_zero [] (congrFun E [])
    exact .pi SD hp (EΓ ▸ ihB hΓA)

/-- Actual native recovery of a literal simple header suffices to normalize
the recovered value. Eta is performed while its native certificate is still
available; every subsequent result application again has a literal header.
No normalization or recovery principle for convertible types is assumed. -/
theorem UnitArrows.native_canonical (A : UnitArrows)
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D)
      (proofEraseCtx Γ) e (A.raw s)) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D)
      (proofEraseCtx Γ) e (A.canonical s uc) :=
  (A.profile hi hS hΓ).compute heq hs hi rfl rfl rfl RN

/-- A caller with a literal simple unit domain replaces any raw supplied
argument by the canonical value. The argument has no typing, native-recovery,
observation, or computation-history premise. The caller's result may depend on
its parameter. Normalization occurs under the fresh binder before beta. -/
theorem UnitArrows.caller_canonical (A : UnitArrows)
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D)
      (proofEraseCtx Γ) f (.forallE (A.raw s) B)) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (.app f x) (.app f (A.canonical s uc)) := by
  have hA : env.HasType univs Γ (A.control U).expr (.sort (A.control U).level) :=
    HeterogeneousControl.ControlType.typed A.wf
  have SD : DomainSort (proofEraseCtx Γ) (A.raw s) (A.control U).level :=
    ⟨Γ, _, hΓ, rfl, hA, A.erase hi hS hΓ⟩
  have hp : ¬ (A.control U).level ≈ .zero := by
    intro E
    exact (A.control U).level_ne_zero [] (congrFun E [])
  exact (A.profile hi hS hΓ).caller heq hs hi rfl rfl rfl SD hp RN

end Lean4Lean.VEnv.Strengthening.ConstructorDemand
