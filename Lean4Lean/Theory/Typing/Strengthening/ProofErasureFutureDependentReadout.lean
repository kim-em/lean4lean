import Lean4Lean.Theory.Typing.Strengthening.ProofErasureDependentFieldReadout
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointUnion

/-! # Exact future decomposition of a dependent pair guard

At each future major residual, the type fields compare and the value fields
check at one of those types. The chosen side may vary with the residual.
This retains symmetry without postulating carrier transport or exchanging
a future quantifier with a disjunction.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private beta_eq from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
open private ProofShape.beta_proj_inv
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitiveBetaResidual
variable [Params]

/-- Symmetric dependent field checks at every future major residual reconstruct
the full future record guard. The chosen field carrier need not be uniform
across reductions or interpreted substitutions. -/
theorem BetaStableFamily.dependent_pair_pack
    (hi : env.projections family info) (hz : info.nindices = 0)
    (hp : info.nparams = 0) (hf : info.numFields = 2)
    (hshape : info.ctorType.instL [] = .forallE (.sort (.succ .zero))
      (.forallE (.bvar 0) (.const family [])))
    (hadm : (info.resultLevel.inst []).IsNeverZero)
    (H : BetaStableFamily (fun Δ => DependentPairFieldCheck Step Δ family) Δ a b) :
    BetaStableCarrier Step Δ (.const family []) a b := by
  have fixed {C : ProofShape} (R : ProofShape.BetaRed (.const family []) C) :
      C = .const family [] := by
    have RR : ProofShape.BetaRed (ProofShape.mkApps (.const family []) []) C := R
    obtain ⟨ps', rfl, HP⟩ := RR.const_spine
    cases HP
    rfl
  constructor
  · intro C p q RC RP RQ
    cases fixed RC
    exact (H.1 RP RQ).pack hi hz hp hf hshape hadm
  · intro Δ' τ C p q W RC RP RQ
    change ProofShape.BetaRed (.const family []) C at RC
    cases fixed RC
    exact (H.2 W RP RQ).pack hi hz hp hf hshape hadm

/-- The first projections retain an ordinary full future common comparison.
Only the value-field certificate has the residual-dependent orientation. -/
theorem BetaStableFamily.dependent_pair_type_fields
    (H : BetaStableFamily (fun Δ => DependentPairFieldCheck Step Δ family) Δ a b) :
    BetaStableFamily (fun Δ => JointCompare Step Δ true) Δ
      (.proj family 0 a) (.proj family 0 b) := by
  constructor
  · intro p q RP RQ
    obtain ⟨p', rfl, RA⟩ := ProofShape.beta_proj_inv RP
    obtain ⟨q', rfl, RB⟩ := ProofShape.beta_proj_inv RQ
    exact (H.1 RA RB).1
  · intro Δ' τ p q W RP RQ
    obtain ⟨p', rfl, RA⟩ := ProofShape.beta_proj_inv RP
    obtain ⟨q', rfl, RB⟩ := ProofShape.beta_proj_inv RQ
    exact (H.2 W RA RB).1

private theorem pair_fields_beta
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hprim : ∀ {Δ a b}, Primitive D a b → ScopedCompute Step Δ a b)
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (hinert : ∀ {Δ args out}, ¬ Step Δ (ProofShape.mkApps (.const family []) args) out)
    (hi : env.projections family info) (hp : info.nparams = 0) (hf : info.numFields = 2)
    (hz : info.nindices = 0) (hadm : (info.resultLevel.inst []).IsNeverZero)
    (hshape : info.ctorType.instL [] = .forallE (.sort (.succ .zero))
      (.forallE (.bvar 0) (.const family [])))
    (hΓ : OnCtx Γ (env.IsType univs))
    (hx : env.HasType univs Γ x (.const family []))
    (hy : env.HasType univs Γ y (.const family []))
    (H : BetaStableCarrier Step (proofEraseCtx Γ) (.const family [])
      (proofErase Γ x) (proofErase Γ y))
    (RP : ProofShape.BetaRed (proofErase Γ x) p)
    (RQ : ProofShape.BetaRed (proofErase Γ y) q) :
    DependentPairFieldCheck Step (proofEraseCtx Γ) family p q := by
  obtain ⟨x', PX, EX⟩ := proofErase_beta_replay hΓ hx RP
  obtain ⟨y', PY, EY⟩ := proofErase_beta_replay hΓ hy RQ
  have HG := H.1 .refl RP RQ
  rw [← EX, ← EY] at HG ⊢
  exact proofErase_dependent_pair_fields hstep hprim hhead hinert hi hp hf hz hadm hshape
    hΓ (beta_eq hΓ hx PX).hasType.2 (beta_eq hΓ hy PY).hasType.2 HG

/-- Exact future readout of actual typed dependent pairs. The result preserves
all future major paths and substitutions, with the value check at either
residual type field. It asserts neither uniform orientation nor independent
future reduction of that chosen carrier apart from its major. -/
theorem proofErase_future_dependent_pair_fields
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hprim : ∀ {Δ a b}, Primitive D a b → ScopedCompute Step Δ a b)
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (hinert : ∀ {Δ args out}, ¬ Step Δ (ProofShape.mkApps (.const family []) args) out)
    (hi : env.projections family info) (hp : info.nparams = 0) (hf : info.numFields = 2)
    (hz : info.nindices = 0) (hadm : (info.resultLevel.inst []).IsNeverZero)
    (hshape : info.ctorType.instL [] = .forallE (.sort (.succ .zero))
      (.forallE (.bvar 0) (.const family [])))
    (hΓ : OnCtx Γ (env.IsType univs))
    (hx : env.HasType univs Γ x (.const family []))
    (hy : env.HasType univs Γ y (.const family []))
    (H : BetaStableCarrier Step (proofEraseCtx Γ) (.const family [])
      (proofErase Γ x) (proofErase Γ y)) :
    BetaStableFamily (fun Δ => DependentPairFieldCheck Step Δ family)
      (proofEraseCtx Γ) (proofErase Γ x) (proofErase Γ y) := by
  refine ⟨fun RP RQ => pair_fields_beta hstep hprim hhead hinert hi hp hf hz hadm hshape
    hΓ hx hy H RP RQ, ?_⟩
  intro Δ' τ p q W RP RQ
  have HG := H.subst W
  obtain ⟨Γ₀, σ, hΓ₀, EΓ₀, WS, ES⟩ := W hΓ rfl
  simp only [ProofShape.subst] at HG
  rw [← proofErase_subst_with hΓ₀ WS hx ES, ← proofErase_subst_with hΓ₀ WS hy ES, ← EΓ₀] at HG
  rw [← proofErase_subst_with hΓ₀ WS hx ES] at RP
  rw [← proofErase_subst_with hΓ₀ WS hy ES] at RQ
  rw [← EΓ₀]
  exact pair_fields_beta hstep hprim hhead hinert hi hp hf hz hadm hshape hΓ₀
    (hx.subst henv WS) (hy.subst henv WS) HG RP RQ

/-- A full future dependent-pair guard is equivalent to its symmetric field
checks at all future major residuals and interpreted substitutions. -/
theorem proofErase_future_dependent_pair_iff
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hprim : ∀ {Δ a b}, Primitive D a b → ScopedCompute Step Δ a b)
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (hinert : ∀ {Δ args out}, ¬ Step Δ (ProofShape.mkApps (.const family []) args) out)
    (hi : env.projections family info) (hp : info.nparams = 0) (hf : info.numFields = 2)
    (hz : info.nindices = 0) (hadm : (info.resultLevel.inst []).IsNeverZero)
    (hshape : info.ctorType.instL [] = .forallE (.sort (.succ .zero))
      (.forallE (.bvar 0) (.const family [])))
    (hΓ : OnCtx Γ (env.IsType univs))
    (hx : env.HasType univs Γ x (.const family []))
    (hy : env.HasType univs Γ y (.const family [])) :
    BetaStableCarrier Step (proofEraseCtx Γ) (.const family []) (proofErase Γ x) (proofErase Γ y) ↔
    BetaStableFamily (fun Δ => DependentPairFieldCheck Step Δ family)
      (proofEraseCtx Γ) (proofErase Γ x) (proofErase Γ y) :=
  ⟨proofErase_future_dependent_pair_fields hstep hprim hhead hinert hi hp hf hz hadm hshape hΓ hx hy,
    fun H => H.dependent_pair_pack hi hz hp hf hshape hadm⟩

/-- Concrete canonical-Eq union readout, discharging the primitive hypotheses
with sound declarations and local exclusion of the record family from unfolding. -/
theorem proofErase_future_union_dependent_pair_iff
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hD : ∀ levels rhs, ¬ D.unfolds family levels rhs)
    (hi : env.projections family info) (hp : info.nparams = 0) (hf : info.numFields = 2)
    (hz : info.nindices = 0) (hadm : (info.resultLevel.inst []).IsNeverZero)
    (hshape : info.ctorType.instL [] = .forallE (.sort (.succ .zero))
      (.forallE (.bvar 0) (.const family [])))
    (hΓ : OnCtx Γ (env.IsType univs))
    (hx : env.HasType univs Γ x (.const family []))
    (hy : env.HasType univs Γ y (.const family [])) :
    BetaStableCarrier (ErasedJointUnion D) (proofEraseCtx Γ) (.const family [])
      (proofErase Γ x) (proofErase Γ y) ↔
    BetaStableFamily (fun Δ => DependentPairFieldCheck (ErasedJointUnion D) Δ family)
      (proofEraseCtx Γ) (proofErase Γ x) (proofErase Γ y) := by
  apply proofErase_future_dependent_pair_iff (erased_joint_union_descent heq hs)
    (fun H => .base ⟨0, .inl (.inl H)⟩) (@erased_joint_union_head _ D) ?_
    hi hp hf hz hadm hshape hΓ hx hy
  intro Δ args out H
  exact erased_joint_union_no_rigid heq (henv.projectionRigid hi) hD H (constHead_mkApps _ _)

end Lean4Lean.VEnv.Strengthening
