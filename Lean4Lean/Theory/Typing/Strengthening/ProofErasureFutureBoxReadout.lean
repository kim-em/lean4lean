import Lean4Lean.Theory.Typing.Strengthening.ProofErasureBoxFieldReadout
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointUnion

/-! # Future Box checking is equivalent to future field checking

Independent parameter and major beta paths are typed by forward replay.
The complete ordinary Box guard can then be read at each residual. Interpreted
substitutions preserve the stored whole guard, so the readout retains all
future paths without a global substitution law for the ambient primitives.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private beta_eq from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
open private ProofShape.beta_proj_inv
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitiveBetaResidual
open private BoxCarrierAlignment.family_typed
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointBoxAlignment
variable [Params]

private theorem box_field_beta
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hprim : ∀ {Δ a b}, Primitive D a b → ScopedCompute Step Δ a b)
    (hinert : ∀ {Δ args out}, ¬ Step Δ (ProofShape.mkApps (.const family []) args) out)
    (hi : env.projections family info) (hp : info.nparams = 1) (hf : info.numFields = 1)
    (hshape : info.ctorType.instL [] = .forallE (.sort (.succ .zero))
      (.forallE (.bvar 0) (.app (.const family []) (.bvar 1))))
    (hc : env.constants family = some ⟨0, .forallE (.sort (.succ .zero)) (.sort (.succ .zero))⟩)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort (.succ .zero)))
    (hx : env.HasType univs Γ x (.app (.const family []) A))
    (hy : env.HasType univs Γ y (.app (.const family []) A))
    (hpx : env.HasType univs Γ (.proj family 0 x) A)
    (hpy : env.HasType univs Γ (.proj family 0 y) A)
    (H : BetaStableCarrier Step (proofEraseCtx Γ) (.app (.const family []) (proofErase Γ A))
      (proofErase Γ x) (proofErase Γ y))
    (RC : ProofShape.BetaRed (proofErase Γ A) C)
    (RP : ProofShape.BetaRed (.proj family 0 (proofErase Γ x)) p)
    (RQ : ProofShape.BetaRed (.proj family 0 (proofErase Γ y)) q) :
    JointCarrierGuard Step (proofEraseCtx Γ) C p q := by
  obtain ⟨p', rfl, RX⟩ := ProofShape.beta_proj_inv RP
  obtain ⟨q', rfl, RY⟩ := ProofShape.beta_proj_inv RQ
  obtain ⟨A', PA, EA⟩ := proofErase_beta_replay hΓ hA RC
  obtain ⟨x', PX, EX⟩ := proofErase_beta_replay hΓ hx RX
  obtain ⟨y', PY, EY⟩ := proofErase_beta_replay hΓ hy RY
  have HA := beta_eq hΓ hA PA
  have HX := beta_eq hΓ hx PX
  have HY := beta_eq hΓ hy PY
  have HPX := SimAt.proj henv.orderedStrong hΓ (fun _ ht => HX.toU.of_l henv hΓ ht) A hpx
  have HPY := SimAt.proj henv.orderedStrong hΓ (fun _ ht => HY.toU.of_l henv hΓ ht) A hpy
  have HBox := IsDefEq.appDF (BoxCarrierAlignment.family_typed (Γ := Γ) hc) HA
  have HG := H.1 (.app .refl RC) RX RY
  rw [← EA, ← EX, ← EY] at HG
  have HF := proofErase_box_field_guard hstep hprim hinert hi hp hf hshape hc hΓ HA.hasType.2
    (HBox.defeq HX.hasType.2) (HBox.defeq HY.hasType.2)
    (HA.defeq HPX.hasType.2) (HA.defeq HPY.hasType.2) HG
  simpa only [EA, EX, EY] using HF

/-- A supplied whole Box future certificate yields its complete field
certificate, including independent future reductions of the parameter and
projected majors. The actual projection typings identify the field carrier.
No primitive substitution or carrier-conversion law is assumed. -/
theorem proofErase_future_box_field_guard
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hprim : ∀ {Δ a b}, Primitive D a b → ScopedCompute Step Δ a b)
    (hinert : ∀ {Δ args out}, ¬ Step Δ (ProofShape.mkApps (.const family []) args) out)
    (hi : env.projections family info) (hp : info.nparams = 1) (hf : info.numFields = 1)
    (hshape : info.ctorType.instL [] = .forallE (.sort (.succ .zero))
      (.forallE (.bvar 0) (.app (.const family []) (.bvar 1))))
    (hc : env.constants family = some ⟨0, .forallE (.sort (.succ .zero)) (.sort (.succ .zero))⟩)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort (.succ .zero)))
    (hx : env.HasType univs Γ x (.app (.const family []) A))
    (hy : env.HasType univs Γ y (.app (.const family []) A))
    (hpx : env.HasType univs Γ (.proj family 0 x) A)
    (hpy : env.HasType univs Γ (.proj family 0 y) A)
    (H : BetaStableCarrier Step (proofEraseCtx Γ) (.app (.const family []) (proofErase Γ A))
      (proofErase Γ x) (proofErase Γ y)) :
    BetaStableCarrier Step (proofEraseCtx Γ) (proofErase Γ A)
      (.proj family 0 (proofErase Γ x)) (.proj family 0 (proofErase Γ y)) := by
  refine ⟨fun RC RP RQ => box_field_beta hstep hprim hinert hi hp hf hshape hc
    hΓ hA hx hy hpx hpy H RC RP RQ, ?_⟩
  intro Δ' τ C p q W RC RP RQ
  have HG := H.subst W
  obtain ⟨Γ₀, σ, hΓ₀, EΓ₀, WS, ES⟩ := W hΓ rfl
  simp only [ProofShape.subst] at HG RP RQ
  rw [← proofErase_subst_with hΓ₀ WS hA ES, ← proofErase_subst_with hΓ₀ WS hx ES,
    ← proofErase_subst_with hΓ₀ WS hy ES, ← EΓ₀] at HG
  rw [← proofErase_subst_with hΓ₀ WS hA ES] at RC
  rw [← proofErase_subst_with hΓ₀ WS hx ES] at RP
  rw [← proofErase_subst_with hΓ₀ WS hy ES] at RQ
  rw [← EΓ₀]
  exact box_field_beta hstep hprim hinert hi hp hf hshape hc hΓ₀
    (hA.subst henv WS) (hx.subst henv WS) (hy.subst henv WS)
    (hpx.subst henv WS) (hpy.subst henv WS) HG RC RP RQ

/-- For actual Box majors and their naturally typed projections, whole-record
future checking is equivalent to recursive future field checking. This
inverts arbitrary supplied guards, not only an explicit carrierNested node. -/
theorem proofErase_future_box_iff
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hprim : ∀ {Δ a b}, Primitive D a b → ScopedCompute Step Δ a b)
    (hinert : ∀ {Δ args out}, ¬ Step Δ (ProofShape.mkApps (.const family []) args) out)
    (hi : env.projections family info) (hp : info.nparams = 1) (hf : info.numFields = 1)
    (hshape : info.ctorType.instL [] = .forallE (.sort (.succ .zero))
      (.forallE (.bvar 0) (.app (.const family []) (.bvar 1))))
    (hc : env.constants family = some ⟨0, .forallE (.sort (.succ .zero)) (.sort (.succ .zero))⟩)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort (.succ .zero)))
    (hx : env.HasType univs Γ x (.app (.const family []) A))
    (hy : env.HasType univs Γ y (.app (.const family []) A))
    (hpx : env.HasType univs Γ (.proj family 0 x) A)
    (hpy : env.HasType univs Γ (.proj family 0 y) A)
    (hz : info.nindices = 0) (hadm : (info.resultLevel.inst []).IsNeverZero) :
    BetaStableCarrier Step (proofEraseCtx Γ) (.app (.const family []) (proofErase Γ A))
      (proofErase Γ x) (proofErase Γ y) ↔
    BetaStableCarrier Step (proofEraseCtx Γ) (proofErase Γ A)
      (.proj family 0 (proofErase Γ x)) (.proj family 0 (proofErase Γ y)) :=
  ⟨proofErase_future_box_field_guard hstep hprim hinert hi hp hf hshape hc hΓ hA hx hy hpx hpy,
    fun H => H.box hi hz hp hf hshape hadm⟩

/-- In the concrete joint union, a future Box guard is exactly its future
field guard. Actual projection typings are derived from registration. All
primitive hypotheses are discharged using canonical Eq, sound definitions
and exclusion of this family from unfolding. -/
theorem proofErase_future_union_box_iff
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hD : ∀ levels rhs, ¬ D.unfolds family levels rhs)
    (hi : env.projections family info) (hp : info.nparams = 1) (hf : info.numFields = 1)
    (hshape : info.ctorType.instL [] = .forallE (.sort (.succ .zero))
      (.forallE (.bvar 0) (.app (.const family []) (.bvar 1))))
    (hc : env.constants family = some ⟨0, .forallE (.sort (.succ .zero)) (.sort (.succ .zero))⟩)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort (.succ .zero)))
    (hx : env.HasType univs Γ x (.app (.const family []) A))
    (hy : env.HasType univs Γ y (.app (.const family []) A))
    (hz : info.nindices = 0) (hadm : (info.resultLevel.inst []).IsNeverZero) :
    BetaStableCarrier (ErasedJointUnion D) (proofEraseCtx Γ)
      (.app (.const family []) (proofErase Γ A)) (proofErase Γ x) (proofErase Γ y) ↔
    BetaStableCarrier (ErasedJointUnion D) (proofEraseCtx Γ) (proofErase Γ A)
      (.proj family 0 (proofErase Γ x)) (.proj family 0 (proofErase Γ y)) := by
  apply proofErase_future_box_iff (erased_joint_union_descent heq hs)
    (fun H => .base ⟨0, .inl (.inl H)⟩) ?_ hi hp hf hshape hc hΓ hA hx hy
    (box_projection_typed hi hp hf hz hadm hshape hΓ hx)
    (box_projection_typed hi hp hf hz hadm hshape hΓ hy) hz hadm
  intro Δ args out H
  exact erased_joint_union_no_rigid heq (henv.projectionRigid hi) hD H (constHead_mkApps _ _)

end Lean4Lean.VEnv.Strengthening
