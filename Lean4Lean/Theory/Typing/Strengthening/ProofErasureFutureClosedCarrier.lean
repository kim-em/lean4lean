import Lean4Lean.Theory.Typing.Strengthening.ProofErasureFutureComparedRecord

/-! # Arbitrary future guards transported from a closed rigid carrier

A typed comparison with a constant carrying no universe or term arguments
forces the target to compute to that exact constant. The supplied guard may
contain arbitrary recursive dependent fields; it is not rebuilt from common
field comparisons or structural subsingleton evidence.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private beta_eq from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
variable [Params]

/-- Typed comparison with a rigid nullary constant exposes the exact constant.
Actual source and target typings force the exposed universe list to be empty. -/
theorem proofErase_compared_closed_carrier_compute
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hn : ∀ {Δ ls args out}, ¬ Step Δ (ProofShape.mkApps (.const family ls) args) out)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ (.const family []) (.sort u))
    (hU : env.HasType univs Γ U (.sort v))
    (HC : JointCompare Step (proofEraseCtx Γ) mode (.const family []) (proofErase Γ U)) :
    ScopedCompute Step (proofEraseCtx Γ) (proofErase Γ U) (.const family []) := by
  have EA : proofErase Γ (.const family []) = .const family [] :=
    if_neg (not_isProof_of_sort hΓ hA)
  have HC' : JointCompare Step (proofEraseCtx Γ) mode
      (proofErase Γ (.const family [])) (proofErase Γ U) := by rw [EA]; exact HC
  have HC' := proofErase_joint_types_inferred hstep hΓ hA hU HC'
  rw [EA] at HC'
  obtain ⟨ls', ps', R, hlen⟩ := JointCompare.const_spine_exposure (args := []) hn HC'
  have hps : ps' = [] := by simpa using hlen
  subst ps'
  obtain ⟨F, HU, EF⟩ := proofErase_scoped_compute_realize hstep hΓ hU rfl rfl R
  obtain ⟨args, rfl, Eargs⟩ := proofErase_const_spine_inv EF
  have hargs : args = [] := by
    have HH := congrArg List.length Eargs
    simpa using HH.symm
  subst args
  obtain ⟨ci, Hci, _, hzero⟩ := hA.const_inv henv hΓ
  obtain ⟨ci', Hci', _, hls⟩ := HU.hasType.2.const_inv henv hΓ
  rw [Hci] at Hci'
  cases Option.some.inj Hci'
  have hnil : ls' = [] := by simpa using hls.trans hzero.symm
  subst ls'
  exact R

/-- A recovered application domain compared with a closed assigned carrier
accepts any supplied guard at that carrier, including dependent record guards.
The exact exposure path builds the native argument guard. This requires the
actual recovery/type comparison; it makes no coverage claim for all typings. -/
theorem proofErase_joint_application_of_compared_recovery_closed_carrier
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (hn : ∀ {Δ ls args out}, ¬ Step Δ (ProofShape.mkApps (.const family ls) args) out)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (.forallE (.const family []) B))
    (R : ScopedTypeRecovery Step (proofEraseCtx Γ) (proofErase Γ f) T)
    (HC : JointCompare Step (proofEraseCtx Γ) mode T
      (proofErase Γ (.forallE (.const family []) B)))
    (HG : JointCarrierGuard Step (proofEraseCtx Γ) (.const family []) a b)
    (Hfg : JointCompare Step (proofEraseCtx Γ) false (proofErase Γ f) g) :
    JointCompare Step (proofEraseCtx Γ) resultMode
      (.app (proofErase Γ f) a) (.app g b) := by
  obtain ⟨A, C, hfAC, RD, HD⟩ := proofErase_joint_recovered_pi_domain hstep hhead hΓ hf R HC
  obtain ⟨_, hPi⟩ := hf.isType henv hΓ
  obtain ⟨⟨_, hSource⟩, _, _⟩ := hPi.forallE_inv henv
  obtain ⟨_, hPi'⟩ := hfAC.isType henv hΓ
  obtain ⟨⟨_, hTarget⟩, _, _⟩ := hPi'.forallE_inv henv
  have EA : proofErase Γ (.const family []) = .const family [] :=
    if_neg (not_isProof_of_sort hΓ hSource)
  rw [EA] at HD
  have RC := proofErase_compared_closed_carrier_compute hstep hn hΓ hSource hTarget HD
  exact .appCarrier RD Hfg (.carrierCompute RC HG)

private theorem closed_carrier_beta
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hn : ∀ {Δ ls args out}, ¬ Step Δ (ProofShape.mkApps (.const family ls) args) out)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ (.const family []) (.sort u))
    (hU : env.HasType univs Γ U (.sort v))
    (HC : BetaStableFamily (fun Δ => JointCompare Step Δ mode)
      (proofEraseCtx Γ) (.const family []) (proofErase Γ U))
    (HG : BetaStableCarrier Step (proofEraseCtx Γ) (.const family []) a b)
    (RC : ProofShape.BetaRed (proofErase Γ U) C)
    (RA : ProofShape.BetaRed a p) (RB : ProofShape.BetaRed b q) :
    JointCarrierGuard Step (proofEraseCtx Γ) C p q := by
  obtain ⟨U', PU, EU⟩ := proofErase_beta_replay hΓ hU RC
  have HT : JointCompare Step (proofEraseCtx Γ) mode (.const family []) (proofErase Γ U') := by
    rw [EU]
    exact HC.1 .refl RC
  have R := proofErase_compared_closed_carrier_compute hstep hn hΓ hA
    (beta_eq hΓ hU PU).hasType.2 HT
  rw [EU] at R
  exact .carrierCompute R (HG.1 .refl RA RB)

/-- A supplied future type comparison transports any full future guard from a
closed rigid carrier to the compared type. Endpoint typings and structural
subsingleton evidence are not used to build this raw guard; reflection at the
target still requires actual endpoint typings there. -/
theorem proofErase_future_compared_closed_carrier
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hn : ∀ {Δ ls args out}, ¬ Step Δ (ProofShape.mkApps (.const family ls) args) out)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ (.const family []) (.sort u))
    (hU : env.HasType univs Γ U (.sort v))
    (HC : BetaStableFamily (fun Δ => JointCompare Step Δ mode)
      (proofEraseCtx Γ) (.const family []) (proofErase Γ U))
    (HG : BetaStableCarrier Step (proofEraseCtx Γ) (.const family []) a b) :
    BetaStableCarrier Step (proofEraseCtx Γ) (proofErase Γ U) a b := by
  refine ⟨fun RC RA RB => closed_carrier_beta hstep hn hΓ hA hU HC HG RC RA RB, ?_⟩
  intro Δ' τ C p q W RC RA RB
  have HT := HC.subst W
  have HG' := HG.subst W
  obtain ⟨Γ₀, σ, hΓ₀, EΓ₀, WS, ES⟩ := W hΓ rfl
  simp only [ProofShape.subst] at HT HG'
  rw [← proofErase_subst_with hΓ₀ WS hU ES, ← EΓ₀] at HT
  rw [← EΓ₀] at HG'
  rw [← proofErase_subst_with hΓ₀ WS hU ES] at RC
  rw [← EΓ₀]
  exact closed_carrier_beta hstep hn hΓ₀ (hA.subst henv WS) (hU.subst henv WS) HT HG' RC RA RB

/-- For a registered nullary record in the canonical-Eq union, future type
comparison transports its arbitrary whole guard, including recursively
checked dependent values. Only this family is excluded from unfolding. -/
theorem proofErase_future_union_compared_closed_carrier
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hD : ∀ levels rhs, ¬ D.unfolds family levels rhs)
    (hi : env.projections family info)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ (.const family []) (.sort u))
    (hU : env.HasType univs Γ U (.sort v))
    (HC : BetaStableFamily (fun Δ => JointCompare (ErasedJointUnion D) Δ mode)
      (proofEraseCtx Γ) (.const family []) (proofErase Γ U))
    (HG : BetaStableCarrier (ErasedJointUnion D) (proofEraseCtx Γ) (.const family []) a b) :
    BetaStableCarrier (ErasedJointUnion D) (proofEraseCtx Γ) (proofErase Γ U) a b := by
  apply proofErase_future_compared_closed_carrier (erased_joint_union_descent heq hs) ?_ hΓ hA hU HC HG
  intro Δ ls args out H
  exact erased_joint_union_no_rigid heq (henv.projectionRigid hi) hD H (constHead_mkApps _ _)

end Lean4Lean.VEnv.Strengthening
