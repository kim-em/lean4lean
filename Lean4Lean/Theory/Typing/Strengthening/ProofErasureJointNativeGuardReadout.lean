import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointNativeTelescope

/-! # Reading native argument guards through union computation

The original recoverable native walk controls selected domains after arbitrary
argument computation. Native guard readout therefore needs no unrestricted
union substitution or recovery of the computed arguments.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private const_app_compute
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureNativeSpineReadout
variable [Params]

/-- Recovering a computed constant prefix cannot escape the original native
Pi domain. The constant head must remain inert, and the original walk retains argument
recoveries. Computed arguments need no exact recovery. -/
theorem proofErase_joint_union_computed_const_domain
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hn : ∀ {Δ ls args out}, ¬ ErasedJointUnion D Δ (ProofShape.mkApps (.const c ls) args) out)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hc : env.constants c = some ci) (hw : ∀ l ∈ ls, l.WF univs)
    (hl : ls.length = ci.uvars)
    (HW : RecoverableNativeWalk D Γ (ci.type.instL ls) args (.forallE A B))
    (hPi : env.HasType univs Γ (.forallE A B) (.sort u))
    (RP : ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ)
      (ProofShape.mkApps (.const c ls) (args.map (proofErase Γ))) f)
    (R : ScopedTypeRecovery (ErasedJointUnion D) (proofEraseCtx Γ) f (.forallE domain body)) :
    ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ) (proofErase Γ A) domain := by
  obtain ⟨args', rfl, HA⟩ := RP.const_spine hn
  have H := proofErase_joint_union_computed_const_native heq hs hΓ hc hw hl HW HA R
  rw [show proofErase Γ (.forallE A B) = .forallE (proofErase Γ A) (proofErase (A :: Γ) B) from
    if_neg (not_isProof_of_sort hΓ hPi)] at H
  obtain ⟨_, _, HE, HD⟩ := H.forallE_domain_inv erased_joint_union_head
  cases HE
  exact HD


private theorem native_argument_readout
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hn : ∀ {Δ ls args out}, ¬ ErasedJointUnion D Δ (ProofShape.mkApps (.const c ls) args) out)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hc : env.constants c = some ci) (hw : ∀ l ∈ ls, l.WF univs)
    (hl : ls.length = ci.uvars)
    (HW : RecoverableNativeWalk D Γ (ci.type.instL ls) args (.forallE A B))
    (hPi : env.HasType univs Γ (.forallE A B) (.sort u))
    (H : JointCheck (ErasedJointUnion D) Δ kind sa sb) (hm : kind = .compare false)
    (EΔ : proofEraseCtx Γ = Δ)
    (Ea : sa = .app (ProofShape.mkApps (.const c ls) as) x)
    (Eb : sb = .app (ProofShape.mkApps (.const c ls) bs) y)
    (RA : ScopedCompute (ErasedJointUnion D) Δ (ProofShape.mkApps (.const c ls) (args.map (proofErase Γ)))
      (ProofShape.mkApps (.const c ls) as))
    (RB : ScopedCompute (ErasedJointUnion D) Δ (ProofShape.mkApps (.const c ls) (args.map (proofErase Γ)))
      (ProofShape.mkApps (.const c ls) bs)) :
    JointCarrierGuard (ErasedJointUnion D) Δ (proofErase Γ A) x y := by
  induction H generalizing as x bs y with
  | leaf H =>
    cases hm
    cases H with
    | refl =>
      have E := (ProofShape.app.inj (Ea.symm.trans Eb)).2
      exact E ▸ JointCheck.carrierChecked (JointCheck.leaf ScopedLeaf.refl)
    | sort | const => cases Ea
  | app HF HX => cases Ea; cases Eb; exact .carrierChecked HX
  | appCarrier R HF HX =>
    cases Ea
    cases Eb
    rw [← EΔ] at RA R HX ⊢
    exact .carrierCompute
      (proofErase_joint_union_computed_const_domain heq hs hn hΓ hc hw hl HW hPi RA R) HX
  | compute Ra Rb HC ih =>
    obtain ⟨as', x', EA, RA', RX⟩ := const_app_compute hn (Ea ▸ Ra)
    obtain ⟨bs', y', EB, RB', RY⟩ := const_app_compute hn (Eb ▸ Rb)
    exact .carrierReduce RX RY (ih hm EΔ EA EB (RA.trans RA') (RB.trans RB'))
  | symm H ih => exact .carrierSymm (ih hm EΔ Eb Ea RB RA)
  | proj | lam | forallE | lamSorted | forallSorted | etaLams => cases Ea
  | lamCommon | etaBodyL | etaBodyR | structFields |
      carrierIntro | carrierChecked | carrierSubsingleton | carrierFunction |
      carrierSymm | carrierCompute | carrierReduce | carrierNested => cases hm

/-- Comparison after independently computing a shared declaration prefix yields
the final argument guard at that prefix's original native domain. The final raw
arguments x and y need no typing or recovery certificate; the original prefix
requires recoveries along its original typed telescope walk. No primitive
substitution closure is assumed. -/
theorem proofErase_joint_union_computed_native_argument_guard
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hn : ∀ {Δ ls args out}, ¬ ErasedJointUnion D Δ (ProofShape.mkApps (.const c ls) args) out)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hc : env.constants c = some ci) (hw : ∀ l ∈ ls, l.WF univs)
    (hl : ls.length = ci.uvars)
    (HW : RecoverableNativeWalk D Γ (ci.type.instL ls) args (.forallE A B))
    (hPi : env.HasType univs Γ (.forallE A B) (.sort u))
    (RA : ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ)
      (ProofShape.mkApps (.const c ls) (args.map (proofErase Γ))) f)
    (RB : ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ)
      (ProofShape.mkApps (.const c ls) (args.map (proofErase Γ))) g)
    (H : JointCompare (ErasedJointUnion D) (proofEraseCtx Γ) false (.app f x) (.app g y)) :
    JointCarrierGuard (ErasedJointUnion D) (proofEraseCtx Γ) (proofErase Γ A) x y := by
  obtain ⟨as, rfl, _⟩ := RA.const_spine hn
  obtain ⟨bs, rfl, _⟩ := RB.const_spine hn
  exact native_argument_readout heq hs hn hΓ hc hw hl HW hPi H rfl rfl rfl rfl RA RB


end Lean4Lean.VEnv.Strengthening
