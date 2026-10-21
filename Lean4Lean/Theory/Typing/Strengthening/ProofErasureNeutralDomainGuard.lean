import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointNeutralContext
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqNativeCarrierRecovery
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureComparedSubsingleton
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJoinedNativeGuard

/-! # All function guards through convertible neutral input domains

Neutral context transport handles the function rule. Typed Pi computation
inversion retains its codomain path in the original binder context, allowing
that path to be replayed under the target domain. Consequently arbitrary
intermediate carrier computations are included, not just a displayed rule.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private subsingleton_pi
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureComparedSubsingleton
open private domain_sort_raw
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointTransport
open private native_walk_typing
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJoinedNativeGuard
variable [Params]

/-- Every joint function guard transports from A to convertible B when both
input types erase to neutral spines. The codomain is arbitrary raw syntax.
Carrier computation, endpoint reduction, nested fields, and repeated function
checking are all retained. Only the input types need original typing evidence. -/
theorem ProofShape.JointCarrierGuard.neutral_domain
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (hsubst : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextSubstitution Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (hΓ : OnCtx Γ (env.IsType univs))
    (HAB : env.IsDefEq univs Γ A B (.sort u))
    (EA : proofErase Γ A = ProofShape.mkApps (.bvar i) args)
    (EB : proofErase Γ B = ProofShape.mkApps (.bvar j) args')
    (H : JointCarrierGuard Step (proofEraseCtx Γ) (.forallE (proofErase Γ A) body) a b) :
    JointCarrierGuard Step (proofEraseCtx Γ) (.forallE (proofErase Γ B) body) a b := by
  change JointCheck Step (proofEraseCtx Γ) (.carrier (.forallE (proofErase Γ A) body)) a b at H
  generalize EΓ : proofEraseCtx Γ = Δ at H ⊢
  generalize E : JointCheckKind.carrier (.forallE (proofErase Γ A) body) = kind at H
  induction H generalizing A body args with
  | carrierChecked H => exact .carrierChecked H
  | carrierFunction S H ih =>
    cases EΓ
    obtain ⟨ED, rfl⟩ := ProofShape.forallE.inj (JointCheckKind.carrier.inj E)
    rw [← ED] at S H
    have hA := domain_sort_raw S hΓ HAB.hasType.1 rfl rfl
    have hB := (HAB.toU.of_l henv hΓ hA).hasType.2
    exact .carrierFunction ⟨Γ, B, hΓ, rfl, hB, rfl⟩
      (proofErase_joint_neutral_context hhead hsubst hΓ HAB EA EB H)
  | carrierSubsingleton HS =>
    cases E
    exact .carrierSubsingleton (.forallE (subsingleton_pi HS))
  | carrierSymm H ih => exact .carrierSymm (ih HAB EA EΓ E)
  | carrierReduce RA RB H ih => exact .carrierReduce RA RB (ih HAB EA EΓ E)
  | carrierCompute R H ih =>
    cases EΓ
    cases E
    obtain ⟨Araw, body', Eout, RA, RC⟩ := R.forallE_inv_typed hstep hsubst hhead hΓ HAB.hasType.1 rfl
    obtain ⟨A', HA, EAprime⟩ := proofErase_scoped_compute_realize hstep hΓ HAB.hasType.1 rfl rfl RA
    have HA' := HA.symm.trans HAB
    have Rneutral := RA
    rw [EA] at Rneutral
    obtain ⟨newArgs, Eneutral, _⟩ := Rneutral.bvar_spine hhead
    have EA' := EAprime.trans Eneutral
    have RC : ScopedCompute Step (proofEraseCtx (A :: Γ)) body body' := RC
    have RC' := RC.defeqCtx hsubst hΓ (.succ .zero HAB)
    apply JointCheck.carrierCompute (ScopedCompute.forallE .refl RC')
    exact ih HA' EA' rfl (by rw [EAprime, ← Eout])
  | carrierIntro | carrierNested =>
    have HE := congrArg ProofShape.constHead (JointCheckKind.carrier.inj E)
    simp only [ProofShape.constHead, constHead_mkApps] at HE
    cases HE
  | leaf | app | appCarrier | proj | lam | forallE | lamSorted | forallSorted | lamCommon |
      etaBodyL | etaBodyR | structFields | etaLams | compute | symm => cases E

/-- The raw neutral-input transport applies to actual dependent Pi carriers.
Context conversion supplies the target codomain typing and exactly relates
its erasure. No recovered-domain comparison or join is an additional premise. -/
theorem proofErase_joint_neutral_domain_guard
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (hsubst : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextSubstitution Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (hΓ : OnCtx Γ (env.IsType univs))
    (HAB : env.IsDefEq univs Γ A B (.sort u))
    (hC : env.HasType univs (A :: Γ) C (.sort v))
    (EA : proofErase Γ A = ProofShape.mkApps (.bvar i) args)
    (EB : proofErase Γ B = ProofShape.mkApps (.bvar j) args')
    (H : JointCarrierGuard Step (proofEraseCtx Γ) (proofErase Γ (.forallE A C)) a b) :
    JointCarrierGuard Step (proofEraseCtx Γ) (proofErase Γ (.forallE B C)) a b := by
  have hctx := IsDefEqCtx.succ .zero HAB
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, HAB.hasType.1⟩
  have hPi := HasType.forallE HAB.hasType.1 hC
  have hPi' := HasType.forallE HAB.hasType.2 (hC.defeqDFC henv hctx)
  rw [show proofErase Γ (.forallE A C) = .forallE _ _ from
    if_neg (not_isProof_of_sort hΓ hPi)] at H
  rw [show proofErase Γ (.forallE B C) = .forallE _ _ from
    if_neg (not_isProof_of_sort hΓ hPi')]
  have H' := H.neutral_domain hstep hhead hsubst hΓ HAB EA EB
  rwa [proofErase_defeqCtx hΓA hctx hC] at H'

/-- Certified guards tolerate convertible neutral input-domain changes,
including arbitrary certified carrier computations. This is unconditional
on proposition beta transport and stays within the certified relation. -/
theorem proofErase_certified_neutral_domain_guard
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (HAB : env.IsDefEq univs Γ A B (.sort u))
    (hC : env.HasType univs (A :: Γ) C (.sort v))
    (EA : proofErase Γ A = ProofShape.mkApps (.bvar i) args)
    (EB : proofErase Γ B = ProofShape.mkApps (.bvar j) args')
    (H : JointCarrierGuard (ErasedBetaStableJoint D) (proofEraseCtx Γ)
      (proofErase Γ (.forallE A C)) a b) :
    JointCarrierGuard (ErasedBetaStableJoint D) (proofEraseCtx Γ)
      (proofErase Γ (.forallE B C)) a b :=
  proofErase_joint_neutral_domain_guard (erased_beta_stable_joint_descent heq hs)
    erased_beta_stable_joint_head (erased_beta_stable_joint_subst heq hs) hΓ HAB hC EA EB H

/-- A literal native declaration prefix consumes a function guard after its
input domain changes from neutral A to convertible neutral B. The prefix's
recovery, target argument typings, and actual proposition comparison are all
constructed. There is no parameter join or compared-recovery premise. -/
theorem proofErase_native_neutral_domain_propositions
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (hsubst : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextSubstitution Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (hΓ : OnCtx Γ (env.IsType univs))
    (hc : env.constants c = some ci) (hw : ∀ l ∈ ls, l.WF univs)
    (hl : ls.length = ci.uvars)
    (HW : InstForallsC env univs Γ (ci.type.instL ls) params
      (.forallE (.forallE B C) (.sort .zero)))
    (HAB : env.IsDefEq univs Γ A B (.sort u))
    (hC : env.HasType univs (A :: Γ) C (.sort v))
    (EA : proofErase Γ A = ProofShape.mkApps (.bvar i) args)
    (EB : proofErase Γ B = ProofShape.mkApps (.bvar j) args')
    (hx : env.HasType univs Γ x (.forallE A C))
    (hy : env.HasType univs Γ y (.forallE A C))
    (H : JointCarrierGuard Step (proofEraseCtx Γ)
      (proofErase Γ (.forallE A C)) (proofErase Γ x) (proofErase Γ y)) :
    let f := VExpr.mkApps (.const c ls) params
    env.HasType univs Γ (.app f x) (.sort .zero) ∧
      env.HasType univs Γ (.app f y) (.sort .zero) ∧
      JointCompare Step (proofEraseCtx Γ) mode
        (proofErase Γ (.app f x)) (proofErase Γ (.app f y)) := by
  have hf := native_walk_typing (HasType.const hc hw hl) HW
  have hn := not_isProof_function_to_sort hΓ hf
  have RF := proofErase_const_native_recovery (Step := Step) hΓ hc hw hl HW hn
  obtain ⟨_, hPi⟩ := hf.isType henv hΓ
  rw [show proofErase Γ (.forallE (.forallE B C) (.sort .zero)) = .forallE _ _ from
    if_neg (not_isProof_of_sort hΓ hPi)] at RF
  have HG := proofErase_joint_neutral_domain_guard hstep hhead hsubst hΓ HAB hC EA EB H
  have HE := IsDefEq.forallEDF HAB hC
  have hL := hf.app (HE.defeq hx)
  have hR := hf.app (HE.defeq hy)
  refine ⟨hL, hR, ?_⟩
  rw [show proofErase Γ (.app (VExpr.mkApps (.const c ls) params) x) = .app _ _ from
      if_neg (not_isProof_of_sort hΓ hL),
    show proofErase Γ (.app (VExpr.mkApps (.const c ls) params) y) = .app _ _ from
      if_neg (not_isProof_of_sort hΓ hR)]
  exact .appCarrier RF (.leaf .refl) HG

end Lean4Lean.VEnv.Strengthening
