import Lean4Lean.Theory.Typing.Strengthening.ProofErasureFutureClosedCarrier
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureFutureCarrierPrefixes

/-! # Reading arbitrary guards at an equal closed rigid carrier

The target is already exposed. Actual type equality identifies any record
carrier occurring in the guard with that exact nullary constant, and separates
it from a function carrier. Source carrier computations can therefore be
replayed and discarded without a general comparison-transport law.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private erase_forallE_inv
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
variable [Params]

private theorem rigid_spine_eq_closed
    (hΓ : OnCtx Γ (env.IsType univs)) (htarget : env.Rigid family)
    (hsource : env.Rigid source)
    (hA : env.HasType univs Γ A (.sort u))
    (HE : env.IsDefEqU univs Γ A (.const family []))
    (EA : proofErase Γ A = ProofShape.mkApps (.const source ls) ps) :
    ProofShape.mkApps (.const source ls) ps = .const family [] := by
  obtain ⟨args, rfl, Eargs⟩ := proofErase_const_spine_inv EA
  obtain ⟨rfl, HL, HA⟩ := henv.headInversion.rigid_rigid (args' := []) hΓ hsource htarget
    (HE.typeChain henv hΓ hA)
  cases HL
  cases HA
  simp only [List.map_nil] at Eargs
  subst ps
  rfl

private theorem carrier_closed_raw
    (hstep : ErasedScopedPrimitiveDescent Step)
    (htarget : env.Rigid family)
    (H : JointCheck Step Δ kind a b)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u))
    (HE : env.IsDefEqU univs Γ A (.const family []))
    (EΓ : proofEraseCtx Γ = Δ)
    (E : JointCheckKind.carrier (proofErase Γ A) = kind) :
    JointCarrierGuard Step Δ (.const family []) a b := by
  induction H generalizing Γ A u with
  | carrierChecked HC => exact .carrierChecked HC
  | carrierFunction =>
    obtain ⟨D, C, rfl, _, _, _⟩ := erase_forallE_inv (JointCheckKind.carrier.inj E)
    exact (henv.headInversion.forallE_rigid (args := []) hΓ htarget
      (HE.typeChain henv hΓ hA)).elim
  | carrierSubsingleton HS =>
    cases HS with
    | unit hi hz hf hp =>
      have EC := rigid_spine_eq_closed hΓ htarget (henv.projectionRigid hi) hA HE
        (JointCheckKind.carrier.inj E)
      rw [← EC]
      exact .carrierSubsingleton (.unit hi hz hf hp)
    | forallE HS =>
      obtain ⟨D, C, rfl, _, _, _⟩ := erase_forallE_inv (JointCheckKind.carrier.inj E)
      exact (henv.headInversion.forallE_rigid (args := []) hΓ htarget
        (HE.typeChain henv hΓ hA)).elim
  | carrierSymm HC ih => exact .carrierSymm (ih hΓ hA HE EΓ E)
  | carrierReduce RA RB HC ih => exact .carrierReduce RA RB (ih hΓ hA HE EΓ E)
  | carrierCompute R HC ih =>
    obtain ⟨A', HA, EA⟩ := proofErase_scoped_compute_realize hstep hΓ hA EΓ
      (JointCheckKind.carrier.inj E) R
    exact ih hΓ HA.hasType.2 (HA.symm.toU.trans henv hΓ HE) EΓ (congrArg JointCheckKind.carrier EA)
  | carrierIntro hi hz hp hadm HF =>
    have EC := rigid_spine_eq_closed hΓ htarget (henv.projectionRigid hi) hA HE
      (JointCheckKind.carrier.inj E)
    rw [← EC]
    exact .carrierIntro hi hz hp hadm HF
  | carrierNested hi hz hp hadm HT HF =>
    have EC := rigid_spine_eq_closed hΓ htarget (henv.projectionRigid hi) hA HE
      (JointCheckKind.carrier.inj E)
    rw [← EC]
    exact .carrierNested hi hz hp hadm HT HF
  | leaf | app | appCarrier | proj | lam | forallE | lamSorted | forallSorted | lamCommon |
      etaBodyL | etaBodyR | structFields | etaLams | compute | symm => cases E

/-- Actual type equality to a closed rigid constant transports an arbitrary
joint carrier guard to that constant. Source carrier computation prefixes are
replayed using soundness, with no type comparison or global exposure premise.
The endpoints may remain raw because only carrier computations are replayed. -/
theorem proofErase_joint_carrier_to_closed_rigid
    (hstep : ErasedScopedPrimitiveDescent Step)
    (htarget : env.Rigid family)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u))
    (HE : env.IsDefEqU univs Γ A (.const family []))
    (H : JointCarrierGuard Step (proofEraseCtx Γ) (proofErase Γ A) a b) :
    JointCarrierGuard Step (proofEraseCtx Γ) (.const family []) a b :=
  carrier_closed_raw hstep htarget H hΓ hA HE rfl rfl

/-- The same readout preserves a full future certificate. Actual equality
substitutes into every realized future context, and the target constant has
no nontrivial beta carrier path. No endpoint typings or future type-comparison
certificate are needed in this direction. -/
theorem proofErase_future_carrier_to_closed_rigid
    (hstep : ErasedScopedPrimitiveDescent Step)
    (htarget : env.Rigid family)
    (hΓ : OnCtx Γ (env.IsType univs))
    (HE : env.IsDefEq univs Γ A (.const family []) (.sort u))
    (H : BetaStableCarrier Step (proofEraseCtx Γ) (proofErase Γ A) a b) :
    BetaStableCarrier Step (proofEraseCtx Γ) (.const family []) a b := by
  have fixed {C : ProofShape} (R : ProofShape.BetaRed (.const family []) C) :
      C = .const family [] := by
    have RR : ProofShape.BetaRed (ProofShape.mkApps (.const family []) []) C := R
    obtain ⟨ps', rfl, HP⟩ := RR.const_spine
    cases HP
    rfl
  constructor
  · intro C p q RC RP RQ
    cases fixed RC
    exact proofErase_joint_carrier_to_closed_rigid hstep htarget hΓ HE.hasType.1 HE.toU
      (H.1 .refl RP RQ)
  · intro Δ' τ C p q W RC RP RQ
    change ProofShape.BetaRed (.const family []) C at RC
    cases fixed RC
    have HG := H.2 W .refl RP RQ
    obtain ⟨Γ₀, σ, hΓ₀, EΓ₀, WS, ES⟩ := W hΓ rfl
    rw [← proofErase_subst_with hΓ₀ WS HE.hasType.1 ES, ← EΓ₀] at HG
    rw [← EΓ₀]
    have HE' := HE.subst henv WS
    exact proofErase_joint_carrier_to_closed_rigid hstep htarget hΓ₀ HE'.hasType.1 HE'.toU HG

private theorem closed_carrier_compute_eq
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (R : ScopedCompute Step (proofEraseCtx Γ) (proofErase Γ A) (.const family [])) :
    env.IsDefEq univs Γ A (.const family []) (.sort u) := by
  obtain ⟨F, HA, EF⟩ := proofErase_scoped_compute_realize hstep hΓ hA rfl rfl R
  obtain ⟨args, rfl, Eargs⟩ := proofErase_const_spine_inv
    (show proofErase Γ F = ProofShape.mkApps (.const family []) [] from EF)
  have hargs : args = [] := by
    have HH := congrArg List.length Eargs
    simpa using HH.symm
  subst args
  exact HA

/-- Forward carrier computation is valid when its target is a closed rigid
constant. The computation may use arbitrary sound scoped primitives and the
source guard may contain independent carrier-computation prefixes. -/
theorem proofErase_joint_carrier_compute_closed
    (hstep : ErasedScopedPrimitiveDescent Step) (htarget : env.Rigid family)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (R : ScopedCompute Step (proofEraseCtx Γ) (proofErase Γ A) (.const family []))
    (H : JointCarrierGuard Step (proofEraseCtx Γ) (proofErase Γ A) a b) :
    JointCarrierGuard Step (proofEraseCtx Γ) (.const family []) a b :=
  proofErase_joint_carrier_to_closed_rigid hstep htarget hΓ hA
    (closed_carrier_compute_eq hstep hΓ hA R).toU H

/-- Full future guards move forward along the same arbitrary computation to
a closed rigid constant. Sound replay supplies substitutable actual equality,
so neither primitive substitution nor a beta-commutation law is required. -/
theorem proofErase_future_carrier_compute_closed
    (hstep : ErasedScopedPrimitiveDescent Step) (htarget : env.Rigid family)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (R : ScopedCompute Step (proofEraseCtx Γ) (proofErase Γ A) (.const family []))
    (H : BetaStableCarrier Step (proofEraseCtx Γ) (proofErase Γ A) a b) :
    BetaStableCarrier Step (proofEraseCtx Γ) (.const family []) a b :=
  proofErase_future_carrier_to_closed_rigid hstep htarget hΓ
    (closed_carrier_compute_eq hstep hΓ hA R) H

/-- A future type comparison with a closed rigid constant yields equivalence
of all full future guards at the two carriers. The readout direction uses
actual equality only; the reverse direction uses the supplied comparison. -/
theorem proofErase_future_compared_closed_carrier_iff
    (hstep : ErasedScopedPrimitiveDescent Step) (htarget : env.Rigid family)
    (hn : ∀ {Δ ls args out}, ¬ Step Δ (ProofShape.mkApps (.const family ls) args) out)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hC : env.HasType univs Γ (.const family []) (.sort u))
    (hA : env.HasType univs Γ A (.sort v))
    (HC : BetaStableFamily (fun Δ => JointCompare Step Δ mode)
      (proofEraseCtx Γ) (.const family []) (proofErase Γ A)) :
    BetaStableCarrier Step (proofEraseCtx Γ) (proofErase Γ A) a b ↔
      BetaStableCarrier Step (proofEraseCtx Γ) (.const family []) a b := by
  constructor
  · exact proofErase_future_carrier_compute_closed hstep htarget hΓ hA
      (proofErase_compared_closed_carrier_compute hstep hn hΓ hC hA HC.base)
  · exact proofErase_future_compared_closed_carrier hstep hn hΓ hC hA HC

/-- An ordinary certified type comparison already gives the full future-guard
equivalence in the union. Its exact exposure path is certified, so backward
transport retains all future paths; forward transport needs only soundness.
The type comparison itself need not carry a full future certificate. -/
theorem proofErase_certified_closed_carrier_iff
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hD : ∀ levels rhs, ¬ D.unfolds family levels rhs)
    (hi : env.projections family info)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hC : env.HasType univs Γ (.const family []) (.sort u))
    (hA : env.HasType univs Γ A (.sort v))
    (HC : JointCompare (ErasedBetaStableJoint D) (proofEraseCtx Γ) mode
      (.const family []) (proofErase Γ A)) :
    BetaStableCarrier (ErasedJointUnion D) (proofEraseCtx Γ) (proofErase Γ A) a b ↔
      BetaStableCarrier (ErasedJointUnion D) (proofEraseCtx Γ) (.const family []) a b := by
  have hn {Δ ls args out} : ¬ ErasedBetaStableJoint D Δ
      (ProofShape.mkApps (.const family ls) args) out := fun H =>
    erased_joint_union_no_rigid heq (henv.projectionRigid hi) hD
      (erased_beta_stable_joint_into_union H) (constHead_mkApps _ _)
  have R := proofErase_compared_closed_carrier_compute
    (erased_beta_stable_joint_descent heq hs) hn hΓ hC hA HC
  constructor
  · exact proofErase_future_carrier_compute_closed (erased_joint_union_descent heq hs)
      (henv.projectionRigid hi) hΓ hA (R.mono erased_beta_stable_joint_into_union)
  · intro H
    exact H.certified_carrier_prefix heq hs hΓ hA R

end Lean4Lean.VEnv.Strengthening
