import Lean4Lean.Theory.Typing.Strengthening.ProofErasureComputedJointDescent
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedPiExposure

/-! # Carrier checking at sort-typed endpoints

A carrier inhabited by a sort-typed endpoint cannot use structure or function
eta to bypass ordinary comparison. Compatible computation preserves this
fact, even when the carrier's literal shape changes. Only one endpoint needs
the supplied carrier typing; both retain their independent sort typings.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private erase_forallE_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
variable [Params]

private theorem type_not_family_carrier
    (hΓ : OnCtx Γ (env.IsType univs)) (he : env.HasType univs Γ e (.sort u))
    (heC : env.HasType univs Γ e C) (hi : env.projections family info)
    (EC : proofErase Γ C = ProofShape.mkApps (.const family ls) ps) : False := by
  obtain ⟨args, rfl, _⟩ := proofErase_const_spine_inv EC
  exact HasType.sortTele_not_rigid (as := []) (doms := []) hΓ (henv.projectionRigid hi) he heC

private theorem type_not_pi_carrier
    (hΓ : OnCtx Γ (env.IsType univs)) (he : env.HasType univs Γ e (.sort u))
    (heC : env.HasType univs Γ e C) (EC : proofErase Γ C = .forallE A B) : False := by
  obtain ⟨_, _, rfl, _, _, _⟩ := erase_forallE_inv EC
  exact (he.uniqU henv hΓ heC).sort_forallE_inv henv hΓ

private theorem carrier_types_checked
    (hstep : ErasedScopedPrimitiveDescent Step)
    (H : ComputedJointCarrierGuard Step Δ rawC sa sb)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs Γ a (.sort u)) (hb : env.HasType univs Γ b (.sort v))
    (ht : env.HasType univs Γ a C ∨ env.HasType univs Γ b C)
    (EΓ : proofEraseCtx Γ = Δ) (Ea : proofErase Γ a = sa) (Eb : proofErase Γ b = sb)
    (EC : proofErase Γ C = rawC) :
    ComputedJointCompare Step Δ true sa sb := by
  change ComputedJointCheck Step Δ (.carrier rawC) sa sb at H
  generalize EK : JointCheckKind.carrier rawC = kind at H
  induction H generalizing Γ a b C u v rawC with
  | carrierChecked H => exact H
  | carrierIntro hi hx hp hadm H | carrierNested hi hx hp hadm HT H =>
    cases EK
    rcases ht with ht | ht
    · exact (type_not_family_carrier hΓ ha ht hi EC).elim
    · exact (type_not_family_carrier hΓ hb ht hi EC).elim
  | carrierSubsingleton H =>
    cases EK
    cases H with
    | unit hi hx hf hp =>
      rcases ht with ht | ht
      · exact (type_not_family_carrier hΓ ha ht hi EC).elim
      · exact (type_not_family_carrier hΓ hb ht hi EC).elim
    | forallE H =>
      rcases ht with ht | ht
      · exact (type_not_pi_carrier hΓ ha ht EC).elim
      · exact (type_not_pi_carrier hΓ hb ht EC).elim
  | carrierFunction S H ih =>
    cases EK
    rcases ht with ht | ht
    · exact (type_not_pi_carrier hΓ ha ht EC).elim
    · exact (type_not_pi_carrier hΓ hb ht EC).elim
  | carrierSymm H ih => exact .symm (ih hΓ hb ha ht.symm EΓ Eb Ea EC EK)
  | carrierCompute RC H ih =>
    cases EK
    have hCt : env.IsType univs Γ C := ht.elim (fun h => h.isType henv hΓ) (fun h => h.isType henv hΓ)
    obtain ⟨_, hC⟩ := hCt
    obtain ⟨C', HC, EC'⟩ := proofErase_scoped_compute_realize hstep hΓ hC EΓ EC RC
    have ht' : env.HasType univs Γ a C' ∨ env.HasType univs Γ b C' :=
      ht.imp (fun h => HC.defeq h) (fun h => HC.defeq h)
    exact ih hΓ ha hb ht' EΓ Ea Eb EC' rfl
  | carrierReduce RA RB H ih =>
    cases EK
    obtain ⟨a', HA, EA⟩ := proofErase_scoped_compute_realize hstep hΓ ha EΓ Ea RA
    obtain ⟨b', HB, EB⟩ := proofErase_scoped_compute_realize hstep hΓ hb EΓ Eb RB
    have ht' : env.HasType univs Γ a' C ∨ env.HasType univs Γ b' C :=
      ht.imp (fun h => (IsDefEqU.of_l henv hΓ ⟨_, HA⟩ h).hasType.2)
        (fun h => (IsDefEqU.of_l henv hΓ ⟨_, HB⟩ h).hasType.2)
    exact .compute RA RB (ih hΓ HA.hasType.2 HB.hasType.2 ht' EΓ EA EB EC rfl)
  | leaf | app | appCarrier | appComputed | proj | lam | forallE | lamSorted | forallSorted |
      lamCommon | etaBodyL | etaBodyR | structFields | etaLams | compute | symm => cases EK

/-- At two independently sort-typed endpoints, a computed carrier guard is an
ordinary common comparison whenever either endpoint has that actual carrier.
The primitive relation and every raw endpoint are retained exactly. -/
theorem proofErase_computed_carrier_types_checked
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs Γ a (.sort u)) (hb : env.HasType univs Γ b (.sort v))
    (ht : env.HasType univs Γ a C ∨ env.HasType univs Γ b C)
    (H : ComputedJointCarrierGuard Step (proofEraseCtx Γ) (proofErase Γ C)
      (proofErase Γ a) (proofErase Γ b)) :
    ComputedJointCompare Step (proofEraseCtx Γ) true (proofErase Γ a) (proofErase Γ b) :=
  carrier_types_checked hstep H hΓ ha hb ht rfl rfl rfl rfl

end Lean4Lean.VEnv.Strengthening
