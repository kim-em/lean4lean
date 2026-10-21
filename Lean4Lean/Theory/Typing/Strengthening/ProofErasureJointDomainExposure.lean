import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointLoopReadout
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierDomainJoin

/-! # Retaining domain comparison during recovered Pi exposure

Pi exposure can retain common comparison between the displayed domain and the
newly selected domain. Typed recovery replay upgrades this to inferred domain
comparison, allowing existing carrier alignment results to consume it. Neither
existence of the starting recovery nor comparison completeness is asserted.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
namespace ProofShape
open private beta_forallE_parts
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierDomainJoin

/-- Computation from a Pi retains a computation of its domain in the original
ambient context. No transport of the changing codomain context is needed. -/
theorem ScopedCompute.forallE_domain_inv
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (R : ScopedCompute Step Δ (.forallE A B) out) :
    ∃ A' B', out = .forallE A' B' ∧ ScopedCompute Step Δ A A' := by
  generalize E : ProofShape.forallE A B = source at R
  induction R generalizing A B with
  | base H => exact (E ▸ hhead H).elim
  | beta H =>
    obtain ⟨A', B', HE, HA, _⟩ := beta_forallE_parts (E ▸ H)
    exact ⟨A', B', HE, .beta HA⟩
  | trans _ _ ih₁ ih₂ =>
    obtain ⟨A₁, B₁, rfl, HA⟩ := ih₁ E
    obtain ⟨A₂, B₂, HE, HA'⟩ := ih₂ rfl
    exact ⟨A₂, B₂, HE, HA.trans HA'⟩
  | forallE HA HB => cases E; exact ⟨_, _, rfl, HA⟩
  | app | proj | lam => cases E

variable [Params]

private theorem domain_exposure_pair
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (H : JointCheck Step Δ kind a b) (hm : kind = .compare false) :
    (∀ A B, a = .forallE A B → ∃ A' B',
      ScopedCompute Step Δ b (.forallE A' B') ∧ JointCompare Step Δ true A A') ∧
    (∀ A B, b = .forallE A B → ∃ A' B',
      ScopedCompute Step Δ a (.forallE A' B') ∧ JointCompare Step Δ true A A') := by
  induction H with
  | leaf H =>
    cases hm
    cases H with
    | refl => constructor <;> intro A B E <;> exact ⟨A, B, E ▸ .refl, .leaf .refl⟩
    | sort | const => constructor <;> intro A B E <;> cases E
  | forallE HA HB =>
    constructor
    · intro A B E; cases E; exact ⟨_, _, .refl, JointCompare.common HA⟩
    · intro A B E; cases E; exact ⟨_, _, .refl, .symm (JointCompare.common HA)⟩
  | forallSorted _ _ HA _ _ HB =>
    constructor
    · intro A B E; cases E; exact ⟨_, _, .refl, HA⟩
    · intro A B E; cases E; exact ⟨_, _, .refl, .symm HA⟩
  | compute Ra Rb HC ih =>
    constructor
    · intro A B E
      obtain ⟨A₁, B₁, HE, HA⟩ := (E ▸ Ra).forallE_domain_inv hhead
      obtain ⟨A₂, B₂, R, HD⟩ := (ih hm).1 A₁ B₁ HE
      exact ⟨A₂, B₂, Rb.trans R, .compute HA .refl HD⟩
    · intro A B E
      obtain ⟨A₁, B₁, HE, HA⟩ := (E ▸ Rb).forallE_domain_inv hhead
      obtain ⟨A₂, B₂, R, HD⟩ := (ih hm).2 A₁ B₁ HE
      exact ⟨A₂, B₂, Ra.trans R, .compute HA .refl HD⟩
  | symm H ih => exact (ih hm).symm
  | app | appCarrier | proj | lam | lamSorted | etaLams =>
    constructor <;> intro A B E <;> cases E
  | lamCommon | etaBodyL | etaBodyR | structFields |
      carrierIntro | carrierChecked | carrierSubsingleton | carrierFunction |
      carrierSymm | carrierCompute | carrierReduce | carrierNested => cases hm

/-- Inferred comparison against a Pi exposes a target Pi and keeps common
comparison of its domain with the source domain, at the same stage. -/
theorem JointCompare.forallE_domain_exposure
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (H : JointCompare Step Δ false (.forallE A B) T) :
    ∃ A' B', ScopedCompute Step Δ T (.forallE A' B') ∧
      JointCompare Step Δ true A A' :=
  (domain_exposure_pair hhead H rfl).1 A B rfl

/-- A recovery compared with an assigned Pi can select a new Pi while retaining
comparison from the assigned domain to the newly recovered domain. -/
theorem ScopedTypeRecovery.pi_domain_of_joint_compare
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (R : ScopedTypeRecovery Step Δ e T)
    (H : JointCompare Step Δ false T (.forallE A B)) :
    ∃ A' B', ScopedTypeRecovery Step Δ e (.forallE A' B') ∧
      JointCompare Step Δ true A A' := by
  obtain ⟨A', B', RT, HD⟩ := JointCompare.forallE_domain_exposure hhead (.symm H)
  exact ⟨A', B', R.convert RT, HD⟩

end ProofShape

open ProofShape
variable [Params]

/-- For an actually typed function, comparison of a selected recovered type
with its assigned Pi exposes another actual Pi typing. The assigned and newly
selected domains compare in inferred mode, even if the supplied type comparison
uses common mode. This consumes existing recovery and comparison certificates. -/
theorem proofErase_joint_recovered_pi_domain
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (.forallE A B))
    (R : ScopedTypeRecovery Step (proofEraseCtx Γ) (proofErase Γ f) T)
    (H : JointCompare Step (proofEraseCtx Γ) mode T (proofErase Γ (.forallE A B))) :
    ∃ D C, env.HasType univs Γ f (.forallE D C) ∧
      ScopedTypeRecovery Step (proofEraseCtx Γ) (proofErase Γ f)
        (.forallE (proofErase Γ D) (proofErase (D :: Γ) C)) ∧
      JointCompare Step (proofEraseCtx Γ) false (proofErase Γ A) (proofErase Γ D) := by
  obtain ⟨F, hfF, EF⟩ := proofErase_scoped_typeRecovery_replay hstep hΓ hf R
  obtain ⟨u, hF⟩ := hfF.isType henv hΓ
  obtain ⟨v, hPi⟩ := hf.isType henv hΓ
  have H' := proofErase_joint_types_inferred hstep hΓ hF hPi (EF ▸ H)
  have EPi : proofErase Γ (.forallE A B) =
      .forallE (proofErase Γ A) (proofErase (A :: Γ) B) :=
    if_neg (not_isProof_of_sort hΓ hPi)
  rw [EF, EPi] at H'
  obtain ⟨D', C', R', HD⟩ := R.pi_domain_of_joint_compare hhead H'
  obtain ⟨D, C, hfDC, ED, EC⟩ := proofErase_scoped_recovered_pi_descend hstep hΓ hΓ
    (show Ctx.LiftN 0 0 Γ Γ from .zero []) hf
    (by simpa only [ProofShape.liftN_zero] using R')
  simp only [ProofShape.liftN_zero] at ED EC
  rw [← ED, ← EC] at R'
  rw [← ED] at HD
  obtain ⟨_, hDC⟩ := hfDC.isType henv hΓ
  obtain ⟨⟨_, hA⟩, _, _⟩ := hPi.forallE_inv henv
  obtain ⟨⟨_, hD⟩, _, _⟩ := hDC.forallE_inv henv
  exact ⟨D, C, hfDC, R', proofErase_joint_types_inferred hstep hΓ hA hD HD⟩

/-- If the assigned function domain is an empty registered structure, a
compared recovery supplies a new Pi recovery and its argument guard together.
The selected domain may have different syntax and need not join the old one. -/
theorem proofErase_joint_compared_recovery_unit_guard
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (hn : ∀ {Δ ls args out}, ¬ Step Δ (ProofShape.mkApps (.const family ls) args) out)
    (hi : env.projections family info) (hx : info.nindices = 0)
    (hf : info.numFields = 0) (hp : ps.length = info.nparams)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ f (.forallE A B))
    (R : ScopedTypeRecovery Step (proofEraseCtx Γ) (proofErase Γ f) T)
    (H : JointCompare Step (proofEraseCtx Γ) mode T (proofErase Γ (.forallE A B)))
    (EA : proofErase Γ A = ProofShape.mkApps (.const family ls) ps) :
    ∃ D C, ScopedTypeRecovery Step (proofEraseCtx Γ) (proofErase Γ f) (.forallE D C) ∧
      JointCarrierGuard Step (proofEraseCtx Γ) D x y := by
  obtain ⟨D, C, _, RD, HD⟩ := proofErase_joint_recovered_pi_domain hstep hhead hΓ ht R H
  rw [EA] at HD
  exact ⟨_, _, RD, HD.unit_carrier_target hn hi hx hf hp⟩

/-- The empty-domain compared-recovery case closes the actual joint application
rule, retaining the original function and argument endpoints and stage. The
function comparison, initial recovery and assigned-type comparison are supplied;
no global re-synthesis or comparison-completeness hypothesis is used. -/
theorem proofErase_joint_application_of_compared_recovery_unit
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (hn : ∀ {Δ ls args out}, ¬ Step Δ (ProofShape.mkApps (.const family ls) args) out)
    (hi : env.projections family info) (hx : info.nindices = 0)
    (hf : info.numFields = 0) (hp : ps.length = info.nparams)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ f (.forallE A B))
    (R : ScopedTypeRecovery Step (proofEraseCtx Γ) (proofErase Γ f) T)
    (H : JointCompare Step (proofEraseCtx Γ) mode T (proofErase Γ (.forallE A B)))
    (EA : proofErase Γ A = ProofShape.mkApps (.const family ls) ps)
    (HF : JointCompare Step (proofEraseCtx Γ) false (proofErase Γ f) g) :
    JointCompare Step (proofEraseCtx Γ) resultMode (.app (proofErase Γ f) x) (.app g y) := by
  obtain ⟨D, C, RD, HG⟩ := proofErase_joint_compared_recovery_unit_guard
    hstep hhead hn hi hx hf hp hΓ ht R H EA (x := x) (y := y)
  exact .appCarrier RD HF HG

end Lean4Lean.VEnv.Strengthening
