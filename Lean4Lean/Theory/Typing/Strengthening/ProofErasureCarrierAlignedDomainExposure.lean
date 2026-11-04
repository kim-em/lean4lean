import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedTypeResidual
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedPiRoot

/-! # Native Pi exposure retaining the selected domain comparison

The enlarged aligned checker may compare native types through recursive carrier
promotion. At actual type endpoints those promotions reduce to checked type
comparison. Pi exposure can therefore retain the assigned-to-selected domain
certificate needed by a subsequent carrier-transfer argument.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private sort_not_lam sort_not_constructor from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedPiExposure
variable [Params]

private theorem computed_domain_exposure_pair
    (hn : ∀ {Δ A B out}, ¬ Step Δ (.forallE A B) out)
    (H : ComputedJointCheck Step Δ kind a b) (hm : kind = .compare false) :
    (∀ A B, a = .forallE A B → ∃ A' B',
      ScopedCompute Step Δ b (.forallE A' B') ∧ ComputedJointCompare Step Δ true A A') ∧
    (∀ A B, b = .forallE A B → ∃ A' B',
      ScopedCompute Step Δ a (.forallE A' B') ∧ ComputedJointCompare Step Δ true A A') := by
  induction H with
  | leaf H =>
    cases hm
    cases H with
    | refl => constructor <;> intro A B E <;> exact ⟨A, B, E ▸ .refl, .leaf .refl⟩
    | sort | const => constructor <;> intro A B E <;> cases E
  | forallE HA HB =>
    constructor
    · intro A B E; cases E; exact ⟨_, _, .refl, ComputedJointCompare.common HA⟩
    · intro A B E; cases E; exact ⟨_, _, .refl, .symm (ComputedJointCompare.common HA)⟩
  | forallSorted _ _ HA _ _ HB =>
    constructor
    · intro A B E; cases E; exact ⟨_, _, .refl, HA⟩
    · intro A B E; cases E; exact ⟨_, _, .refl, .symm HA⟩
  | compute Ra Rb HC ih =>
    constructor
    · intro A B E
      obtain ⟨A₁, B₁, HE, HA⟩ := (E ▸ Ra).forallE_domain_inv_of_no_root hn
      obtain ⟨A₂, B₂, R, HD⟩ := (ih hm).1 A₁ B₁ HE
      exact ⟨A₂, B₂, Rb.trans R, .compute HA .refl HD⟩
    · intro A B E
      obtain ⟨A₁, B₁, HE, HA⟩ := (E ▸ Rb).forallE_domain_inv_of_no_root hn
      obtain ⟨A₂, B₂, R, HD⟩ := (ih hm).2 A₁ B₁ HE
      exact ⟨A₂, B₂, Ra.trans R, .compute HA .refl HD⟩
  | symm H ih => exact (ih hm).symm
  | app | appCarrier | appComputed | proj | lam | lamSorted | etaLams =>
    constructor <;> intro A B E <;> cases E
  | lamCommon | etaBodyL | etaBodyR | structFields |
      carrierIntro | carrierChecked | carrierSubsingleton | carrierFunction |
      carrierSymm | carrierCompute | carrierReduce | carrierNested => cases hm

private def DomainExposurePair
    (Step : List ProofShape → ProofShape → ProofShape → Prop)
    (Cmp : ProofShape → ProofShape → Prop) (Δ : List ProofShape) (sa sb : ProofShape) : Prop :=
  (∀ A B, sa = .forallE A B → ∃ A' B', ScopedCompute Step Δ sb (.forallE A' B') ∧ Cmp A A') ∧
  (∀ A B, sb = .forallE A B → ∃ A' B', ScopedCompute Step Δ sa (.forallE A' B') ∧ Cmp A A')

private theorem computed_domains
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hn : ∀ {Δ A B out}, ¬ Step Δ (.forallE A B) out)
    (H : ComputedJointCompare Step Δ mode sa sb)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs Γ a (.sort u)) (hb : env.HasType univs Γ b (.sort v))
    (EΓ : proofEraseCtx Γ = Δ) (Ea : proofErase Γ a = sa) (Eb : proofErase Γ b = sb) :
    DomainExposurePair Step (CarrierAlignedCompare Step Δ true) Δ sa sb := by
  have HI := proofErase_computed_joint_types_inferred hstep hΓ ha hb
    (by simpa only [EΓ, Ea, Eb] using H)
  rw [EΓ, Ea, Eb] at HI
  have HH := computed_domain_exposure_pair hn HI rfl
  constructor
  · intro A B E
    obtain ⟨A', B', R, HD⟩ := HH.1 A B E
    exact ⟨A', B', R, .base (.base HD)⟩
  · intro A B E
    obtain ⟨A', B', R, HD⟩ := HH.2 A B E
    exact ⟨A', B', R, .base (.base HD)⟩

private theorem carrier_domains
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hn : ∀ {Δ A B out}, ¬ Step Δ (.forallE A B) out)
    (RA : ScopedTypeRecovery Step Δ sa rawC)
    (HC : ComputedJointCarrierGuard Step Δ rawC sa sb)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs Γ a (.sort u)) (hb : env.HasType univs Γ b (.sort v))
    (EΓ : proofEraseCtx Γ = Δ) (Ea : proofErase Γ a = sa) (Eb : proofErase Γ b = sb) :
    DomainExposurePair Step (CarrierAlignedCompare Step Δ true) Δ sa sb := by
  obtain ⟨C, haC, EC⟩ := proofErase_scoped_typeRecovery_descend hstep hΓ hΓ
    (Ctx.LiftN.zero []) ha EΓ (by simpa only [List.length_nil, ProofShape.liftN_zero, Ea] using RA)
  simp only [List.length_nil, ProofShape.liftN_zero] at EC
  have H := proofErase_computed_carrier_types_checked hstep hΓ ha hb (.inl haC)
    (by simpa only [EΓ, Ea, Eb, EC] using HC)
  exact computed_domains hstep hn (by simpa only [EΓ, Ea, Eb] using H) hΓ ha hb EΓ Ea Eb

private theorem recovered_domains
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hn : ∀ {Δ A B out}, ¬ Step Δ (.forallE A B) out)
    (H : CarrierRecoveredCompare Step Δ mode sa sb)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs Γ a (.sort u)) (hb : env.HasType univs Γ b (.sort v))
    (EΓ : proofEraseCtx Γ = Δ) (Ea : proofErase Γ a = sa) (Eb : proofErase Γ b = sb) :
    DomainExposurePair Step (CarrierAlignedCompare Step Δ true) Δ sa sb := by
  induction H generalizing Γ a b u v with
  | base H => exact computed_domains hstep hn H hΓ ha hb EΓ Ea Eb
  | recovered RA RB HC => exact carrier_domains hstep hn RA HC hΓ ha hb EΓ Ea Eb
  | app | proj => constructor <;> intro A B E <;> cases E
  | lam => exact (sort_not_lam hΓ ha Ea).elim
  | forallE HA HB =>
    constructor
    · intro A B E; cases E; exact ⟨_, _, .refl, .base HA.common⟩
    · intro A B E; cases E; exact ⟨_, _, .refl, .base HA.symm.common⟩
  | compute RA RB H ih =>
    obtain ⟨a', HA, EA⟩ := proofErase_scoped_compute_realize hstep hΓ ha EΓ Ea RA
    obtain ⟨b', HB, EB⟩ := proofErase_scoped_compute_realize hstep hΓ hb EΓ Eb RB
    have IH := ih hΓ HA.hasType.2 HB.hasType.2 EΓ EA EB
    constructor
    · intro A B E
      obtain ⟨A₁, B₁, HE, HD⟩ := (E ▸ RA).forallE_domain_inv_of_no_root hn
      obtain ⟨A₂, B₂, R, HX⟩ := IH.1 A₁ B₁ HE
      exact ⟨A₂, B₂, RB.trans R, .compute HD .refl HX⟩
    · intro A B E
      obtain ⟨A₁, B₁, HE, HD⟩ := (E ▸ RB).forallE_domain_inv_of_no_root hn
      obtain ⟨A₂, B₂, R, HX⟩ := IH.2 A₁ B₁ HE
      exact ⟨A₂, B₂, RA.trans R, .compute HD .refl HX⟩
  | symm H ih => exact (ih hΓ hb ha EΓ Eb Ea).symm

private theorem aligned_domains
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hn : ∀ {Δ A B out}, ¬ Step Δ (.forallE A B) out)
    (H : CarrierAlignedCompare Step Δ mode sa sb)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs Γ a (.sort u)) (hb : env.HasType univs Γ b (.sort v))
    (EΓ : proofEraseCtx Γ = Δ) (Ea : proofErase Γ a = sa) (Eb : proofErase Γ b = sb) :
    DomainExposurePair Step (CarrierAlignedCompare Step Δ true) Δ sa sb := by
  induction H generalizing Γ a b u v with
  | base H => exact recovered_domains hstep hn H hΓ ha hb EΓ Ea Eb
  | commonCarrier RA HC | aligned RA RB HT HC ihT => exact carrier_domains hstep hn RA HC hΓ ha hb EΓ Ea Eb
  | recover RA RB HT HC ihT ihC => exact ihC hΓ ha hb EΓ Ea Eb
  | app | proj => constructor <;> intro A B E <;> cases E
  | lam | lamSorted | lamCommon | etaBodyL | etaLams => exact (sort_not_lam hΓ ha Ea).elim
  | etaBodyR => exact (sort_not_lam hΓ hb Eb).elim
  | structFields hi hx hp hf => exact (sort_not_constructor hΓ ha hi hx hp hf Ea).elim
  | forallE HA HB =>
    constructor
    · intro A B E; cases E; exact ⟨_, _, .refl, HA.common⟩
    · intro A B E; cases E; exact ⟨_, _, .refl, HA.symm.common⟩
  | forallSorted S S' HA T T' HB =>
    constructor
    · intro A B E; cases E; exact ⟨_, _, .refl, HA⟩
    · intro A B E; cases E; exact ⟨_, _, .refl, HA.symm⟩
  | compute RA RB H ih =>
    obtain ⟨a', HA, EA⟩ := proofErase_scoped_compute_realize hstep hΓ ha EΓ Ea RA
    obtain ⟨b', HB, EB⟩ := proofErase_scoped_compute_realize hstep hΓ hb EΓ Eb RB
    have IH := ih hΓ HA.hasType.2 HB.hasType.2 EΓ EA EB
    constructor
    · intro A B E
      obtain ⟨A₁, B₁, HE, HD⟩ := (E ▸ RA).forallE_domain_inv_of_no_root hn
      obtain ⟨A₂, B₂, R, HX⟩ := IH.1 A₁ B₁ HE
      exact ⟨A₂, B₂, RB.trans R, .compute HD .refl HX⟩
    · intro A B E
      obtain ⟨A₁, B₁, HE, HD⟩ := (E ▸ RB).forallE_domain_inv_of_no_root hn
      obtain ⟨A₂, B₂, R, HX⟩ := IH.2 A₁ B₁ HE
      exact ⟨A₂, B₂, RA.trans R, .compute HD .refl HX⟩
  | symm H ih => exact (ih hΓ hb ha EΓ Eb Ea).symm

/-- A typed aligned comparison against a displayed Pi exposes a Pi on the
other side and retains common comparison from the displayed domain to the
selected domain. The supplied comparison may use either checking mode. -/
theorem proofErase_carrier_aligned_pi_domain_exposure_of_no_root
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hn : ∀ {Δ A B out}, ¬ Step Δ (.forallE A B) out)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs Γ a (.sort u)) (hb : env.HasType univs Γ b (.sort v))
    (H : CarrierAlignedCompare Step (proofEraseCtx Γ) mode (proofErase Γ a) (proofErase Γ b))
    (Ea : proofErase Γ a = .forallE A B) :
    ∃ A' B', ScopedCompute Step (proofEraseCtx Γ) (proofErase Γ b) (.forallE A' B') ∧
      CarrierAlignedCompare Step (proofEraseCtx Γ) true A A' :=
  (aligned_domains hstep hn H hΓ ha hb rfl rfl rfl).1 A B Ea

/-- Native recovery compared with an actual assigned Pi yields an actual new
Pi typing, exact native recovery there, and an inferred comparison from the
assigned domain to the newly selected domain. No exact assigned-Pi recovery or
comparison completeness is assumed. -/
theorem proofErase_carrier_aligned_recovered_pi_domain_of_no_root
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hn : ∀ {Δ A B out}, ¬ Step Δ (.forallE A B) out)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (.forallE A B))
    (R : ScopedTypeRecovery Step (proofEraseCtx Γ) (proofErase Γ f) T)
    (H : CarrierAlignedCompare Step (proofEraseCtx Γ) mode T (proofErase Γ (.forallE A B))) :
    ∃ D C, env.HasType univs Γ f (.forallE D C) ∧
      ScopedTypeRecovery Step (proofEraseCtx Γ) (proofErase Γ f)
        (.forallE (proofErase Γ D) (proofErase (D :: Γ) C)) ∧
      CarrierAlignedCompare Step (proofEraseCtx Γ) false (proofErase Γ A) (proofErase Γ D) := by
  obtain ⟨F, hfF, EF⟩ := proofErase_scoped_typeRecovery_replay hstep hΓ hf R
  obtain ⟨u, hF⟩ := hfF.isType henv hΓ
  obtain ⟨v, hPi⟩ := hf.isType henv hΓ
  have EPi : proofErase Γ (.forallE A B) = .forallE (proofErase Γ A) (proofErase (A :: Γ) B) :=
    if_neg (not_isProof_of_sort hΓ hPi)
  obtain ⟨D', C', RT, HD⟩ := proofErase_carrier_aligned_pi_domain_exposure_of_no_root hstep hn hΓ hPi hF
    (by simpa only [EF] using H.symm) EPi
  rw [EF] at RT
  have R' := R.convert RT
  obtain ⟨D, C, hfDC, ED, EC⟩ := proofErase_scoped_recovered_pi_descend hstep hΓ hΓ
    (show Ctx.LiftN 0 0 Γ Γ from .zero []) hf
    (by simpa only [ProofShape.liftN_zero] using R')
  simp only [ProofShape.liftN_zero] at ED EC
  rw [← ED, ← EC] at R'
  rw [← ED] at HD
  obtain ⟨_, hDC⟩ := hfDC.isType henv hΓ
  obtain ⟨⟨_, hA⟩, _, _⟩ := hPi.forallE_inv henv
  obtain ⟨⟨_, hD⟩, _, _⟩ := hDC.forallE_inv henv
  exact ⟨D, C, hfDC, R', proofErase_carrier_aligned_types_inferred hstep hΓ hA hD HD⟩

/-- Compatibility with the original constant/projection primitive-head interface. -/
theorem proofErase_carrier_aligned_pi_domain_exposure
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs Γ a (.sort u)) (hb : env.HasType univs Γ b (.sort v))
    (H : CarrierAlignedCompare Step (proofEraseCtx Γ) mode (proofErase Γ a) (proofErase Γ b))
    (Ea : proofErase Γ a = .forallE A B) :
    ∃ A' B', ScopedCompute Step (proofEraseCtx Γ) (proofErase Γ b) (.forallE A' B') ∧
      CarrierAlignedCompare Step (proofEraseCtx Γ) true A A' :=
  proofErase_carrier_aligned_pi_domain_exposure_of_no_root hstep (fun H => (hhead H).elim) hΓ ha hb H Ea

/-- Compatibility with the original constant/projection primitive-head interface. -/
theorem proofErase_carrier_aligned_recovered_pi_domain
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (.forallE A B))
    (R : ScopedTypeRecovery Step (proofEraseCtx Γ) (proofErase Γ f) T)
    (H : CarrierAlignedCompare Step (proofEraseCtx Γ) mode T (proofErase Γ (.forallE A B))) :
    ∃ D C, env.HasType univs Γ f (.forallE D C) ∧
      ScopedTypeRecovery Step (proofEraseCtx Γ) (proofErase Γ f)
        (.forallE (proofErase Γ D) (proofErase (D :: Γ) C)) ∧
      CarrierAlignedCompare Step (proofEraseCtx Γ) false (proofErase Γ A) (proofErase Γ D) :=
  proofErase_carrier_aligned_recovered_pi_domain_of_no_root hstep (fun H => (hhead H).elim) hΓ hf R H

end Lean4Lean.VEnv.Strengthening
