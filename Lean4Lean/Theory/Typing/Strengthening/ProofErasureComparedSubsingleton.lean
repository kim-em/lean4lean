import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointTransport
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedContextConversion
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureBetaStableJoint
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointTypeExposure
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierDomainJoin
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointDomainExposure

/-! # Structural subsingletons transported by actual type comparison

An actual comparison certificate replaces semantic head adequacy for this
carrier fragment. Dependent Pi codomains are handled in their original binder
contexts and their paths are moved to the target binder by primitive context
transport. No arbitrary semantic conversion law is assumed.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private erase_forallE_inv
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
open private infer_raw
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointTransport
open private sort_not_lam sort_not_constructor
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedPiExposure
variable [Params]

private theorem subsingleton_pi (H : SubsingletonCarrier (.forallE A B)) : SubsingletonCarrier B := by
  generalize E : ProofShape.forallE A B = C at H
  cases H with
  | unit =>
    have HE := congrArg constHead E
    simp only [constHead, constHead_mkApps] at HE
    cases HE
  | forallE H => cases E; exact H

private theorem subsingleton_nonpi_compute
    (hinert : ∀ {family info Δ ls args out}, env.projections family info →
      ¬ Step Δ (mkApps (.const family ls) args) out)
    (R : ScopedCompute Step Δ A B) (H : SubsingletonCarrier A)
    (hn : ∀ D C, A ≠ .forallE D C) : SubsingletonCarrier B := by
  cases H with
  | unit hi hx hf hp =>
    obtain ⟨ps', rfl, HA⟩ := R.const_spine (hinert hi)
    exact .unit hi hx hf (HA.length_eq.symm.trans hp)
  | forallE => exact (hn _ _ rfl).elim

/-- Structural subsingletons survive scoped computation whenever registered
family heads are inert. Parameter computations and changing Pi domains do
not affect the recursively subsingleton codomain certificate. -/
theorem ProofShape.SubsingletonCarrier.scoped_compute
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (hinert : ∀ {family info Δ ls args out}, env.projections family info →
      ¬ Step Δ (mkApps (.const family ls) args) out)
    (R : ScopedCompute Step Δ A B) (H : SubsingletonCarrier A) : SubsingletonCarrier B := by
  induction R with
  | base HP =>
    cases H with
    | unit hi => exact (hinert hi HP).elim
    | forallE => exact (hhead HP).elim
  | beta HB => exact H.beta HB
  | trans _ _ ih₁ ih₂ => exact ih₂ (ih₁ H)
  | forallE RA RB ihA ihB =>
    exact .forallE (ihB (subsingleton_pi H))
  | app RA RB => exact subsingleton_nonpi_compute hinert (.app RA RB) H (by intros; intro E; cases E)
  | proj R => exact subsingleton_nonpi_compute hinert (.proj R) H (by intros; intro E; cases E)
  | lam RA RB => exact subsingleton_nonpi_compute hinert (.lam RA RB) H (by intros; intro E; cases E)

private def SubsingletonComparisonPair
    (Step : List ProofShape → ProofShape → ProofShape → Prop)
    (Δ : List ProofShape) (sa sb : ProofShape) : Prop :=
  ∀ {Γ T U u v}, OnCtx Γ (env.IsType univs) →
    env.HasType univs Γ T (.sort u) → env.HasType univs Γ U (.sort v) →
    proofEraseCtx Γ = Δ → proofErase Γ T = sa → proofErase Γ U = sb →
    (SubsingletonCarrier sa → ∃ out, ScopedCompute Step Δ sb out ∧ SubsingletonCarrier out) ∧
    (SubsingletonCarrier sb → ∃ out, ScopedCompute Step Δ sa out ∧ SubsingletonCarrier out)

private theorem nonpi_target
    (hinert : ∀ {family info Δ ls args out}, env.projections family info →
      ¬ Step Δ (mkApps (.const family ls) args) out)
    (HC : JointCompare Step Δ false a b) (HS : SubsingletonCarrier a)
    (hn : ∀ A B, a ≠ .forallE A B) :
    ∃ out, ScopedCompute Step Δ b out ∧ SubsingletonCarrier out := by
  cases HS with
  | unit hi hx hf hp =>
    obtain ⟨ls', ps', R, hl⟩ := HC.const_spine_exposure (hinert hi)
    exact ⟨_, R, .unit hi hx hf (hl.trans hp)⟩
  | forallE => exact (hn _ _ rfl).elim

private theorem nonpi_pair
    (hinert : ∀ {family info Δ ls args out}, env.projections family info →
      ¬ Step Δ (mkApps (.const family ls) args) out)
    (HC : JointCompare Step Δ false a b)
    (ha : ∀ A B, a ≠ .forallE A B) (hb : ∀ A B, b ≠ .forallE A B) :
    SubsingletonComparisonPair Step Δ a b := by
  intro Γ T U u v hΓ hT hU EΓ ET EU
  exact ⟨fun H => nonpi_target hinert HC H ha, fun H => nonpi_target hinert HC.symm H hb⟩

private theorem pi_pair
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hsubst : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextSubstitution Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (HA : JointCompare Step Δ mode A C)
    (IH : SubsingletonComparisonPair Step (A :: Δ) B D) :
    SubsingletonComparisonPair Step Δ (.forallE A B) (.forallE C D) := by
  intro Γ T U u v hΓ hT hU EΓ ET EU
  obtain ⟨A₀, B₀, rfl, _, EA, EB⟩ := erase_forallE_inv ET
  obtain ⟨C₀, D₀, rfl, _, EC, ED⟩ := erase_forallE_inv EU
  obtain ⟨⟨w, hA⟩, _, hB⟩ := hT.forallE_inv henv
  obtain ⟨⟨z, hC⟩, _, hD⟩ := hU.forallE_inv henv
  have HAC := proofErase_joint_types_inferred hstep hΓ hA hC
    (by simpa only [EΓ, EA, EC] using HA)
  have HE := infer_raw hstep HAC hΓ hA hC rfl rfl rfl
    (not_isProof_of_sort hΓ hA) (not_isProof_of_sort hΓ hC)
  have W : IsDefEqCtx env univs Γ (A₀ :: Γ) (C₀ :: Γ) := .succ .zero HE
  have hΓA : OnCtx (A₀ :: Γ) (env.IsType univs) := ⟨hΓ, _, hA⟩
  have hDA := hD.defeqDFC henv (W.symm henv.ordered)
  have EDA : proofErase (A₀ :: Γ) D₀ = D := by
    rw [proofErase_defeqCtx hΓA W hDA]
    exact ED
  have IH' := IH hΓA hB hDA (by simp only [proofEraseCtx, EA, EΓ]) EB EDA
  constructor
  · intro HS
    have HS' : SubsingletonCarrier B := subsingleton_pi HS
    obtain ⟨out, R, Hout⟩ := IH'.1 HS'
    have R' : ScopedCompute Step (proofEraseCtx (A₀ :: Γ)) D out := by
      simpa only [proofEraseCtx, EA, EΓ] using R
    have R' := R'.defeqCtx hsubst hΓ W
    refine ⟨.forallE C out, .forallE .refl ?_, .forallE Hout⟩
    simpa only [proofEraseCtx, EC, EΓ] using R'
  · intro HS
    have HS' : SubsingletonCarrier D := subsingleton_pi HS
    obtain ⟨out, R, Hout⟩ := IH'.2 HS'
    exact ⟨.forallE A out, .forallE .refl R, .forallE Hout⟩

private theorem comparison_pair
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (hinert : ∀ {family info Δ ls args out}, env.projections family info →
      ¬ Step Δ (mkApps (.const family ls) args) out)
    (hsubst : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextSubstitution Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (H : JointCheck Step Δ kind a b) (hm : kind = .compare mode) :
    SubsingletonComparisonPair Step Δ a b := by
  induction H generalizing mode with
  | leaf H =>
    cases hm
    cases H with
    | refl => intro Γ T U u v hΓ hT hU EΓ ET EU; exact ⟨fun HS => ⟨_, .refl, HS⟩, fun HS => ⟨_, .refl, HS⟩⟩
    | sort H => exact nonpi_pair hinert (.leaf (.sort H)) (by intros; intro E; cases E) (by intros; intro E; cases E)
    | const H => exact nonpi_pair hinert (.leaf (.const H)) (by intros; intro E; cases E) (by intros; intro E; cases E)
    | etaL H =>
      intro Γ T U u v hΓ hT hU EΓ ET EU
      obtain ⟨_, _, E, _⟩ := H.shape
      exact (sort_not_lam hΓ hT (ET.trans E)).elim
    | etaR H =>
      intro Γ T U u v hΓ hT hU EΓ ET EU
      obtain ⟨_, _, E, _⟩ := H.shape
      exact (sort_not_lam hΓ hU (EU.trans E)).elim
  | app HF HX => exact nonpi_pair hinert (.app HF HX) (by intros; intro E; cases E) (by intros; intro E; cases E)
  | appCarrier R HF HX => exact nonpi_pair hinert (.appCarrier R HF HX) (by intros; intro E; cases E) (by intros; intro E; cases E)
  | proj H => exact nonpi_pair hinert (.proj H) (by intros; intro E; cases E) (by intros; intro E; cases E)
  | lam | lamSorted | lamCommon | etaBodyL | etaLams =>
    intro Γ T U u v hΓ hT hU EΓ ET EU
    exact (sort_not_lam hΓ hT ET).elim
  | etaBodyR =>
    intro Γ T U u v hΓ hT hU EΓ ET EU
    exact (sort_not_lam hΓ hU EU).elim
  | structFields hi hx hp hf =>
    intro Γ T U u v hΓ hT hU EΓ ET EU
    exact (sort_not_constructor hΓ hT hi hx hp hf ET).elim
  | forallE HA HB ihA ihB => exact pi_pair hstep hsubst HA (ihB rfl)
  | forallSorted S S' HA T T' HB ihA ihB => exact pi_pair hstep hsubst HA (ihB rfl)
  | compute RA RB HC ih =>
    intro Γ T U u v hΓ hT hU EΓ ET EU
    obtain ⟨T', HT, ET'⟩ := proofErase_scoped_compute_realize hstep hΓ hT EΓ ET RA
    obtain ⟨U', HU, EU'⟩ := proofErase_scoped_compute_realize hstep hΓ hU EΓ EU RB
    have IH := ih hm hΓ HT.hasType.2 HU.hasType.2 EΓ ET' EU'
    constructor
    · intro HS
      obtain ⟨out, R, Hout⟩ := IH.1 (HS.scoped_compute hhead hinert RA)
      exact ⟨out, RB.trans R, Hout⟩
    · intro HS
      obtain ⟨out, R, Hout⟩ := IH.2 (HS.scoped_compute hhead hinert RB)
      exact ⟨out, RA.trans R, Hout⟩
  | symm H ih =>
    intro Γ T U u v hΓ hT hU EΓ ET EU
    exact (ih hm hΓ hU hT EΓ EU ET).symm
  | carrierIntro | carrierChecked | carrierSubsingleton | carrierFunction |
      carrierSymm | carrierCompute | carrierReduce | carrierNested => cases hm


/-- Typed comparison transports structural subsingletons, including arbitrary
Pi telescopes, by computing the target to a structural subsingleton. Both the
comparison and output path use the same primitive relation. No semantic head
exposure, comparison completeness, or endpoint beta transport is assumed. -/
theorem proofErase_joint_compared_subsingleton_compute
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (hinert : ∀ {family info Δ ls args out}, env.projections family info →
      ¬ Step Δ (mkApps (.const family ls) args) out)
    (hsubst : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextSubstitution Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (hΓ : OnCtx Γ (env.IsType univs))
    (hT : env.HasType univs Γ T (.sort u)) (hU : env.HasType univs Γ U (.sort v))
    (HC : JointCompare Step (proofEraseCtx Γ) mode (proofErase Γ T) (proofErase Γ U))
    (HS : SubsingletonCarrier (proofErase Γ T)) :
    ∃ out, ScopedCompute Step (proofEraseCtx Γ) (proofErase Γ U) out ∧ SubsingletonCarrier out :=
  (comparison_pair hstep hhead hinert hsubst HC rfl hΓ hT hU rfl rfl rfl).1 HS

/-- An actual type-comparison certificate supplies a target carrier guard
for every pair of endpoints when the source is structurally subsingleton.
Sound use supplies their typings at the target type separately. -/
theorem proofErase_joint_compared_subsingleton_guard
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (hinert : ∀ {family info Δ ls args out}, env.projections family info →
      ¬ Step Δ (mkApps (.const family ls) args) out)
    (hsubst : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextSubstitution Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (hΓ : OnCtx Γ (env.IsType univs))
    (hT : env.HasType univs Γ T (.sort u)) (hU : env.HasType univs Γ U (.sort v))
    (HC : JointCompare Step (proofEraseCtx Γ) mode (proofErase Γ T) (proofErase Γ U))
    (HS : SubsingletonCarrier (proofErase Γ T)) :
    JointCarrierGuard Step (proofEraseCtx Γ) (proofErase Γ U) a b := by
  obtain ⟨out, R, Hout⟩ := proofErase_joint_compared_subsingleton_compute
    hstep hhead hinert hsubst hΓ hT hU HC HS
  exact .carrierCompute R (.carrierSubsingleton Hout)

/-- A compared recovery at a function whose assigned domain is structurally
subsingleton supplies a new Pi recovery and its argument guard together.
The new domain need not be the assigned domain or have a literal join with it. -/
theorem proofErase_joint_compared_recovery_subsingleton_guard
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (hinert : ∀ {family info Δ ls args out}, env.projections family info →
      ¬ Step Δ (mkApps (.const family ls) args) out)
    (hsubst : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextSubstitution Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (.forallE A B))
    (R : ScopedTypeRecovery Step (proofEraseCtx Γ) (proofErase Γ f) T)
    (HC : JointCompare Step (proofEraseCtx Γ) mode T (proofErase Γ (.forallE A B)))
    (HS : SubsingletonCarrier (proofErase Γ A)) :
    ∃ D C, ScopedTypeRecovery Step (proofEraseCtx Γ) (proofErase Γ f) (.forallE D C) ∧
      JointCarrierGuard Step (proofEraseCtx Γ) D x y := by
  obtain ⟨D, C, hfDC, RD, HD⟩ := proofErase_joint_recovered_pi_domain hstep hhead hΓ hf R HC
  obtain ⟨_, hAB⟩ := hf.isType henv hΓ
  obtain ⟨⟨_, hA⟩, _, _⟩ := hAB.forallE_inv henv
  obtain ⟨_, hDC⟩ := hfDC.isType henv hΓ
  obtain ⟨⟨_, hD⟩, _, _⟩ := hDC.forallE_inv henv
  exact ⟨_, _, RD, proofErase_joint_compared_subsingleton_guard hstep hhead hinert hsubst hΓ hA hD HD HS⟩

/-- The actual application rule consumes the recovered domain and its rebuilt
subsingleton argument guard. Recovery and assigned-type comparison are local
input certificates; no coverage assumption is made for arbitrary typings. -/
theorem proofErase_joint_application_of_compared_recovery_subsingleton
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (hinert : ∀ {family info Δ ls args out}, env.projections family info →
      ¬ Step Δ (mkApps (.const family ls) args) out)
    (hsubst : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextSubstitution Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (.forallE A B))
    (R : ScopedTypeRecovery Step (proofEraseCtx Γ) (proofErase Γ f) T)
    (HC : JointCompare Step (proofEraseCtx Γ) mode T (proofErase Γ (.forallE A B)))
    (HS : SubsingletonCarrier (proofErase Γ A))
    (HF : JointCompare Step (proofEraseCtx Γ) false (proofErase Γ f) g) :
    JointCompare Step (proofEraseCtx Γ) resultMode (.app (proofErase Γ f) x) (.app g y) := by
  obtain ⟨D, C, RD, HG⟩ := proofErase_joint_compared_recovery_subsingleton_guard
    hstep hhead hinert hsubst hΓ hf R HC HS (x := x) (y := y)
  exact .appCarrier RD HF HG

/-- At stage zero, core substitution supplies the required context transport
unconditionally. An actual type comparison preserves every structural
subsingleton guard without increasing the primitive stage. -/
theorem proofErase_joint_zero_compared_subsingleton_guard
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hD : ∀ {family info}, env.projections family info → ∀ levels rhs, ¬ D.unfolds family levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hT : env.HasType univs Γ T (.sort u)) (hU : env.HasType univs Γ U (.sort v))
    (HC : JointCompare (ErasedJointStage D 0) (proofEraseCtx Γ) mode (proofErase Γ T) (proofErase Γ U))
    (HS : SubsingletonCarrier (proofErase Γ T)) :
    JointCarrierGuard (ErasedJointStage D 0) (proofEraseCtx Γ) (proofErase Γ U) a b := by
  apply proofErase_joint_compared_subsingleton_guard (erased_joint_stage_descent heq hs 0)
    (erased_joint_stage_head 0) ?_ ?_ hΓ hT hU HC HS
  · intro family info Δ ls args out hi H
    exact erased_joint_stage_no_rigid heq (henv.projectionRigid hi) (hD hi) 0 H (constHead_mkApps _ _)
  · intro Δ Δ' a b τ H W
    exact erased_iota_primitive_subst H

/-- Certified joint checking supports the same comparison-directed transport
at its own relation, using its established primitive substitution law. This
requires the actual comparison certificate, not merely semantic equality. -/
theorem proofErase_certified_compared_subsingleton_guard
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hD : ∀ {family info}, env.projections family info → ∀ levels rhs, ¬ D.unfolds family levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hT : env.HasType univs Γ T (.sort u)) (hU : env.HasType univs Γ U (.sort v))
    (HC : JointCompare (ErasedBetaStableJoint D) (proofEraseCtx Γ) mode (proofErase Γ T) (proofErase Γ U))
    (HS : SubsingletonCarrier (proofErase Γ T)) :
    JointCarrierGuard (ErasedBetaStableJoint D) (proofEraseCtx Γ) (proofErase Γ U) a b := by
  apply proofErase_joint_compared_subsingleton_guard (erased_beta_stable_joint_descent heq hs)
    erased_beta_stable_joint_head ?_ (erased_beta_stable_joint_subst heq hs) hΓ hT hU HC HS
  intro family info Δ ls args out hi H
  exact erased_joint_union_no_rigid heq (henv.projectionRigid hi) (hD hi)
    (erased_beta_stable_joint_into_union H) (constHead_mkApps _ _)

end Lean4Lean.VEnv.Strengthening
