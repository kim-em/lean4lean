import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJoinedNativeGuard
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointCertifiedChecking

/-! # Certified application guards through beta-joined native prefixes

Retaining pure beta paths through raw telescope supply allows the already
proved certified carrier transport to consume the native domain join. This
covers all certified joint guard constructors without a proposition beta law.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private beta_forallE_parts
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierDomainJoin
open private native_walk_type
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureNativeSupplyJoin

private theorem beta_images (e : ProofShape) {σ τ : ProofShape.Subst}
    (H : ∀ i, ProofShape.BetaRed (σ i) (τ i)) :
    ProofShape.BetaRed (e.subst σ) (e.subst τ) := by
  induction e generalizing σ τ with
  | proof | sort | const => exact .refl
  | bvar i => exact H i
  | app _ _ ihf iha => exact .app (ihf H) (iha H)
  | proj _ _ _ ih => exact .proj (ih H)
  | lam _ _ ihA ihb | forallE _ _ ihA ihb =>
    have HB : ∀ i, ProofShape.BetaRed (σ.lift i) (τ.lift i) := by
      intro i
      cases i with
      | zero => exact .refl
      | succ i => exact (H i).liftN
    first | exact .lam (ihA H) (ihb HB) | exact .forallE (ihA H) (ihb HB)

private theorem beta_inst_image (e : ProofShape) (R : ProofShape.BetaRed x y) :
    ProofShape.BetaRed (e.inst x) (e.inst y) := by
  simp only [ProofShape.inst_eq_subst]
  apply beta_images
  intro i
  cases i with
  | zero => exact R
  | succ i => exact .refl

/-- Literal raw telescope supply survives simultaneous beta reduction of its
type and arguments, and its output only beta-reduces. No typing, primitive
closure, or normalization premise is needed for this raw syntactic fact. -/
theorem ProofShape.supplyType_beta
    (HS : ProofShape.supplyType args T = some out)
    (RT : ProofShape.BetaRed T T') (HA : List.Forall₂ ProofShape.BetaRed args args') :
    ∃ out', ProofShape.supplyType args' T' = some out' ∧ ProofShape.BetaRed out out' := by
  induction args generalizing args' T T' out with
  | nil => cases HA; cases HS; exact ⟨_, rfl, RT⟩
  | cons a args ih =>
    cases HA with
    | cons RA HA =>
      cases T <;> try contradiction
      rename_i A B
      obtain ⟨A', B', rfl, _, RB⟩ := beta_forallE_parts RT
      have RB' : ProofShape.BetaRed (B.inst a) (B'.inst a) := by
        simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using RB.subst (σ := ProofShape.Subst.one a)
      obtain ⟨out', HS', R⟩ := ih HS (RB'.trans (beta_inst_image B' RA)) HA
      exact ⟨out', HS', R⟩

variable [Params]

/-- Beta-joined typed prefixes give beta-joined native residuals. Retaining
this stronger path label enables certified carrier transport, where arbitrary
primitive computation of carrier types is not known to transport guards. -/
theorem proofErase_native_residuals_beta_join
    (hΓ : OnCtx Γ (env.IsType univs)) (hT : env.HasType univs Γ T (.sort u))
    (HW : InstForallsC env univs Γ T args residual)
    (HW' : InstForallsC env univs Γ T args' residual')
    (HA : List.Forall₂ ProofShape.BetaRed (args.map (proofErase Γ)) sharedArgs)
    (HA' : List.Forall₂ ProofShape.BetaRed (args'.map (proofErase Γ)) sharedArgs) :
    ∃ out, ProofShape.supplyType sharedArgs (proofErase Γ T) = some out ∧
      ProofShape.BetaRed (proofErase Γ residual) out ∧
      ProofShape.BetaRed (proofErase Γ residual') out := by
  obtain ⟨out, HS, R⟩ := ProofShape.supplyType_beta (proofErase_native_supply hΓ hT HW) .refl HA
  obtain ⟨out', HS', R'⟩ := ProofShape.supplyType_beta (proofErase_native_supply hΓ hT HW') .refl HA'
  cases Option.some.inj (HS.symm.trans HS')
  exact ⟨out, HS, R, R'⟩

/-- Every certified joint argument guard transfers to a recovered common Pi
of beta-joined native prefixes. The primitive certificates and guard remain
in the same certified relation, with no stage-wide beta-transport hypothesis. -/
theorem proofErase_certified_beta_joined_native_guard
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hc : env.constants c = some ci) (hw : ∀ l ∈ ls, l.WF univs)
    (hl : ls.length = ci.uvars)
    (HW : InstForallsC env univs Γ (ci.type.instL ls) args (.forallE A B))
    (HW' : InstForallsC env univs Γ (ci.type.instL ls) args' (.forallE A' B'))
    (hn : ¬ IsProof Γ (VExpr.mkApps (.const c ls) args'))
    (HA : List.Forall₂ ProofShape.BetaRed (args.map (proofErase Γ)) sharedArgs)
    (HA' : List.Forall₂ ProofShape.BetaRed (args'.map (proofErase Γ)) sharedArgs)
    (hx : env.HasType univs Γ x A) (hy : env.HasType univs Γ y A)
    (HX : JointCarrierGuard (ErasedBetaStableJoint D) (proofEraseCtx Γ)
      (proofErase Γ A) (proofErase Γ x) (proofErase Γ y)) :
    ∃ domain body, ScopedTypeRecovery (ErasedBetaStableJoint D) (proofEraseCtx Γ)
        (proofErase Γ (VExpr.mkApps (.const c ls) args')) (.forallE domain body) ∧
      ProofShape.BetaRed (proofErase Γ A) domain ∧
      ProofShape.BetaRed (proofErase Γ A') domain ∧
      JointCarrierGuard (ErasedBetaStableJoint D) (proofEraseCtx Γ)
        domain (proofErase Γ x) (proofErase Γ y) := by
  have hf : env.HasType univs [] (.const c ls) (ci.type.instL ls) := .const hc hw hl
  obtain ⟨_, hT⟩ := hf.isType henv (by trivial)
  have hTΓ := hT.weak0 henv.ordered (Γ := Γ)
  obtain ⟨out, _, R, R'⟩ := proofErase_native_residuals_beta_join hΓ hTΓ HW HW' HA HA'
  obtain ⟨_, hPi⟩ := native_walk_type hTΓ HW
  obtain ⟨_, hPi'⟩ := native_walk_type hTΓ HW'
  have RR := R
  have RR' := R'
  rw [show proofErase Γ (.forallE A B) = .forallE _ _ from
    if_neg (not_isProof_of_sort hΓ hPi)] at RR
  rw [show proofErase Γ (.forallE A' B') = .forallE _ _ from
    if_neg (not_isProof_of_sort hΓ hPi')] at RR'
  obtain ⟨domain, body, rfl, RD, _⟩ := beta_forallE_parts RR
  obtain ⟨_, _, E, RD', _⟩ := beta_forallE_parts RR'
  cases E
  have RF := proofErase_const_native_recovery (Step := ErasedBetaStableJoint D) hΓ hc hw hl HW' hn
  have W : ContextOracleBeta (proofEraseCtx Γ) (proofEraseCtx Γ) :=
    ⟨ContextSubstitution.of_defeqCtx hΓ (.zero (Γ₀ := Γ)), fun _ => .refl⟩
  exact ⟨domain, body, RF.convert (.beta R'), RD, RD',
    proofErase_beta_stable_joint_oracle_beta heq hs HX hΓ hx hy rfl rfl rfl rfl W domain RD⟩

/-- Beta-joined prefixes close the application rule using any certified joint
guard, including nested fields and functions with certified singleton steps. -/
theorem proofErase_certified_application_of_beta_joined_native_prefixes
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hc : env.constants c = some ci) (hw : ∀ l ∈ ls, l.WF univs)
    (hl : ls.length = ci.uvars)
    (HW : InstForallsC env univs Γ (ci.type.instL ls) args (.forallE A B))
    (HW' : InstForallsC env univs Γ (ci.type.instL ls) args' (.forallE A' B'))
    (hn : ¬ IsProof Γ (VExpr.mkApps (.const c ls) args'))
    (HA : List.Forall₂ ProofShape.BetaRed (args.map (proofErase Γ)) sharedArgs)
    (HA' : List.Forall₂ ProofShape.BetaRed (args'.map (proofErase Γ)) sharedArgs)
    (hx : env.HasType univs Γ x A) (hy : env.HasType univs Γ y A)
    (HX : JointCarrierGuard (ErasedBetaStableJoint D) (proofEraseCtx Γ)
      (proofErase Γ A) (proofErase Γ x) (proofErase Γ y))
    (HF : JointCompare (ErasedBetaStableJoint D) (proofEraseCtx Γ) false
      (proofErase Γ (VExpr.mkApps (.const c ls) args')) g) :
    JointCompare (ErasedBetaStableJoint D) (proofEraseCtx Γ) mode
      (.app (proofErase Γ (VExpr.mkApps (.const c ls) args')) (proofErase Γ x))
      (.app g (proofErase Γ y)) := by
  obtain ⟨_, _, RF, _, _, HG⟩ := proofErase_certified_beta_joined_native_guard
    heq hs hΓ hc hw hl HW HW' hn HA HA' hx hy HX
  exact .appCarrier RF HF HG

end Lean4Lean.VEnv.Strengthening
