import Lean4Lean.Theory.Typing.Strengthening.ProofErasureNativeTelescopeRecovery
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureBetaStableJoint

/-! # Reading argument guards at a declaration's native prefix domain

Two copies of the same typed constant prefix may compute independently before
comparison. The original native domain computes to every selected application
domain on either branch. Thus the final argument guard can be read at that
original domain, retaining computation prefixes and comparison symmetry.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params]

/-- Recovering a computed constant prefix cannot escape the original native
Pi domain. The primitive relation must keep this constant head inert. -/
theorem proofErase_computed_const_prefix_domain
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (hsubst : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextSubstitution Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (hn : ∀ {Δ ls args out}, ¬ Step Δ (ProofShape.mkApps (.const c ls) args) out)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hc : env.constants c = some ci) (hw : ∀ l ∈ ls, l.WF univs)
    (hl : ls.length = ci.uvars)
    (HW : InstForallsC env univs Γ (ci.type.instL ls) args (.forallE A B))
    (hPi : env.HasType univs Γ (.forallE A B) (.sort u))
    (RP : ScopedCompute Step (proofEraseCtx Γ)
      (ProofShape.mkApps (.const c ls) (args.map (proofErase Γ))) f)
    (R : ScopedTypeRecovery Step (proofEraseCtx Γ) f (.forallE D C)) :
    ScopedCompute Step (proofEraseCtx Γ) (proofErase Γ A) D := by
  obtain ⟨args', rfl, HA⟩ := RP.const_spine hn
  have H := proofErase_computed_const_prefix_native_compute hstep hhead hsubst hΓ hc hw hl HW HA R
  rw [show proofErase Γ (.forallE A B) = .forallE (proofErase Γ A) (proofErase (A :: Γ) B) from
    if_neg (not_isProof_of_sort hΓ hPi)] at H
  obtain ⟨_, _, HE, HD⟩ := H.forallE_domain_inv hhead
  cases HE
  exact HD

omit [Params] in
private theorem forall₂_snoc {Rel : α → β → Prop} (H : List.Forall₂ Rel (xs ++ [x]) ys) :
    ∃ ys' y, ys = ys' ++ [y] ∧ List.Forall₂ Rel xs ys' ∧ Rel x y := by
  induction xs generalizing ys with
  | nil => cases H with | cons H Hnil => cases Hnil; exact ⟨[], _, rfl, .nil, H⟩
  | cons a as ih =>
    cases H with | cons H Hrest =>
    obtain ⟨ys', y, rfl, HY, Hxy⟩ := ih Hrest
    exact ⟨_, _, rfl, .cons H HY, Hxy⟩

omit [Params] in
private theorem compute_apps
    (HF : ScopedCompute Step Δ f g) (HA : List.Forall₂ (ScopedCompute Step Δ) args args') :
    ScopedCompute Step Δ (ProofShape.mkApps f args) (ProofShape.mkApps g args') := by
  induction HA generalizing f g with
  | nil => exact HF
  | cons H _ ih => exact ih (.app HF H)

omit [Params] in
private theorem const_app_compute
    (hn : ∀ {Δ ls args out}, ¬ Step Δ (ProofShape.mkApps (.const c ls) args) out)
    (R : ScopedCompute Step Δ (.app (ProofShape.mkApps (.const c ls) args) x) out) :
    ∃ args' x', out = .app (ProofShape.mkApps (.const c ls) args') x' ∧
      ScopedCompute Step Δ (ProofShape.mkApps (.const c ls) args)
        (ProofShape.mkApps (.const c ls) args') ∧ ScopedCompute Step Δ x x' := by
  rw [← ProofShape.mkApps_snoc] at R
  obtain ⟨ys, E, HY⟩ := R.const_spine hn
  obtain ⟨ys', y, rfl, HA, HX⟩ := forall₂_snoc HY
  rw [ProofShape.mkApps_snoc] at E
  exact ⟨_, _, E, compute_apps .refl HA, HX⟩

/-- Inferred comparison of two inert constant spines retains inferred
comparison of their prefixes after deleting the last argument. Computations
of both prefixes are preserved; no typing or native recovery is required. -/
theorem ProofShape.JointCompare.const_app_prefix
    (hn : ∀ {Δ ls args out}, ¬ Step Δ (ProofShape.mkApps (.const c ls) args) out)
    (H : JointCompare Step Δ false
      (.app (ProofShape.mkApps (.const c ls) as) x)
      (.app (ProofShape.mkApps (.const c ls') bs) y)) :
    JointCompare Step Δ false (ProofShape.mkApps (.const c ls) as)
      (ProofShape.mkApps (.const c ls') bs) := by
  generalize Ea : ProofShape.app (ProofShape.mkApps (.const c ls) as) x = a at H
  generalize Eb : ProofShape.app (ProofShape.mkApps (.const c ls') bs) y = b at H
  change JointCheck Step Δ (.compare false) a b at H
  generalize hm : JointCheckKind.compare false = kind at H
  induction H generalizing ls as x ls' bs y with
  | leaf H =>
    cases hm
    cases H with
    | refl =>
      have E := (ProofShape.app.inj (Ea.trans Eb.symm)).1
      exact E ▸ JointCheck.leaf ScopedLeaf.refl
    | sort | const => cases Ea
  | app HF HX => cases Ea; cases Eb; exact HF
  | appCarrier R HF HX => cases Ea; cases Eb; exact HF
  | compute Ra Rb HC ih =>
    obtain ⟨as', x', EA, RA, _⟩ := const_app_compute hn (Ea ▸ Ra)
    obtain ⟨bs', y', EB, RB, _⟩ := const_app_compute hn (Eb ▸ Rb)
    exact .compute RA RB (ih EA.symm EB.symm hm)
  | symm H ih => exact .symm (ih Eb Ea hm)
  | proj | lam | forallE | lamSorted | forallSorted | etaLams => cases Ea
  | lamCommon | etaBodyL | etaBodyR | structFields |
      carrierIntro | carrierChecked | carrierSubsingleton | carrierFunction |
      carrierSymm | carrierCompute | carrierReduce | carrierNested => cases hm

private theorem native_argument_readout
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (hsubst : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextSubstitution Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (hn : ∀ {Δ ls args out}, ¬ Step Δ (ProofShape.mkApps (.const c ls) args) out)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hc : env.constants c = some ci) (hw : ∀ l ∈ ls, l.WF univs)
    (hl : ls.length = ci.uvars)
    (HW : InstForallsC env univs Γ (ci.type.instL ls) args (.forallE A B))
    (hPi : env.HasType univs Γ (.forallE A B) (.sort u))
    (H : JointCheck Step Δ kind sa sb) (hm : kind = .compare false)
    (EΔ : proofEraseCtx Γ = Δ)
    (Ea : sa = .app (ProofShape.mkApps (.const c ls) as) x)
    (Eb : sb = .app (ProofShape.mkApps (.const c ls) bs) y)
    (RA : ScopedCompute Step Δ (ProofShape.mkApps (.const c ls) (args.map (proofErase Γ)))
      (ProofShape.mkApps (.const c ls) as))
    (RB : ScopedCompute Step Δ (ProofShape.mkApps (.const c ls) (args.map (proofErase Γ)))
      (ProofShape.mkApps (.const c ls) bs)) :
    JointCarrierGuard Step Δ (proofErase Γ A) x y := by
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
      (proofErase_computed_const_prefix_domain hstep hhead hsubst hn hΓ hc hw hl HW hPi RA R) HX
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
requires its supplied typed telescope walk. -/
theorem proofErase_joint_computed_native_argument_guard
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (hsubst : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextSubstitution Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (hn : ∀ {Δ ls args out}, ¬ Step Δ (ProofShape.mkApps (.const c ls) args) out)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hc : env.constants c = some ci) (hw : ∀ l ∈ ls, l.WF univs)
    (hl : ls.length = ci.uvars)
    (HW : InstForallsC env univs Γ (ci.type.instL ls) args (.forallE A B))
    (hPi : env.HasType univs Γ (.forallE A B) (.sort u))
    (RA : ScopedCompute Step (proofEraseCtx Γ)
      (ProofShape.mkApps (.const c ls) (args.map (proofErase Γ))) f)
    (RB : ScopedCompute Step (proofEraseCtx Γ)
      (ProofShape.mkApps (.const c ls) (args.map (proofErase Γ))) g)
    (H : JointCompare Step (proofEraseCtx Γ) false (.app f x) (.app g y)) :
    JointCarrierGuard Step (proofEraseCtx Γ) (proofErase Γ A) x y := by
  obtain ⟨as, rfl, _⟩ := RA.const_spine hn
  obtain ⟨bs, rfl, _⟩ := RB.const_spine hn
  exact native_argument_readout hstep hhead hsubst hn hΓ hc hw hl HW hPi H rfl rfl rfl rfl RA RB

/-- A fixed typed declaration prefix reads its final argument guard in inferred
comparison. This extends the Eq readout to arbitrary dependent declaration
telescopes whose head remains primitive-inert. -/
theorem proofErase_joint_native_argument_guard
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (hsubst : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextSubstitution Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (hn : ∀ {Δ ls args out}, ¬ Step Δ (ProofShape.mkApps (.const c ls) args) out)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hc : env.constants c = some ci) (hw : ∀ l ∈ ls, l.WF univs)
    (hl : ls.length = ci.uvars)
    (HW : InstForallsC env univs Γ (ci.type.instL ls) args (.forallE A B))
    (hPi : env.HasType univs Γ (.forallE A B) (.sort u))
    (H : JointCompare Step (proofEraseCtx Γ) false
      (.app (ProofShape.mkApps (.const c ls) (args.map (proofErase Γ))) x)
      (.app (ProofShape.mkApps (.const c ls) (args.map (proofErase Γ))) y)) :
    JointCarrierGuard Step (proofEraseCtx Γ) (proofErase Γ A) x y :=
  proofErase_joint_computed_native_argument_guard hstep hhead hsubst hn hΓ hc hw hl HW hPi .refl .refl H

/-- Core-stage comparison at a rigid declaration prefix reads the native
argument guard unconditionally. Its primitive assumptions follow from the
existing core substitution law and the exclusion of unfolding this constant. -/
theorem proofErase_joint_zero_native_argument_guard
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hr : env.Rigid c) (hD : ∀ levels rhs, ¬ D.unfolds c levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hc : env.constants c = some ci) (hw : ∀ l ∈ ls, l.WF univs)
    (hl : ls.length = ci.uvars)
    (HW : InstForallsC env univs Γ (ci.type.instL ls) args (.forallE A B))
    (hPi : env.HasType univs Γ (.forallE A B) (.sort u))
    (H : JointCompare (ErasedJointStage D 0) (proofEraseCtx Γ) false
      (.app (ProofShape.mkApps (.const c ls) (args.map (proofErase Γ))) x)
      (.app (ProofShape.mkApps (.const c ls) (args.map (proofErase Γ))) y)) :
    JointCarrierGuard (ErasedJointStage D 0) (proofEraseCtx Γ) (proofErase Γ A) x y := by
  apply proofErase_joint_native_argument_guard (erased_joint_stage_descent heq hs 0)
    (erased_joint_stage_head 0) ?_ ?_ hΓ hc hw hl HW hPi H
  · intro Δ Δ' a b τ H W
    exact erased_iota_primitive_subst H
  · intro Δ ls args out H
    exact erased_joint_stage_no_rigid heq hr hD 0 H (constHead_mkApps _ _)

/-- Certified comparison reads the same native argument guard at its own
relation, using its proved interpreted primitive substitution law. No global
proposition beta transport or semantic head adequacy is assumed. -/
theorem proofErase_certified_native_argument_guard
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hr : env.Rigid c) (hD : ∀ levels rhs, ¬ D.unfolds c levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hc : env.constants c = some ci) (hw : ∀ l ∈ ls, l.WF univs)
    (hl : ls.length = ci.uvars)
    (HW : InstForallsC env univs Γ (ci.type.instL ls) args (.forallE A B))
    (hPi : env.HasType univs Γ (.forallE A B) (.sort u))
    (H : JointCompare (ErasedBetaStableJoint D) (proofEraseCtx Γ) false
      (.app (ProofShape.mkApps (.const c ls) (args.map (proofErase Γ))) x)
      (.app (ProofShape.mkApps (.const c ls) (args.map (proofErase Γ))) y)) :
    JointCarrierGuard (ErasedBetaStableJoint D) (proofEraseCtx Γ) (proofErase Γ A) x y := by
  apply proofErase_joint_native_argument_guard (erased_beta_stable_joint_descent heq hs)
    erased_beta_stable_joint_head (erased_beta_stable_joint_subst heq hs) ?_ hΓ hc hw hl HW hPi H
  intro Δ ls args out H
  exact erased_joint_union_no_rigid heq hr hD
    (erased_beta_stable_joint_into_union H) (constHead_mkApps _ _)


/-- Missing declaration-type congruence for the dependent-field argument.
An actual comparison of two non-proof prefixes should compare their native
residual types after different typed argument substitutions. Source and Target
are separate because stage-preserving comparison closure is not assumed. This
property is not proved here and is not claimed to be a smaller sufficient
strengthening front. In its application case, a parameter guard must pass
through the dependent declaration codomain. -/
def JointNativePrefixTypeComparison
    (Source Target : List ProofShape → ProofShape → ProofShape → Prop) : Prop :=
  ∀ {Γ c ci ls args args' T U}, OnCtx Γ (env.IsType univs) →
    env.constants c = some ci → (∀ l ∈ ls, l.WF univs) → ls.length = ci.uvars →
    InstForallsC env univs Γ (ci.type.instL ls) args T →
    InstForallsC env univs Γ (ci.type.instL ls) args' U →
    ¬ IsProof Γ (VExpr.mkApps (.const c ls) args) →
    ¬ IsProof Γ (VExpr.mkApps (.const c ls) args') →
    JointCompare Source (proofEraseCtx Γ) false
      (proofErase Γ (VExpr.mkApps (.const c ls) args))
      (proofErase Γ (VExpr.mkApps (.const c ls) args')) →
    JointCompare Target (proofEraseCtx Γ) true (proofErase Γ T) (proofErase Γ U)

end Lean4Lean.VEnv.Strengthening
