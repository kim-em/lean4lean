import Lean4Lean.Theory.Typing.Strengthening.ProofErasureNativeSpineReadout

/-! # Native telescope supply through computationally joined arguments

Typed argument computations preserve successful raw telescope supply. Both
native residual types compute to the same raw output when their argument
lists compute pointwise to a common list. This constructs the missing
comparison for this explicit-join case, without general native congruence.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params]

/-- A successful literal raw telescope supply constructs recovery for its
whole application spine. It does not inspect or recover argument types. -/
theorem ProofShape.ScopedTypeRecovery.supply
    (R : ScopedTypeRecovery Step Δ f T)
    (HS : ProofShape.supplyType args T = some out) :
    ScopedTypeRecovery Step Δ (ProofShape.mkApps f args) out := by
  induction args generalizing f T with
  | nil => cases HS; exact R
  | cons a args ih =>
    cases T <;> try contradiction
    exact ih (.app R) HS

/-- Computed typed arguments still supply the native telescope, even when
its starting type has already computed. The native residual computes to the
literal raw supply result. This needs primitive substitution closure, but
neither semantic head exposure nor comparison/carrier conversion closure. -/
theorem proofErase_computed_native_supply
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (hsubst : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextSubstitution Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (hΓ : OnCtx Γ (env.IsType univs)) (hT : env.HasType univs Γ T (.sort u))
    (HW : InstForallsC env univs Γ T args residual)
    (RT : ScopedCompute Step (proofEraseCtx Γ) (proofErase Γ T) rawType)
    (HA : List.Forall₂ (ScopedCompute Step (proofEraseCtx Γ))
      (args.map (proofErase Γ)) rawArgs) :
    ∃ out, ProofShape.supplyType rawArgs rawType = some out ∧
      ScopedCompute Step (proofEraseCtx Γ) (proofErase Γ residual) out := by
  induction HW generalizing u rawType rawArgs with
  | nil => cases HA; exact ⟨_, rfl, RT⟩
  | @cons a A args residual B ha HW ih =>
    cases HA with
    | cons RA HA =>
      obtain ⟨⟨v, hA⟩, w, hB⟩ := hT.forallE_inv henv
      have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, v, hA⟩
      have RT' := RT
      rw [show proofErase Γ (.forallE A B) = .forallE _ _ from
        if_neg (not_isProof_of_sort hΓ hT)] at RT'
      obtain ⟨D, C, rfl, _⟩ := RT'.forallE_domain_inv hhead
      obtain ⟨a', Haa', Ea'⟩ := proofErase_scoped_compute_realize hstep hΓ ha rfl rfl RA
      have RB := proofErase_computed_pi_inst hstep hhead hsubst hΓ hA hB Haa'.hasType.2 RT
      rw [Ea'] at RB
      have RX := proofErase_scoped_compute_inst_argument hsubst hΓA hB ha RA
      rw [← Ea', ← proofErase_instN hΓA Haa'.hasType.2 Ctx.InstN.zero hB] at RX
      obtain ⟨out, HS, RO⟩ := ih (hB.instN henv Ctx.InstN.zero ha) (RX.trans RB) HA
      exact ⟨out, HS, RO⟩

/-- Two typed walks from the same native type have computationally joined
residual types when their argument erasures compute to a common list. The
shared residual is fixed by deterministic raw supply, not semantic equality. -/
theorem proofErase_native_residuals_join
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (hsubst : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextSubstitution Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (hΓ : OnCtx Γ (env.IsType univs)) (hT : env.HasType univs Γ T (.sort u))
    (HW : InstForallsC env univs Γ T args residual)
    (HW' : InstForallsC env univs Γ T args' residual')
    (HA : List.Forall₂ (ScopedCompute Step (proofEraseCtx Γ))
      (args.map (proofErase Γ)) sharedArgs)
    (HA' : List.Forall₂ (ScopedCompute Step (proofEraseCtx Γ))
      (args'.map (proofErase Γ)) sharedArgs) :
    ∃ out, ProofShape.supplyType sharedArgs (proofErase Γ T) = some out ∧
      ScopedCompute Step (proofEraseCtx Γ) (proofErase Γ residual) out ∧
      ScopedCompute Step (proofEraseCtx Γ) (proofErase Γ residual') out := by
  obtain ⟨out, HS, R⟩ := proofErase_computed_native_supply hstep hhead hsubst hΓ hT HW .refl HA
  obtain ⟨out', HS', R'⟩ := proofErase_computed_native_supply hstep hhead hsubst hΓ hT HW' .refl HA'
  cases Option.some.inj (HS.symm.trans HS')
  exact ⟨_, HS, R, R'⟩

/-- A raw constant spine with computed arguments and an actual native telescope
walk has an explicit recovered type. Its native residual computes to that type. No
independent recovery or exact-recovery premise on any argument is needed. -/
theorem proofErase_computed_const_prefix_recovery
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (hsubst : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextSubstitution Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (hΓ : OnCtx Γ (env.IsType univs))
    (hc : env.constants c = some ci) (hw : ∀ l ∈ ls, l.WF univs)
    (hl : ls.length = ci.uvars)
    (HW : InstForallsC env univs Γ (ci.type.instL ls) args residual)
    (HA : List.Forall₂ (ScopedCompute Step (proofEraseCtx Γ))
      (args.map (proofErase Γ)) rawArgs) :
    ∃ out, ScopedTypeRecovery Step (proofEraseCtx Γ)
        (ProofShape.mkApps (.const c ls) rawArgs) out ∧
      ScopedCompute Step (proofEraseCtx Γ) (proofErase Γ residual) out := by
  have hf : env.HasType univs [] (.const c ls) (ci.type.instL ls) := .const hc hw hl
  obtain ⟨u, hT⟩ := hf.isType henv (by trivial)
  have ET := proofErase_closed_context ((henv.ordered.closedC hc).instL) hT hΓ
  obtain ⟨out, HS, R⟩ := proofErase_computed_native_supply hstep hhead hsubst hΓ
    (hT.weak0 henv.ordered) HW .refl HA
  rw [ET] at HS
  exact ⟨out, (ScopedTypeRecovery.const hc hw hl).supply HS, R⟩

/-- The explicitly joined-argument case of native declaration-type congruence
is constructive at the original relation. It provides both computations and
an actual comparison, without any assumed prefix-comparison closure law. -/
theorem proofErase_joined_const_native_types
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (hsubst : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextSubstitution Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (hΓ : OnCtx Γ (env.IsType univs))
    (hc : env.constants c = some ci) (hw : ∀ l ∈ ls, l.WF univs)
    (hl : ls.length = ci.uvars)
    (HW : InstForallsC env univs Γ (ci.type.instL ls) args T)
    (HW' : InstForallsC env univs Γ (ci.type.instL ls) args' U)
    (HA : List.Forall₂ (ScopedCompute Step (proofEraseCtx Γ))
      (args.map (proofErase Γ)) sharedArgs)
    (HA' : List.Forall₂ (ScopedCompute Step (proofEraseCtx Γ))
      (args'.map (proofErase Γ)) sharedArgs) :
    ∃ out, ScopedTypeRecovery Step (proofEraseCtx Γ)
        (ProofShape.mkApps (.const c ls) sharedArgs) out ∧
      ScopedCompute Step (proofEraseCtx Γ) (proofErase Γ T) out ∧
      ScopedCompute Step (proofEraseCtx Γ) (proofErase Γ U) out ∧
      JointCompare Step (proofEraseCtx Γ) mode (proofErase Γ T) (proofErase Γ U) := by
  have hf : env.HasType univs [] (.const c ls) (ci.type.instL ls) := .const hc hw hl
  obtain ⟨_, hT⟩ := hf.isType henv (by trivial)
  obtain ⟨out, HS, R, R'⟩ := proofErase_native_residuals_join hstep hhead hsubst hΓ
    (hT.weak0 henv.ordered) HW HW' HA HA'
  rw [proofErase_closed_context ((henv.ordered.closedC hc).instL) hT hΓ] at HS
  exact ⟨out, (ScopedTypeRecovery.const hc hw hl).supply HS, R, R', .compute R R' (.leaf .refl)⟩

private theorem native_walk_type
    (hT : env.HasType univs Γ T (.sort u))
    (HW : InstForallsC env univs Γ T args residual) :
    env.IsType univs Γ residual := by
  induction HW generalizing u with
  | nil => exact ⟨_, hT⟩
  | cons ha _ ih =>
    obtain ⟨_, _, hB⟩ := hT.forallE_inv henv
    exact ih (hB.instN henv Ctx.InstN.zero ha)

/-- Joined telescope prefixes produce a computational join of their next
native domains. For a constructor telescope this is the next dependent field
carrier, including all substitutions of earlier parameters and fields. The
conclusion retains both directed paths; it does not invert carrier computation. -/
theorem proofErase_joined_native_domains
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (hsubst : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextSubstitution Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (hΓ : OnCtx Γ (env.IsType univs)) (hT : env.HasType univs Γ T (.sort u))
    (HW : InstForallsC env univs Γ T args (.forallE A B))
    (HW' : InstForallsC env univs Γ T args' (.forallE A' B'))
    (HA : List.Forall₂ (ScopedCompute Step (proofEraseCtx Γ))
      (args.map (proofErase Γ)) sharedArgs)
    (HA' : List.Forall₂ (ScopedCompute Step (proofEraseCtx Γ))
      (args'.map (proofErase Γ)) sharedArgs) :
    ∃ domain, ScopedCompute Step (proofEraseCtx Γ) (proofErase Γ A) domain ∧
      ScopedCompute Step (proofEraseCtx Γ) (proofErase Γ A') domain ∧
      JointCompare Step (proofEraseCtx Γ) mode (proofErase Γ A) (proofErase Γ A') := by
  obtain ⟨_, _, R, R'⟩ := proofErase_native_residuals_join hstep hhead hsubst hΓ hT HW HW' HA HA'
  obtain ⟨_, hPi⟩ := native_walk_type hT HW
  obtain ⟨_, hPi'⟩ := native_walk_type hT HW'
  rw [show proofErase Γ (.forallE A B) = .forallE _ _ from
    if_neg (not_isProof_of_sort hΓ hPi)] at R
  rw [show proofErase Γ (.forallE A' B') = .forallE _ _ from
    if_neg (not_isProof_of_sort hΓ hPi')] at R'
  obtain ⟨D, C, rfl, RD⟩ := R.forallE_domain_inv hhead
  obtain ⟨_, _, E, RD'⟩ := R'.forallE_domain_inv hhead
  cases E
  exact ⟨D, RD, RD', .compute RD RD' (.leaf .refl)⟩

/-- Certified joint computations discharge primitive descent, head shape,
and substitution closure. Explicitly joined arguments therefore yield native
type comparison within that same certified relation, without head adequacy. -/
theorem proofErase_certified_joined_native_types
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hT : env.HasType univs Γ T (.sort u))
    (HW : InstForallsC env univs Γ T args residual)
    (HW' : InstForallsC env univs Γ T args' residual')
    (HA : List.Forall₂ (ScopedCompute (ErasedBetaStableJoint D) (proofEraseCtx Γ))
      (args.map (proofErase Γ)) sharedArgs)
    (HA' : List.Forall₂ (ScopedCompute (ErasedBetaStableJoint D) (proofEraseCtx Γ))
      (args'.map (proofErase Γ)) sharedArgs) :
    JointCompare (ErasedBetaStableJoint D) (proofEraseCtx Γ) mode
      (proofErase Γ residual) (proofErase Γ residual') := by
  obtain ⟨_, _, R, R'⟩ := proofErase_native_residuals_join
    (erased_beta_stable_joint_descent heq hs) erased_beta_stable_joint_head
    (erased_beta_stable_joint_subst heq hs) hΓ hT HW HW' HA HA'
  exact .compute R R' (.leaf .refl)

end Lean4Lean.VEnv.Strengthening
