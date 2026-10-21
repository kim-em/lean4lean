import Lean4Lean.Theory.Typing.Strengthening.ProofErasureNativeSupplyJoin
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCoreGuardAlignment

/-! # Application guards at computationally joined native domains

A literal typed declaration walk recovers its native residual exactly. For
ordinary-core argument joins, the two native residuals have a common reduct;
forward carrier transport then constructs a guard at the recovered common Pi.
All joint guard constructors, including nested dependent fields, are retained.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private native_walk_type
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureNativeSupplyJoin
open private forget_scope
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureCoreOracleReduction
variable [Params]

/-- A literal typed native walk supplies its exact erased residual. This is
stronger than a computation path when no input argument has been changed. -/
theorem proofErase_native_supply
    (hΓ : OnCtx Γ (env.IsType univs)) (hT : env.HasType univs Γ T (.sort u))
    (HW : InstForallsC env univs Γ T args residual) :
    ProofShape.supplyType (args.map (proofErase Γ)) (proofErase Γ T) =
      some (proofErase Γ residual) := by
  induction HW generalizing u with
  | nil => rfl
  | @cons a A args residual B ha _ ih =>
    obtain ⟨⟨v, hA⟩, _, hB⟩ := hT.forallE_inv henv
    have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, v, hA⟩
    rw [show proofErase Γ (.forallE A B) = .forallE _ _ from
      if_neg (not_isProof_of_sort hΓ hT)]
    simpa only [List.map_cons, ProofShape.supplyType,
      proofErase_instN hΓA ha Ctx.InstN.zero hB] using
      ih (hB.instN henv Ctx.InstN.zero ha)

private theorem native_walk_typing
    (hf : env.HasType univs Γ f T) (HW : InstForallsC env univs Γ T args residual) :
    env.HasType univs Γ (VExpr.mkApps f args) residual := by
  induction HW generalizing f with
  | nil => exact hf
  | cons ha _ ih => exact ih (hf.app ha)

/-- A non-proof constant prefix recovers its exact native residual, provided
its supplied arguments follow the literal declaration telescope. Arbitrary
semantic assignments to the prefix are not asserted recoverable. -/
theorem proofErase_const_native_recovery
    (hΓ : OnCtx Γ (env.IsType univs))
    (hc : env.constants c = some ci) (hw : ∀ l ∈ ls, l.WF univs)
    (hl : ls.length = ci.uvars)
    (HW : InstForallsC env univs Γ (ci.type.instL ls) args residual)
    (hn : ¬ IsProof Γ (VExpr.mkApps (.const c ls) args)) :
    ScopedTypeRecovery Step (proofEraseCtx Γ)
      (proofErase Γ (VExpr.mkApps (.const c ls) args)) (proofErase Γ residual) := by
  have hf : env.HasType univs [] (.const c ls) (ci.type.instL ls) := .const hc hw hl
  obtain ⟨_, hT⟩ := hf.isType henv (by trivial)
  have HS := proofErase_native_supply hΓ (hT.weak0 henv.ordered) HW
  rw [proofErase_closed_context ((henv.ordered.closedC hc).instL) hT hΓ] at HS
  rw [proofErase_const_spine hΓ (native_walk_typing (HasType.const hc hw hl) HW) hn]
  exact (ScopedTypeRecovery.const hc hw hl).supply HS

/-- Computationally joined declaration prefixes construct a recovered Pi for
the second prefix and transport any typed source argument guard to its domain.
The guard may use functions or nested dependent records. This is restricted
to the repaired ordinary core, whose forward carrier transport is proved. -/
theorem ErasedQuotCore.joined_native_prefix_guard
    (hq : QuotRegistered env) (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hc : env.constants c = some ci) (hw : ∀ l ∈ ls, l.WF univs)
    (hl : ls.length = ci.uvars)
    (HW : InstForallsC env univs Γ (ci.type.instL ls) args (.forallE A B))
    (HW' : InstForallsC env univs Γ (ci.type.instL ls) args' (.forallE A' B'))
    (hn : ¬ IsProof Γ (VExpr.mkApps (.const c ls) args'))
    (HA : List.Forall₂ (ScopedCompute (fun _ => Step hq) (proofEraseCtx Γ))
      (args.map (proofErase Γ)) sharedArgs)
    (HA' : List.Forall₂ (ScopedCompute (fun _ => Step hq) (proofEraseCtx Γ))
      (args'.map (proofErase Γ)) sharedArgs)
    (hx : env.HasType univs Γ x A) (hy : env.HasType univs Γ y A)
    (HX : JointCarrierGuard (fun _ => Step hq) (proofEraseCtx Γ)
      (proofErase Γ A) (proofErase Γ x) (proofErase Γ y)) :
    ∃ domain body, ScopedTypeRecovery (fun _ => Step hq) (proofEraseCtx Γ)
        (proofErase Γ (VExpr.mkApps (.const c ls) args')) (.forallE domain body) ∧
      ScopedCompute (fun _ => Step hq) (proofEraseCtx Γ) (proofErase Γ A) domain ∧
      ScopedCompute (fun _ => Step hq) (proofEraseCtx Γ) (proofErase Γ A') domain ∧
      JointCarrierGuard (fun _ => Step hq) (proofEraseCtx Γ)
        domain (proofErase Γ x) (proofErase Γ y) := by
  have hstep : ErasedScopedPrimitiveDescent (fun _ => Step hq) :=
    ErasedPrimitiveReplay.toDescent (sound hq) (erased_iota_replay (sound hq))
  have hhead : ∀ {Δ : List ProofShape} {a b}, (fun _ => Step hq) Δ a b → PrimitiveHead a :=
    fun H => erased_iota_primitive_head H
  have hsubst : ∀ {Δ Δ' a b τ}, (fun _ => Step hq) Δ a b → ContextSubstitution Δ Δ' τ →
      (fun _ => Step hq) Δ' (a.subst τ) (b.subst τ) := fun H _ => erased_iota_primitive_subst H
  have hf : env.HasType univs [] (.const c ls) (ci.type.instL ls) := .const hc hw hl
  obtain ⟨_, hT⟩ := hf.isType henv (by trivial)
  have hTΓ := hT.weak0 henv.ordered (Γ := Γ)
  obtain ⟨out, _, R, R'⟩ := proofErase_native_residuals_join hstep @hhead @hsubst hΓ hTΓ HW HW' HA HA'
  obtain ⟨_, hPi⟩ := native_walk_type hTΓ HW
  obtain ⟨_, hPi'⟩ := native_walk_type hTΓ HW'
  have RR := R
  have RR' := R'
  rw [show proofErase Γ (.forallE A B) = .forallE _ _ from
    if_neg (not_isProof_of_sort hΓ hPi)] at RR
  rw [show proofErase Γ (.forallE A' B') = .forallE _ _ from
    if_neg (not_isProof_of_sort hΓ hPi')] at RR'
  obtain ⟨domain, body, rfl, RD⟩ := RR.forallE_domain_inv @hhead
  obtain ⟨_, _, E, RD'⟩ := RR'.forallE_domain_inv @hhead
  cases E
  have RF := proofErase_const_native_recovery (Step := fun _ => Step hq) hΓ hc hw hl HW' hn
  exact ⟨domain, body, RF.convert R', RD, RD',
    carrier_compute_forward hq hcon hΓ hx hy HX (forget_scope RD)⟩

/-- The joined-prefix case closes the actual application-checking rule.
No recovered Pi, native type comparison, or converted argument guard is
assumed: all three are constructed from the typed declaration walks and joins. -/
theorem ErasedQuotCore.application_of_joined_native_prefixes
    (hq : QuotRegistered env) (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hc : env.constants c = some ci) (hw : ∀ l ∈ ls, l.WF univs)
    (hl : ls.length = ci.uvars)
    (HW : InstForallsC env univs Γ (ci.type.instL ls) args (.forallE A B))
    (HW' : InstForallsC env univs Γ (ci.type.instL ls) args' (.forallE A' B'))
    (hn : ¬ IsProof Γ (VExpr.mkApps (.const c ls) args'))
    (HA : List.Forall₂ (ScopedCompute (fun _ => Step hq) (proofEraseCtx Γ))
      (args.map (proofErase Γ)) sharedArgs)
    (HA' : List.Forall₂ (ScopedCompute (fun _ => Step hq) (proofEraseCtx Γ))
      (args'.map (proofErase Γ)) sharedArgs)
    (hx : env.HasType univs Γ x A) (hy : env.HasType univs Γ y A)
    (HX : JointCarrierGuard (fun _ => Step hq) (proofEraseCtx Γ)
      (proofErase Γ A) (proofErase Γ x) (proofErase Γ y))
    (HF : JointCompare (fun _ => Step hq) (proofEraseCtx Γ) false
      (proofErase Γ (VExpr.mkApps (.const c ls) args')) g) :
    JointCompare (fun _ => Step hq) (proofEraseCtx Γ) mode
      (.app (proofErase Γ (VExpr.mkApps (.const c ls) args')) (proofErase Γ x))
      (.app g (proofErase Γ y)) := by
  obtain ⟨_, _, RF, _, _, HG⟩ := joined_native_prefix_guard hq hcon hΓ hc hw hl HW HW' hn HA HA' hx hy HX
  exact .appCarrier RF HF HG

/-- A proposition-valued target prefix turns the constructed guard into an
actual comparison of two terms of literal type Prop. The argument typings at
the target domain are derived from the native domain join, not assumed. -/
theorem ErasedQuotCore.joined_native_propositions
    (hq : QuotRegistered env) (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hc : env.constants c = some ci) (hw : ∀ l ∈ ls, l.WF univs)
    (hl : ls.length = ci.uvars)
    (HW : InstForallsC env univs Γ (ci.type.instL ls) args (.forallE A B))
    (HW' : InstForallsC env univs Γ (ci.type.instL ls) args' (.forallE A' (.sort .zero)))
    (HA : List.Forall₂ (ScopedCompute (fun _ => Step hq) (proofEraseCtx Γ))
      (args.map (proofErase Γ)) sharedArgs)
    (HA' : List.Forall₂ (ScopedCompute (fun _ => Step hq) (proofEraseCtx Γ))
      (args'.map (proofErase Γ)) sharedArgs)
    (hx : env.HasType univs Γ x A) (hy : env.HasType univs Γ y A)
    (HX : JointCarrierGuard (fun _ => Step hq) (proofEraseCtx Γ)
      (proofErase Γ A) (proofErase Γ x) (proofErase Γ y)) :
    let f := VExpr.mkApps (.const c ls) args'
    env.HasType univs Γ (.app f x) (.sort .zero) ∧
      env.HasType univs Γ (.app f y) (.sort .zero) ∧
      JointCompare (fun _ => Step hq) (proofEraseCtx Γ) mode
        (proofErase Γ (.app f x)) (proofErase Γ (.app f y)) := by
  have hf := native_walk_typing (HasType.const hc hw hl) HW'
  have hn := not_isProof_function_to_sort hΓ hf
  obtain ⟨_, _, RF, RD, RD', HG⟩ := joined_native_prefix_guard hq hcon hΓ hc hw hl HW HW' hn HA HA' hx hy HX
  have hstep : ErasedScopedPrimitiveDescent (fun _ => Step hq) :=
    ErasedPrimitiveReplay.toDescent (sound hq) (erased_iota_replay (sound hq))
  obtain ⟨_, hPi⟩ := (native_walk_typing (HasType.const hc hw hl) HW).isType henv hΓ
  obtain ⟨⟨_, hA⟩, _, _⟩ := hPi.forallE_inv henv
  obtain ⟨_, hPi'⟩ := hf.isType henv hΓ
  obtain ⟨⟨_, hA'⟩, _, _⟩ := hPi'.forallE_inv henv
  have HC : JointCompare (fun _ => Step hq) (proofEraseCtx Γ) false
      (proofErase Γ A) (proofErase Γ A') := .compute RD RD' (.leaf .refl)
  have HE := (proofErase_joint_compare_reflect hstep hΓ hA hA' HC).2 rfl
    (not_isProof_of_sort hΓ hA) (not_isProof_of_sort hΓ hA')
  have hL := hf.app (hx.defeqU_r henv hΓ HE)
  have hR := hf.app (hy.defeqU_r henv hΓ HE)
  refine ⟨hL, hR, ?_⟩
  rw [show proofErase Γ (.app (VExpr.mkApps (.const c ls) args') x) = .app _ _ from
      if_neg (not_isProof_of_sort hΓ hL),
    show proofErase Γ (.app (VExpr.mkApps (.const c ls) args') y) = .app _ _ from
      if_neg (not_isProof_of_sort hΓ hR)]
  exact .appCarrier RF (.leaf .refl) HG

end Lean4Lean.VEnv.Strengthening
