import Lean4Lean.Theory.Typing.Strengthening.ProofErasureFutureFunctionDomain
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureFamilyInstantiation

/-! # Instantiating dependent future carrier recipes

Retaining the carrier in a future body certificate supports typed instantiation
and paired application at arguments with a certified computational join. The
dependent result carrier is pulled back along the left argument computation;
it need not be syntactically independent of the argument or beta fixed.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params]

/-- Typed instantiation transports the body's full future carrier certificate,
including the dependent carrier and all beta redexes created by substitution.
No recovery premise on the argument or primitive closure law is needed. -/
theorem proofErase_future_carrier_inst
    (hΓA : OnCtx (A :: Γ) (env.IsType univs)) (hx : env.HasType univs Γ x A)
    (hb : env.HasType univs (A :: Γ) b B) (hc : env.HasType univs (A :: Γ) c B)
    (H : BetaStableCarrier Step (proofEraseCtx (A :: Γ)) (proofErase (A :: Γ) B)
      (proofErase (A :: Γ) b) (proofErase (A :: Γ) c)) :
    BetaStableCarrier Step (proofEraseCtx Γ) (proofErase Γ (B.inst x))
      (proofErase Γ (b.inst x)) (proofErase Γ (c.inst x)) := by
  obtain ⟨u, hB⟩ := hb.isType henv hΓA
  have W := (Ctx.InstN.zero (Γ₀ := Γ) (e₀ := x) (A₀ := A)).substEq hΓA hx
  have HI := H.subst (ContextSubstitution.of_typed hΓA.1 W (erasedSubstAgreement_one hΓA hx))
  rw [proofErase_instN hΓA hx Ctx.InstN.zero hB,
    proofErase_instN hΓA hx Ctx.InstN.zero hb, proofErase_instN hΓA hx Ctx.InstN.zero hc]
  simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using HI

/-- A certified argument join instantiates a retained dependent carrier recipe
at two different arguments. The output uses the actual left result carrier;
its computation to the shared result carrier is pulled back explicitly. The
body endpoints themselves need not have a computational join. -/
theorem proofErase_future_carrier_inst_joined
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓA : OnCtx (A :: Γ) (env.IsType univs))
    (hb : env.HasType univs (A :: Γ) b B) (hc : env.HasType univs (A :: Γ) c B)
    (hx : env.HasType univs Γ x A) (hy : env.HasType univs Γ y A)
    (H : BetaStableCarrier (ErasedJointUnion D) (proofEraseCtx (A :: Γ))
      (proofErase (A :: Γ) B) (proofErase (A :: Γ) b) (proofErase (A :: Γ) c))
    (RX : ScopedCompute (ErasedBetaStableJoint D) (proofEraseCtx Γ) (proofErase Γ x) shared)
    (RY : ScopedCompute (ErasedBetaStableJoint D) (proofEraseCtx Γ) (proofErase Γ y) shared) :
    BetaStableCarrier (ErasedJointUnion D) (proofEraseCtx Γ) (proofErase Γ (B.inst x))
      (proofErase Γ (b.inst x)) (proofErase Γ (c.inst y)) := by
  obtain ⟨z, HZ, EZ⟩ := proofErase_scoped_compute_realize
    (erased_beta_stable_joint_descent heq hs) hΓA.1 hx rfl rfl RX
  have hz := HZ.hasType.2
  have HI := proofErase_future_carrier_inst hΓA hz hb hc H
  obtain ⟨u, hB⟩ := hb.isType henv hΓA
  have RB := proofErase_certified_compute_inst_argument heq hs hΓA hb hx RX
  have RC := proofErase_certified_compute_inst_argument heq hs hΓA hc hy RY
  have RT := proofErase_certified_compute_inst_argument heq hs hΓA hB hx RX
  rw [← EZ, ← proofErase_instN hΓA hz Ctx.InstN.zero hb] at RB
  rw [← EZ, ← proofErase_instN hΓA hz Ctx.InstN.zero hc] at RC
  rw [← EZ, ← proofErase_instN hΓA hz Ctx.InstN.zero hB] at RT
  have HC := HI.certified_prefixes heq hs hΓA.1
    (hb.instN henv Ctx.InstN.zero hx) (hc.instN henv Ctx.InstN.zero hy) RB RC
  exact HC.certified_carrier_prefix heq hs hΓA.1 (hB.instN henv Ctx.InstN.zero hx) RT

/-- Two displayed lambdas with retained future carrier bodies apply to
independently computed arguments with a certified join. The result keeps the
left dependent result type and all future paths. This assumes a body recipe;
it does not extract one from a whole-function certificate. -/
theorem proofErase_future_carrier_apply_lams_joined
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (hb : env.HasType univs (A :: Γ) b B) (hc : env.HasType univs (A :: Γ) c B)
    (hx : env.HasType univs Γ x A) (hy : env.HasType univs Γ y A)
    (H : BetaStableCarrier (ErasedJointUnion D) (proofEraseCtx (A :: Γ))
      (proofErase (A :: Γ) B) (proofErase (A :: Γ) b) (proofErase (A :: Γ) c))
    (RX : ScopedCompute (ErasedBetaStableJoint D) (proofEraseCtx Γ) (proofErase Γ x) shared)
    (RY : ScopedCompute (ErasedBetaStableJoint D) (proofEraseCtx Γ) (proofErase Γ y) shared) :
    BetaStableCarrier (ErasedJointUnion D) (proofEraseCtx Γ) (proofErase Γ (B.inst x))
      (proofErase Γ (.app (.lam A b) x)) (proofErase Γ (.app (.lam A c) y)) := by
  have ha := HasType.app (HasType.lam hA hb) hx
  have hd := HasType.app (HasType.lam hA hc) hy
  exact (proofErase_future_carrier_inst_joined heq hs ⟨hΓ, u, hA⟩ hb hc hx hy H RX RY).certified_prefixes
    heq hs hΓ ha hd (.beta (proofErase_beta_forward hΓ ha .beta))
    (.beta (proofErase_beta_forward hΓ hd .beta))

/-- Change a displayed lambda's domain by arbitrary actual type equality and
then apply both bodies at independently computed, joined arguments. The old
future body recipe is retained through context conversion before instantiation;
neither exact type recovery nor semantic head exposure is assumed. -/
theorem proofErase_future_carrier_apply_lams_defeq_domain
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (HE : env.IsDefEq univs Γ A A' (.sort u))
    (hb : env.HasType univs (A :: Γ) b B) (hc : env.HasType univs (A :: Γ) c B)
    (hx : env.HasType univs Γ x A') (hy : env.HasType univs Γ y A')
    (H : BetaStableCarrier (ErasedJointUnion D) (proofEraseCtx (A :: Γ))
      (proofErase (A :: Γ) B) (proofErase (A :: Γ) b) (proofErase (A :: Γ) c))
    (RX : ScopedCompute (ErasedBetaStableJoint D) (proofEraseCtx Γ) (proofErase Γ x) shared)
    (RY : ScopedCompute (ErasedBetaStableJoint D) (proofEraseCtx Γ) (proofErase Γ y) shared) :
    BetaStableCarrier (ErasedJointUnion D) (proofEraseCtx Γ) (proofErase Γ (B.inst x))
      (proofErase Γ (.app (.lam A' b) x)) (proofErase Γ (.app (.lam A' c) y)) := by
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, HE.hasType.1⟩
  have W : IsDefEqCtx env univs [] (A :: Γ) (A' :: Γ) := .succ (.refl hΓ) HE
  have HC := H.defeqCtx (by trivial) W
  rw [proofErase_defeqCtx hΓA W (hb.isType henv hΓA).choose_spec,
    proofErase_defeqCtx hΓA W hb, proofErase_defeqCtx hΓA W hc] at HC
  exact proofErase_future_carrier_apply_lams_joined heq hs hΓ HE.hasType.2
    (hb.defeqDFC henv W) (hc.defeqDFC henv W) hx hy HC RX RY

end Lean4Lean.VEnv.Strengthening
