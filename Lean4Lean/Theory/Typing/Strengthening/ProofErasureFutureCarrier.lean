import Lean4Lean.Theory.Typing.Strengthening.ProofErasureFamilyBinders
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointDependentCarrierBeta

/-! # Future certificates retaining the carrier

The carrier and both endpoints may beta-reduce independently, before or after
any interpreted substitution. These are certificates for particular inputs;
composition of arbitrary typed certificates is not assumed.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private beta_forallE_parts
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierDomainJoin
open private context_identity
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureFamilyBinders
variable [Params]

/-- Carrier-sensitive comparison at every future carrier/endpoint beta
residual and every interpreted context substitution. The first component
also covers raw contexts without a chosen typed realization. -/
def BetaStableCarrier (Step : List ProofShape → ProofShape → ProofShape → Prop)
    (Δ : List ProofShape) (A a b : ProofShape) : Prop :=
  JointCarrierTypeBetaResidual Step Δ A a b ∧
  ∀ {Δ' τ A' p q}, ContextSubstitution Δ Δ' τ →
    ProofShape.BetaRed (A.subst τ) A' →
    ProofShape.BetaRed (a.subst τ) p → ProofShape.BetaRed (b.subst τ) q →
    JointCarrierGuard Step Δ' A' p q

/-- Forget the retained future paths. -/
theorem BetaStableCarrier.base (H : BetaStableCarrier Step Δ A a b) :
    JointCarrierGuard Step Δ A a b := H.1 .refl .refl .refl

/-- Independent carrier and endpoint beta paths preserve the full certificate. -/
theorem BetaStableCarrier.beta (H : BetaStableCarrier Step Δ A a b)
    (RC : ProofShape.BetaRed A A') (RA : ProofShape.BetaRed a a')
    (RB : ProofShape.BetaRed b b') : BetaStableCarrier Step Δ A' a' b' := by
  refine ⟨fun PC PA PB => H.1 (RC.trans PC) (RA.trans PA) (RB.trans PB), ?_⟩
  intro Δ' τ C p q W PC PA PB
  exact H.2 W (RC.subst.trans PC) (RA.subst.trans PA) (RB.subst.trans PB)

/-- Compose interpreted substitutions to retain all later beta paths. -/
theorem BetaStableCarrier.subst (H : BetaStableCarrier Step Δ A a b)
    (W : ContextSubstitution Δ Δ' τ) :
    BetaStableCarrier Step Δ' (A.subst τ) (a.subst τ) (b.subst τ) := by
  refine ⟨fun PC PA PB => H.2 W PC PA PB, ?_⟩
  intro Δ'' υ C p q V PC PA PB
  rw [ProofShape.subst_subst] at PC PA PB
  exact H.2 (W.comp V) PC PA PB

/-- Common certificates embed at every supplied carrier, including its future
residuals. The carrierChecked constructor does not inspect the carrier. -/
theorem BetaStableFamily.carrier
    (H : BetaStableFamily (fun Δ => JointCompare Step Δ true) Δ a b) :
    BetaStableCarrier Step Δ A a b :=
  ⟨fun _ RA RB => .carrierChecked (H.1 RA RB),
    fun W _ RA RB => .carrierChecked (H.2 W RA RB)⟩

/-- Subsingleton carriers remain subsingleton after substitution and beta.
In particular the two distinct unit variables now have a future certificate. -/
theorem BetaStableCarrier.subsingleton (H : SubsingletonCarrier A) :
    BetaStableCarrier Step Δ A a b :=
  ⟨JointCarrierTypeBetaResidual.subsingleton H, fun _ RC _ _ => .carrierSubsingleton ((H.subst _).beta RC)⟩

/-- Symmetry exchanges the endpoint paths and keeps the carrier. -/
theorem BetaStableCarrier.symm (H : BetaStableCarrier Step Δ A a b) :
    BetaStableCarrier Step Δ A b a :=
  ⟨JointCarrierTypeBetaResidual.symm H.1, fun W RC RA RB => .carrierSymm (H.2 W RC RB RA)⟩

/-- At a literal sort, carrier certificates are exactly common certificates.
No carrier synthesis or general beta-transport assumption enters this decoder. -/
theorem BetaStableCarrier.sort_iff
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a) :
    BetaStableCarrier Step Δ (.sort u) a b ↔
      BetaStableFamily (fun Δ => JointCompare Step Δ true) Δ a b := by
  refine ⟨fun H => ⟨fun RA RB => ?_, fun W RA RB => ?_⟩, fun H => H.carrier⟩
  · exact (H.1 .refl RA RB).sort_checked hhead
  · exact (H.2 W .refl RA RB).sort_checked hhead

private theorem function_future (S : DomainSort Δ A u)
    (H : BetaStableCarrier Step (A :: Δ) B
      (.app (a.liftN 1) (etaArgument u)) (.app (b.liftN 1) (etaArgument u)))
    (RC : ProofShape.BetaRed (.forallE A B) C)
    (RA : ProofShape.BetaRed a p) (RB : ProofShape.BetaRed b q) :
    JointCarrierGuard Step Δ C p q := by
  obtain ⟨A', B', rfl, RD, RT⟩ := beta_forallE_parts RC
  have W : ContextSubstitution (A :: Δ) (A' :: Δ) ProofShape.Subst.id :=
    context_identity.cons_beta RD
  have HC := ((H.beta RT (.app RA.liftN .refl) (.app RB.liftN .refl)).subst W).base
  simp only [ProofShape.subst_id] at HC
  exact .carrierFunction (S.beta RD) HC

/-- A function carrier retains its recursive certificate beneath the residual
domain, including when future substitution creates new carrier/body redexes. -/
theorem BetaStableCarrier.function (S : DomainSort Δ A u)
    (H : BetaStableCarrier Step (A :: Δ) B
      (.app (a.liftN 1) (etaArgument u)) (.app (b.liftN 1) (etaArgument u))) :
    BetaStableCarrier Step Δ (.forallE A B) a b := by
  refine ⟨fun RC RA RB => function_future S H RC RA RB, ?_⟩
  intro Δ' τ C p q W RC RA RB
  have HC := H.subst W.cons
  simp only [ProofShape.subst, ProofShape.lift_subst_lift, etaArgument_subst] at HC
  exact function_future (W.sort S) HC RC RA RB

end Lean4Lean.VEnv.Strengthening
