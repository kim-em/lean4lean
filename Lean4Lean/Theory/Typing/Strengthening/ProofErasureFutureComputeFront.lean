import Lean4Lean.Theory.Typing.Strengthening.ProofErasureFutureDeltaBoundary

/-! # Forward future carrier computation still contains the proposition front

Retaining carriers repairs the literal unit example, but a freely converted
supplied carrier can hide that unit behind an Eq probe. Even a base output
guard after certified endpoint computation must then expose the probe. The
input certificates need no primitives and the paths only unfold an identity.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private carrier_exposure_ne_eqRec
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypePathUnitFront
variable [Params]

/-- Missing forward endpoint-computation law for future carrier certificates
at an actual common supplied type. The input uses no primitives, the paths
are certified, and only a base guard in the full union is requested. This law
is not established or claimed strictly smaller than PropositionFront. -/
def TypedFutureCarrierForwardCompute (D : PureObservation.Definitions) : Prop :=
  ∀ {Γ a b A a' b'}, OnCtx Γ (env.IsType univs) →
    env.HasType univs Γ a A → env.HasType univs Γ b A →
    BetaStableCarrier (fun _ _ _ => False) (proofEraseCtx Γ)
      (proofErase Γ A) (proofErase Γ a) (proofErase Γ b) →
    ScopedCompute (ErasedBetaStableJoint D) (proofEraseCtx Γ) (proofErase Γ a) a' →
    ScopedCompute (ErasedBetaStableJoint D) (proofEraseCtx Γ) (proofErase Γ b) b' →
    JointCarrierGuard (ErasedJointUnion D) (proofEraseCtx Γ) (proofErase Γ A) a' b'

/-- Forward endpoint computation at a converted supplied carrier descends a
hidden proposition equation. The source endpoints are applications of a
declared unit identity; the paths are its delta and beta computations. No
arbitrary carrier computation or composition is needed for this implication. -/
theorem TypedFutureCarrierForwardCompute.unit_probe_descend
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (hEq : ∀ levels rhs, ¬ D.unfolds ``Eq levels rhs)
    (hRec : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (Hcompute : TypedFutureCarrierForwardCompute D)
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hf : info.numFields = 0)
    (hc : env.constants c = some ⟨0, .forallE (.const family []) (.const family [])⟩)
    (hd : D.unfolds c [] (.lam (.const family []) (.bvar 0)))
    (hS : env.HasType univs [] (.const family []) (.sort (.succ u)))
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.LiftN n 0 Γ Γ')
    (hP : env.HasType univs Γ P (.sort .zero))
    (hQ : env.HasType univs Γ Q (.sort .zero))
    (hq : env.HasType univs Γ' q (eqApp (.succ .zero) (.sort .zero) (P.liftN n) (Q.liftN n)))
    (hiT : env.HasType univs Γ' (.bvar i) (.const family []))
    (hjT : env.HasType univs Γ' (.bvar j) (.const family [])) (hne : i ≠ j)
    (HPQ : env.IsDefEqU univs Γ' (P.liftN n) (Q.liftN n)) :
    env.IsDefEqU univs Γ P Q := by
  have hSw : env.HasType univs Γ' (.const family []) (.sort (.succ u)) :=
    hS.weak0 henv.ordered
  have HE := eqTypeProbe_defeq heq hΓ' hSw (hP.weakN henv W) (hQ.weakN henv W) hq HPQ
  obtain ⟨a, b, ha, hb, HC, RA, RB, _, _⟩ :=
    unit_constant_future_compute_failure hi hp hx hf hc hd hS hΓ' hiT hjT hne
  have HG := Hcompute hΓ' (HE.symm.defeq ha) (HE.symm.defeq hb) HC.carrier RA RB
  rcases HG.checked_or_exposed with Hcmp | ⟨B, R, HB, _⟩
  · exact (hne (Hcmp.bvar_injective erased_joint_union_head)).elim
  exact proofErase_joint_union_type_probe_head_descend heq hs hregistry hEq hRec
    hΓ hΓ' W (hS.weak0 henv.ordered) hP hQ hq R (carrier_exposure_ne_eqRec heq HB)

/-- Even source-False future carrier transport to base union checking after
certified endpoint computation implies PropositionFront, given a closed
positive unit and its declared identity unfolding. This is a conditional
strength result, not a proof of the transport law or a strictness claim. -/
theorem TypedFutureCarrierForwardCompute.propositionFront_of_closed_unit
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (hEq : ∀ levels rhs, ¬ D.unfolds ``Eq levels rhs)
    (hRec : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (Hcompute : TypedFutureCarrierForwardCompute D)
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hf : info.numFields = 0)
    (hc : env.constants c = some ⟨0, .forallE (.const family []) (.const family [])⟩)
    (hd : D.unfolds c [] (.lam (.const family []) (.bvar 0)))
    (hS : env.HasType univs [] (.const family []) (.sort (.succ u))) :
    PropositionFront := by
  intro Γ A P Q hΓ hA hP hQ HPQ
  let S := VExpr.const family []
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, hA⟩
  have hSA : env.HasType univs (A :: Γ) S (.sort (.succ u)) := hS.weak0 henv.ordered
  have hΓS : OnCtx (S :: A :: Γ) (env.IsType univs) := ⟨hΓA, _, hSA⟩
  have hΓSS : OnCtx (S :: S :: A :: Γ) (env.IsType univs) := ⟨hΓS, _, hSA.weak henv⟩
  have W3 : Ctx.LiftN 3 0 Γ (S :: S :: A :: Γ) := Ctx.LiftN.one.cons0.cons0
  have hP3 : env.HasType univs (S :: S :: A :: Γ) (P.liftN 3) (.sort .zero) := hP.weakN henv W3
  have hQ3 : env.HasType univs (S :: S :: A :: Γ) (Q.liftN 3) (.sort .zero) := hQ.weakN henv W3
  let E := eqApp (.succ .zero) (.sort .zero) (P.liftN 3) (Q.liftN 3)
  have hE : env.HasType univs (S :: S :: A :: Γ) E (.sort .zero) :=
    HasType.eqApp heq (by trivial) (HasType.sort (by trivial)) hP3 hQ3
  have hΓE : OnCtx (E :: S :: S :: A :: Γ) (env.IsType univs) := ⟨hΓSS, _, hE⟩
  have W4 : Ctx.LiftN 4 0 Γ (E :: S :: S :: A :: Γ) := W3.cons0
  have hq : env.HasType univs (E :: S :: S :: A :: Γ) (.bvar 0)
      (eqApp (.succ .zero) (.sort .zero) (P.liftN 4) (Q.liftN 4)) := by
    have h := HasType.bvar (env := env) (U := univs) (Lookup.zero (ty := E) (Γ := S :: S :: A :: Γ))
    simpa only [E, eqApp, VExpr.lift, VExpr.liftN, VExpr.liftN_liftN] using h
  have hiT : env.HasType univs (E :: S :: S :: A :: Γ) (.bvar 1) S := .bvar (.succ .zero)
  have hjT : env.HasType univs (E :: S :: S :: A :: Γ) (.bvar 2) S := .bvar (.succ (.succ .zero))
  have HPQ4 : env.IsDefEqU univs (E :: S :: S :: A :: Γ) (P.liftN 4) (Q.liftN 4) := by
    obtain ⟨T, HT⟩ := HPQ
    have WX : Ctx.LiftN 3 0 (A :: Γ) (E :: S :: S :: A :: Γ) := Ctx.LiftN.one.cons0.cons0
    have H := HT.weakN henv WX
    exact ⟨_, by simpa only [VExpr.lift, VExpr.liftN_liftN] using H⟩
  exact Hcompute.unit_probe_descend heq hs hregistry hEq hRec hi hp hx hf hc hd hS
    hΓ hΓE W4 hP hQ hq hiT hjT (by decide) HPQ4

end Lean4Lean.VEnv.Strengthening
