import Lean4Lean.Theory.Typing.Strengthening.ProofErasureSemanticBoxReadout

/-! # A constructive fragment of semantic carrier conversion

Sorts and closed rigid carrier constants are closed under the registered Box
construction. Arbitrary guards at actually equal source types read into every
target in this finite grammar, including all future substitutions and beta
paths. The grammar is not asserted to cover arbitrary original types.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private BoxCarrierAlignment.family_typed
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointBoxAlignment
variable [Params]

/-- Finite nested Box targets over sorts and closed rigid constants.
Actual sort typing is checked separately, including each Box parameter's Type
level. This is a sufficient target fragment, not an irreducible strengthening
obligation or a completeness assertion. -/
inductive ClosedBoxCarrier : VExpr → Prop where
  | sort (v : VLevel) : ClosedBoxCarrier (.sort v)
  | rigid (hr : env.Rigid family) : ClosedBoxCarrier (.const family [])
  | box (hi : env.projections family info) (hp : info.nparams = 1) (hf : info.numFields = 1)
      (hz : info.nindices = 0) (hadm : (info.resultLevel.inst []).IsNeverZero)
      (hshape : info.ctorType.instL [] = .forallE (.sort (.succ .zero))
        (.forallE (.bvar 0) (.app (.const family []) (.bvar 1))))
      (hc : env.constants family = some ⟨0, .forallE (.sort (.succ .zero)) (.sort (.succ .zero))⟩)
      (H : ClosedBoxCarrier C) : ClosedBoxCarrier (.app (.const family []) C)

/-- Targets in this fragment contain no context variables. -/
theorem ClosedBoxCarrier.subst (H : ClosedBoxCarrier C) (σ : VExpr.Subst) : C.subst σ = C := by
  induction H with
  | sort | rigid => rfl
  | box _ _ _ _ _ _ _ _ ih => simp only [VExpr.subst, ih]

private theorem box_parameter_typed
    (hc : env.constants family = some ⟨0, .forallE (.sort (.succ .zero)) (.sort (.succ .zero))⟩)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hC : env.HasType univs Γ (.app (.const family []) C) (.sort u)) :
    env.HasType univs Γ C (.sort (.succ .zero)) := by
  obtain ⟨_, _, hfn, hC⟩ := hC.app_inv henv hΓ
  exact argument_at_displayed_domain hΓ hfn (BoxCarrierAlignment.family_typed hc) hC

/-- Every typed target in the fragment has semantic readout, at arbitrary
nesting depth. The source carrier and its computation prefixes are unrestricted. -/
theorem ClosedBoxCarrier.readout (H : ClosedBoxCarrier C)
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hΓ : OnCtx Γ (env.IsType univs)) (hC : env.HasType univs Γ C (.sort u)) :
    CarrierReadoutAt Step Γ C := by
  induction H generalizing Γ u with
  | sort => exact CarrierReadoutAt.sort hstep hΓ
  | rigid hr => exact CarrierReadoutAt.closed hstep hr hΓ hC
  | box hi hp hf hz hadm hshape hc H ih =>
    have hParam := box_parameter_typed hc hΓ hC
    intro A v a b hA HE HG
    exact CarrierReadoutAt.box hstep hi hp hf hz hadm hshape hc hΓ hParam
      (fun {_ _ _ _} => ih hΓ hParam) hA HE HG

omit [Params] in
private theorem sort_beta_fixed (R : ProofShape.BetaRed (.sort v) out) : out = .sort v := by
  have aux {a b} (H : ProofShape.BetaRed a b) : ∀ v, a = .sort v → b = .sort v := by
    induction H with
    | refl => exact fun _ E => E
    | trans _ _ ihR ihS => exact fun v E => ihS v (ihR v E)
    | app | lam | forallE | proj | beta => intro v E; cases E
  exact aux R v rfl

/-- Erasure of a typed fragment target admits no nontrivial beta reduction. -/
theorem ClosedBoxCarrier.beta_fixed (H : ClosedBoxCarrier C)
    (hΓ : OnCtx Γ (env.IsType univs)) (hC : env.HasType univs Γ C (.sort u))
    (R : ProofShape.BetaRed (proofErase Γ C) out) : out = proofErase Γ C := by
  induction H generalizing Γ u out with
  | sort =>
    rw [show proofErase Γ (.sort _) = .sort _ from if_neg (not_isProof_of_sort hΓ hC)] at R ⊢
    exact sort_beta_fixed R
  | rigid hr =>
    rw [show proofErase Γ (.const _ []) = .const _ [] from if_neg (not_isProof_of_sort hΓ hC)] at R ⊢
    have RR : ProofShape.BetaRed (ProofShape.mkApps (.const _ []) []) out := R
    obtain ⟨ps', rfl, HP⟩ := RR.const_spine
    cases HP
    rfl
  | box hi hp hf hz hadm hshape hc H ih =>
    have hParam := box_parameter_typed hc hΓ hC
    have hfn := BoxCarrierAlignment.family_typed (Γ := Γ) hc
    rw [show proofErase Γ (.app (.const _ []) _) = .app _ _ from
      if_neg (not_isProof_of_sort hΓ hC),
      show proofErase Γ (.const _ []) = .const _ [] from
        if_neg (not_isProof_function_to_sort hΓ hfn)] at R ⊢
    have RR : ProofShape.BetaRed (ProofShape.mkApps (.const _ []) [proofErase Γ _]) out := R
    obtain ⟨ps', rfl, HP⟩ := RR.const_spine
    cases HP with
    | cons RP Hnil =>
      cases Hnil
      rw [ih hΓ hParam RP]
      rfl

/-- Arbitrary full future guards transport into any typed fragment target
using ordinary actual type equality alone. The proof retains all future
endpoint paths and realizes each interpreted substitution, where the same
closed target grammar and its local readout theorem remain available. -/
theorem ClosedBoxCarrier.future_readout (HC : ClosedBoxCarrier C)
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hΓ : OnCtx Γ (env.IsType univs)) (HE : env.IsDefEq univs Γ A C (.sort u))
    (H : BetaStableCarrier Step (proofEraseCtx Γ) (proofErase Γ A) a b) :
    BetaStableCarrier Step (proofEraseCtx Γ) (proofErase Γ C) a b := by
  constructor
  · intro C' p q RC RP RQ
    rw [HC.beta_fixed hΓ HE.hasType.2 RC]
    exact HC.readout hstep hΓ HE.hasType.2 HE.hasType.1 HE.toU (H.1 .refl RP RQ)
  · intro Δ' τ C' p q W RC RP RQ
    have HG := H.2 W .refl RP RQ
    obtain ⟨Γ₀, σ, hΓ₀, EΓ₀, WS, ES⟩ := W hΓ rfl
    have HE' := HE.subst henv WS
    rw [HC.subst σ] at HE'
    rw [← proofErase_subst_with hΓ₀ WS HE.hasType.1 ES, ← EΓ₀] at HG
    rw [← proofErase_subst_with hΓ₀ WS HE.hasType.2 ES, HC.subst σ] at RC
    rw [← EΓ₀, HC.beta_fixed hΓ₀ HE'.hasType.2 RC]
    exact HC.readout hstep hΓ₀ HE'.hasType.2 HE'.hasType.1 HE'.toU HG

/-- A recovered native domain in the fragment accepts a guard at the
function's ordinarily assigned argument type. Typed recovery and uniqueness
supply actual domain equality, so no separate type-comparison certificate is
required. Existence of the displayed recovery remains an explicit input. -/
theorem ClosedBoxCarrier.application (HC : ClosedBoxCarrier C)
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hΓ : OnCtx Γ (env.IsType univs)) (hC : env.HasType univs Γ C (.sort v))
    (hf : env.HasType univs Γ f (.forallE A B))
    (R : ScopedTypeRecovery Step (proofEraseCtx Γ) (proofErase Γ f)
      (.forallE (proofErase Γ C) rawBody))
    (HG : JointCarrierGuard Step (proofEraseCtx Γ) (proofErase Γ A) a b)
    (HF : JointCompare Step (proofEraseCtx Γ) false (proofErase Γ f) g) :
    JointCompare Step (proofEraseCtx Γ) mode (.app (proofErase Γ f) a) (.app g b) := by
  obtain ⟨D, E, hfDE, ED, _⟩ := proofErase_scoped_recovered_pi_descend hstep hΓ hΓ
    (show Ctx.LiftN 0 0 Γ Γ from .zero []) hf
    (by simpa only [ProofShape.liftN_zero] using R)
  simp only [ProofShape.liftN_zero] at ED
  obtain ⟨_, hPi⟩ := hf.isType henv hΓ
  obtain ⟨⟨_, hA⟩, _, _⟩ := hPi.forallE_inv henv
  obtain ⟨_, hPi'⟩ := hfDE.isType henv hΓ
  obtain ⟨⟨_, hD⟩, _, _⟩ := hPi'.forallE_inv henv
  have HD : JointCompare Step (proofEraseCtx Γ) false (proofErase Γ D) (proofErase Γ C) := by
    rw [ED]
    exact .leaf .refl
  have HDC := (proofErase_joint_compare_reflect hstep hΓ hD hC HD).2 rfl
    (not_isProof_of_sort hΓ hD) (not_isProof_of_sort hΓ hC)
  obtain ⟨HAD, _⟩ := (hf.uniqU henv hΓ hfDE).forallE_inv henv hΓ
  have HAC := (show env.IsDefEqU univs Γ A D from ⟨_, HAD.choose_spec⟩).trans henv hΓ HDC
  exact .appCarrier R HF (HC.readout hstep hΓ hC hA HAC HG)

end Lean4Lean.VEnv.Strengthening
