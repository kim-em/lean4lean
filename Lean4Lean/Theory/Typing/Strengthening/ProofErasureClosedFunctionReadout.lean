import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRigidContext

/-! # Carrier readout at functions with a closed rigid domain

The codomain belongs to the closed Box fragment. A supplied function body
guard is transported through the equal binder context, then read at the target
codomain. This uses typed ordinary guards, not inversion of future certificates.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private erase_forallE_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
open private beta_forallE_parts from Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierDomainJoin
open private domain_sort_raw from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointTransport
variable [Params]

private theorem function_body_readout
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (hsubst : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextSubstitution Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (hr : env.Rigid family) (HC : ClosedBoxCarrier C)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hD : env.HasType univs Γ D (.sort u))
    (ha : env.HasType univs Γ a (.forallE D B))
    (hb : env.HasType univs Γ b (.forallE D B))
    (HE : env.IsDefEqU univs Γ (.forallE D B) (.forallE (.const family []) C))
    (HG : JointCarrierGuard Step (proofEraseCtx (D :: Γ)) (proofErase (D :: Γ) B)
      (.app ((proofErase Γ a).liftN 1) (etaArgument u))
      (.app ((proofErase Γ b).liftN 1) (etaArgument u))) :
    JointCarrierGuard Step (proofEraseCtx Γ) (proofErase Γ (.forallE (.const family []) C))
      (proofErase Γ a) (proofErase Γ b) := by
  obtain ⟨_, hPi⟩ := ha.isType henv hΓ
  obtain ⟨⟨_, HD⟩, ⟨_, HB⟩⟩ := HE.forallE_inv henv hΓ
  have HD := HD.toU.of_l henv hΓ hD
  have hΓD : OnCtx (D :: Γ) (env.IsType univs) := ⟨hΓ, u, hD⟩
  have W : IsDefEqCtx env univs [] (D :: Γ) (.const family [] :: Γ) := .succ (.refl hΓ) HD
  have hΓK := (W.symm henv.ordered).isType
  have hC := HB.hasType.2.defeqDFC henv W
  have hTarget := (HE.of_l henv hΓ hPi).hasType.2
  by_cases hpa : IsProof Γ a
  · obtain ⟨P, haP, hP⟩ := hpa
    have hpb : IsProof Γ b := ⟨P, hb.defeqU_r henv hΓ (ha.uniqU henv hΓ haP), hP⟩
    rw [proofErase_eq_proof.2 ⟨P, haP, hP⟩, proofErase_eq_proof.2 hpb]
    exact .carrierChecked (.leaf .refl)
  have hpb : ¬ IsProof Γ b := by
    rintro ⟨P, hbP, hP⟩
    exact hpa ⟨P, ha.defeqU_r henv hΓ (hb.uniqU henv hΓ hbP), hP⟩
  have hfa : env.HasType univs (D :: Γ) (.app a.lift (.bvar 0)) B := by
    simpa only [lift, VExpr.liftN, inst_liftN_bvar] using HasType.app (ha.weak henv) (.bvar .zero)
  have hfb : env.HasType univs (D :: Γ) (.app b.lift (.bvar 0)) B := by
    simpa only [lift, VExpr.liftN, inst_liftN_bvar] using HasType.app (hb.weak henv) (.bvar .zero)
  have Efa := proofErase_eta_body hΓ hD ha hpa
  have Efb := proofErase_eta_body hΓ hD hb hpb
  have HG' := (proofErase_joint_closed_binder (mode := true) hstep hhead hsubst hr hΓ HD hfa hfb).2
    (by simpa only [Efa, Efb] using HG)
  have HB' := HB.defeqDFC henv W
  have HG'' := HC.readout hstep hΓK hC HB'.hasType.1 HB'.toU HG'
  rw [← proofErase_defeqCtx hΓD W hfa, ← proofErase_defeqCtx hΓD W hfb, Efa, Efb] at HG''
  rw [show proofErase Γ (.forallE (.const family []) C) =
    .forallE (proofErase Γ (.const family [])) (proofErase (.const family [] :: Γ) C) from
    if_neg (not_isProof_of_sort hΓ hTarget)]
  exact .carrierFunction ⟨Γ, .const family [], hΓ, rfl, HD.hasType.2, rfl⟩ HG''

private theorem closed_function_readout_raw
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (hsubst : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextSubstitution Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (hr : env.Rigid family) (HC : ClosedBoxCarrier C)
    (hΓ : OnCtx Γ (env.IsType univs))
    (H : JointCheck Step Δ kind sa sb)
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b A)
    (HE : env.IsDefEqU univs Γ A (.forallE (.const family []) C))
    (EΓ : proofEraseCtx Γ = Δ)
    (E : JointCheckKind.carrier (proofErase Γ A) = kind)
    (Ea : proofErase Γ a = sa) (Eb : proofErase Γ b = sb) :
    JointCarrierGuard Step Δ (proofErase Γ (.forallE (.const family []) C)) sa sb := by
  induction H generalizing A a b with
  | carrierChecked H => exact .carrierChecked H
  | carrierSymm H ih => exact .carrierSymm (ih hb ha HE EΓ E Eb Ea)
  | carrierReduce RA RB H ih =>
    obtain ⟨a', HA, EA⟩ := proofErase_scoped_compute_realize hstep hΓ ha EΓ Ea RA
    obtain ⟨b', HB, EB⟩ := proofErase_scoped_compute_realize hstep hΓ hb EΓ Eb RB
    exact .carrierReduce RA RB (ih HA.hasType.2 HB.hasType.2 HE EΓ E EA EB)
  | carrierCompute R H ih =>
    obtain ⟨_, hA⟩ := ha.isType henv hΓ
    obtain ⟨A', HA, EA⟩ := proofErase_scoped_compute_realize hstep hΓ hA EΓ
      (JointCheckKind.carrier.inj E) R
    exact ih (HA.defeq ha) (HA.defeq hb) (HA.symm.toU.trans henv hΓ HE) EΓ
      (congrArg JointCheckKind.carrier EA) Ea Eb
  | carrierFunction SD H =>
    obtain ⟨D, B, rfl, _, ED, EB⟩ := erase_forallE_inv (JointCheckKind.carrier.inj E)
    obtain ⟨_, hPi⟩ := ha.isType henv hΓ
    obtain ⟨⟨_, hD⟩, _, _⟩ := hPi.forallE_inv henv
    have hD := domain_sort_raw SD hΓ hD EΓ ED
    have HG := function_body_readout hstep hhead hsubst hr HC hΓ hD ha hb HE
      (by simpa only [proofEraseCtx, EΓ, ED, EB, Ea, Eb] using H)
    simpa only [EΓ, Ea, Eb] using HG
  | carrierSubsingleton HS =>
    cases HS with
    | unit hi hz hf hp =>
      obtain ⟨args, rfl, _⟩ := proofErase_const_spine_inv (JointCheckKind.carrier.inj E)
      obtain ⟨_, hA⟩ := ha.isType henv hΓ
      exact (henv.headInversion.forallE_rigid hΓ (henv.projectionRigid hi)
        (HE.symm.typeChain henv hΓ (HE.of_l henv hΓ hA).hasType.2)).elim
    | forallE HS =>
      obtain ⟨D, B, rfl, _, ED, EB⟩ := erase_forallE_inv (JointCheckKind.carrier.inj E)
      obtain ⟨_, hPi⟩ := ha.isType henv hΓ
      obtain ⟨⟨_, hD⟩, _, _⟩ := hPi.forallE_inv henv
      have HG := function_body_readout hstep hhead hsubst hr HC hΓ hD ha hb HE
        (.carrierSubsingleton (EB.symm ▸ HS))
      simpa only [EΓ, Ea, Eb] using HG
  | carrierIntro hi hz hp hadm HF | carrierNested hi hz hp hadm HT HF =>
    obtain ⟨args, rfl, _⟩ := proofErase_const_spine_inv (JointCheckKind.carrier.inj E)
    obtain ⟨_, hA⟩ := ha.isType henv hΓ
    exact (henv.headInversion.forallE_rigid hΓ (henv.projectionRigid hi)
      (HE.symm.typeChain henv hΓ (HE.of_l henv hΓ hA).hasType.2)).elim
  | leaf | app | appCarrier | proj | lam | forallE | lamSorted | forallSorted | lamCommon |
      etaBodyL | etaBodyR | structFields | etaLams | compute | symm => cases E

/-- Every typed guard at an equal source carrier reads at a function type
whose domain is closed rigid and whose codomain belongs to the closed Box
fragment. All joint guard constructors and source computation prefixes are
covered. This is a target fragment, not general semantic carrier conversion. -/
theorem ClosedBoxCarrier.function_readout (HC : ClosedBoxCarrier C)
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (hsubst : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextSubstitution Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (hr : env.Rigid family) (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b A)
    (HE : env.IsDefEqU univs Γ A (.forallE (.const family []) C))
    (H : JointCarrierGuard Step (proofEraseCtx Γ) (proofErase Γ A)
      (proofErase Γ a) (proofErase Γ b)) :
    JointCarrierGuard Step (proofEraseCtx Γ) (proofErase Γ (.forallE (.const family []) C))
      (proofErase Γ a) (proofErase Γ b) :=
  closed_function_readout_raw hstep hhead hsubst hr HC hΓ H ha hb HE rfl rfl rfl rfl

/-- Closed function targets have no nontrivial erased beta path. The domain
is rigid and the closed Box codomain is beta fixed independently. -/
theorem ClosedBoxCarrier.function_beta_fixed (HC : ClosedBoxCarrier C)
    (hr : env.Rigid family) (hΓ : OnCtx Γ (env.IsType univs))
    (hT : env.HasType univs Γ (.forallE (.const family []) C) (.sort u))
    (R : ProofShape.BetaRed (proofErase Γ (.forallE (.const family []) C)) out) :
    out = proofErase Γ (.forallE (.const family []) C) := by
  obtain ⟨⟨v, hK⟩, _, hC⟩ := hT.forallE_inv henv
  have hΓK : OnCtx (.const family [] :: Γ) (env.IsType univs) := ⟨hΓ, v, hK⟩
  rw [show proofErase Γ (.forallE (.const family []) C) =
    .forallE (proofErase Γ (.const family [])) (proofErase (.const family [] :: Γ) C) from
    if_neg (not_isProof_of_sort hΓ hT)] at R ⊢
  obtain ⟨D', B', rfl, RD, RB⟩ := beta_forallE_parts R
  rw [(ClosedBoxCarrier.rigid hr).beta_fixed hΓ hK RD, HC.beta_fixed hΓK hC RB]

/-- Typed full future guards transport to the same closed function fragment.
Each future endpoint beta path is replayed to retain endpoint typing; each
interpreted substitution preserves the closed target. No future body inversion
or general application-closure principle is used. -/
theorem ClosedBoxCarrier.function_future_readout (HC : ClosedBoxCarrier C)
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (hsubst : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextSubstitution Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (hr : env.Rigid family) (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b A)
    (HE : env.IsDefEq univs Γ A (.forallE (.const family []) C) (.sort u))
    (H : BetaStableCarrier Step (proofEraseCtx Γ) (proofErase Γ A)
      (proofErase Γ a) (proofErase Γ b)) :
    BetaStableCarrier Step (proofEraseCtx Γ) (proofErase Γ (.forallE (.const family []) C))
      (proofErase Γ a) (proofErase Γ b) := by
  constructor
  · intro T p q RT RP RQ
    rw [HC.function_beta_fixed hr hΓ HE.hasType.2 RT]
    obtain ⟨a', HA, EA⟩ := proofErase_scoped_compute_realize hstep hΓ ha rfl rfl (.beta RP)
    obtain ⟨b', HB, EB⟩ := proofErase_scoped_compute_realize hstep hΓ hb rfl rfl (.beta RQ)
    have HG := HC.function_readout hstep hhead hsubst hr hΓ HA.hasType.2 HB.hasType.2 HE.toU
      (by simpa only [EA, EB] using H.1 .refl RP RQ)
    simpa only [EA, EB] using HG
  · intro Δ' τ T p q W RT RP RQ
    have HG := H.2 W .refl RP RQ
    obtain ⟨Γ₀, σ, hΓ₀, EΓ₀, WS, ES⟩ := W hΓ rfl
    have ET : (VExpr.forallE (.const family []) C).subst σ = .forallE (.const family []) C := by
      simp only [VExpr.subst, HC.subst]
    have HE' := HE.subst henv WS
    rw [ET] at HE'
    rw [← proofErase_subst_with hΓ₀ WS HE.hasType.1 ES, ← EΓ₀] at HG
    rw [← proofErase_subst_with hΓ₀ WS HE.hasType.2 ES, ET] at RT
    rw [← proofErase_subst_with hΓ₀ WS ha ES] at RP
    rw [← proofErase_subst_with hΓ₀ WS hb ES] at RQ
    rw [← EΓ₀, HC.function_beta_fixed hr hΓ₀ HE'.hasType.2 RT]
    obtain ⟨a', HA, EA⟩ := proofErase_scoped_compute_realize hstep hΓ₀ (ha.subst henv WS)
      rfl rfl (.beta RP)
    obtain ⟨b', HB, EB⟩ := proofErase_scoped_compute_realize hstep hΓ₀ (hb.subst henv WS)
      rfl rfl (.beta RQ)
    have HG' := HC.function_readout hstep hhead hsubst hr hΓ₀ HA.hasType.2 HB.hasType.2 HE'.toU
      (by simpa only [EA, EB] using HG)
    simpa only [EA, EB] using HG'

/-- The certified relation supplies every primitive premise for function
future readout. Actual source/target type equality and source endpoint typings
are the only semantic inputs beyond the closed target grammar. -/
theorem ClosedBoxCarrier.certified_function_future_readout (HC : ClosedBoxCarrier C)
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hr : env.Rigid family) (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b A)
    (HE : env.IsDefEq univs Γ A (.forallE (.const family []) C) (.sort u))
    (H : BetaStableCarrier (ErasedBetaStableJoint D) (proofEraseCtx Γ) (proofErase Γ A)
      (proofErase Γ a) (proofErase Γ b)) :
    BetaStableCarrier (ErasedBetaStableJoint D) (proofEraseCtx Γ)
      (proofErase Γ (.forallE (.const family []) C)) (proofErase Γ a) (proofErase Γ b) :=
  HC.function_future_readout (erased_beta_stable_joint_descent heq hs)
    erased_beta_stable_joint_head (erased_beta_stable_joint_subst heq hs) hr hΓ ha hb HE H

end Lean4Lean.VEnv.Strengthening
