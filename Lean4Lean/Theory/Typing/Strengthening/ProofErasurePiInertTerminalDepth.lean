import Lean4Lean.Theory.Typing.Strengthening.ProofErasureComputedJointDepth
import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertComparedControlApplication

/-! # Terminal substitution preserves structural checker depth

Typed terminal-image transport may replace native recovery by a computed
application domain. Both rules occupy the same structural layer, so this
repair preserves the full checker depth, including carrier subderivations.
The bounded lambda cut then contracts constant control applications at the
function child's depth, strictly below the enclosing application layer.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params] {D : Definitions}

/-- Every comparison and carrier constructor transports under terminal-image
substitution at the unchanged expansion base. Native application uses exact
recovery or the proved selected-domain exposure; no body-check or application
repair premise remains. The full structural-depth bound is preserved.
This theorem does not assert transport at later stages. -/
theorem ProofShape.ComputedJointCheckDepth.transport_pi_inert_zero_terminal
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (H : ComputedJointCheckDepth (PiInertStage D 0) depth Δ kind sa sb) :
    ComputedJointTransportDepthResult (PiInertZeroTerminalSubstitution D)
      (PiInertStage D 0) depth Δ kind sa sb := by
  apply H.transport (PiInertZeroTerminalSubstitution D)
    (ErasedScopedPrimitiveCertificateDescent.descent (pi_inert_stage_certificate_descent heq hs 0))
    (fun W => W.cons heq hs) (fun W S => ContextSubstitution.sort W.interpretation S)
    (fun R hΓ ht EΓ Ee W => R.subst_typed
      (ErasedScopedPrimitiveCertificateDescent.descent (pi_inert_stage_certificate_descent heq hs 0))
      pi_inert_zero_primitive_substitution hΓ ht EΓ Ee W.interpretation)
  intro Γ Δ' τ f C E A B hΓ hf hn R W
  obtain ⟨Γ₀, σ, hΓ₀, EΓ₀, WS, ES, HI⟩ := W hΓ rfl
  rcases pi_inert_zero_recovery_subst_terminal_images heq hs R hΓ₀ WS ES hf rfl rfl HI with
    RN | ⟨T, n, HP, ET⟩
  · exact .inl (EΓ₀ ▸ RN)
  · have HL := HP.selected_domain heq hs hΓ₀ (hf.subst henv.orderedStrong WS hΓ₀)
      (mt (isProof_subst hΓ₀ WS hf).1 hn) ET
    exact .inr (by simpa only [proofErase_subst_with hΓ₀ WS hf ES, EΓ₀] using HL)

/-- Any terminal typed value can replace its assigned binder in a whole
stage-zero body comparison. The assigned type need not compute from the type
certifying terminality, and both comparison modes are preserved. -/
theorem pi_inert_zero_compare_depth_inst_terminal
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hp : env.HasType univs Γ p P) (HT : TerminalImage Γ p)
    (ha : env.HasType univs (P :: Γ) a A) (hb : env.HasType univs (P :: Γ) b A)
    (H : ComputedJointCompareDepth (PiInertStage D 0) depth (proofEraseCtx (P :: Γ)) mode
      (proofErase (P :: Γ) a) (proofErase (P :: Γ) b)) :
    ComputedJointCompareDepth (PiInertStage D 0) depth (proofEraseCtx Γ) mode
      (proofErase Γ (a.inst p)) (proofErase Γ (b.inst p)) := by
  obtain ⟨u, hP⟩ := hp.isType henv hΓ
  have hΓP : OnCtx (P :: Γ) (env.IsType univs) := ⟨hΓ, u, hP⟩
  have W := (Ctx.InstN.zero (Γ₀ := Γ) (e₀ := p) (A₀ := P)).substEq hΓP hp
  have HI : PiInertZeroTerminalImages D (P :: Γ) Γ (VExpr.Subst.one p)
      (ProofShape.Subst.one (proofErase Γ p)) := by
    intro i T hl _
    cases hl with
    | zero => exact .inr HT
    | succ hl =>
      apply Or.inl
      simp only [proofEraseCtx, contextOracle, TypeOracle.cons, ProofShape.Subst.one,
        ProofShape.lift_subst_cons, ProofShape.subst_id]
      exact .bvar
  have HR := H.transport_pi_inert_zero_terminal heq hs hΓP ha hb rfl rfl rfl
    (PiInertZeroTerminalSubstitution.of_typed hΓ W (erasedSubstAgreement_one hΓP hp) HI)
  rw [proofErase_instN hΓP hp Ctx.InstN.zero ha, proofErase_instN hΓP hp Ctx.InstN.zero hb]
  simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using HR

/-- A lambda cut retains a body comparison at the original structural bound,
or closes by reflexivity or typed eta. The body scope records either written
annotation; no body comparison is asserted for an eta terminal. -/
def InferredLambdaDepthBody (Step : List ProofShape → ProofShape → ProofShape → Prop)
    (depth : Nat) (Δ : List ProofShape) (A b C d : ProofShape) : Prop :=
  (A = C ∧ b = d) ∨
    ComputedJointCompareDepth Step depth (A :: Δ) false b d ∨
    ComputedJointCompareDepth Step depth (C :: Δ) false b d ∨
    (EtaHead (.lam A b) (.lam C d) ∨ EtaHead (.lam C d) (.lam A b))

/-- Reversing the cut also reverses which annotation scopes its body child. -/
theorem InferredLambdaDepthBody.symm
    (H : InferredLambdaDepthBody Step depth Δ A b C d) :
    InferredLambdaDepthBody Step depth Δ C d A b := by
  rcases H with ⟨rfl, rfl⟩ | HL | HR | HE
  · exact .inl ⟨rfl, rfl⟩
  · exact .inr (.inr (.inl (.symm HL)))
  · exact .inr (.inl (.symm HR))
  · exact .inr (.inr (.inr HE.symm))

private theorem inferred_lambda_depth_cut
    (H : ComputedJointCheckDepth (PiInertStage D n) depth Δ kind a b)
    (hk : kind = .compare false)
    (HL : (∃ A body, a = .lam A body) ∨ ∃ C body, b = .lam C body) :
    ∃ A x C y, ScopedCompute (PiInertStage D n) Δ a (.lam A x) ∧
      ScopedCompute (PiInertStage D n) Δ b (.lam C y) ∧
      InferredLambdaDepthBody (PiInertStage D n) depth Δ A x C y := by
  induction H with
  | leaf H =>
    cases hk
    cases H with
    | refl =>
      rcases HL with ⟨A, x, rfl⟩ | ⟨A, x, rfl⟩ <;>
        exact ⟨A, x, A, x, .refl, .refl, .inl ⟨rfl, rfl⟩⟩
    | sort | const => rcases HL with ⟨_, _, E⟩ | ⟨_, _, E⟩ <;> cases E
  | lam _ HB => exact ⟨_, _, _, _, .refl, .refl, .inr (.inl (by cases hk; exact HB.weaken (Nat.le_succ _)))⟩
  | lamSorted _ _ _ HB => exact ⟨_, _, _, _, .refl, .refl, .inr (.inl (by cases hk; exact HB.weaken (Nat.le_succ _)))⟩
  | etaLams _ HE => exact ⟨_, _, _, _, .refl, .refl, .inr (.inr (.inr HE))⟩
  | compute RA RB HC ih =>
    obtain ⟨A, x, C, y, RX, RY, HC⟩ := ih hk (by
      rcases HL with ⟨A, x, E⟩ | ⟨C, y, E⟩
      · obtain ⟨A', x', E', _⟩ := (E ▸ RA).pi_inert_lam_domain
        exact .inl ⟨A', x', E'⟩
      · obtain ⟨C', y', E', _⟩ := (E ▸ RB).pi_inert_lam_domain
        exact .inr ⟨C', y', E'⟩)
    exact ⟨A, x, C, y, RA.trans RX, RB.trans RY, HC⟩
  | symm HC ih =>
    obtain ⟨A, x, C, y, RX, RY, HT⟩ := ih hk HL.symm
    exact ⟨C, y, A, x, RY, RX, .symm HT⟩
  | app | appCarrier | appComputed | proj | forallE | forallSorted =>
    rcases HL with ⟨_, _, E⟩ | ⟨_, _, E⟩ <;> cases E
  | lamCommon | etaBodyL | etaBodyR | structFields |
      carrierIntro | carrierChecked | carrierSubsingleton | carrierFunction |
      carrierSymm | carrierCompute | carrierReduce | carrierNested => cases hk

/-- An inferred comparison with one displayed lambda computes both endpoints
to a body cut at the unchanged depth bound. Neither endpoint typing is needed
for the cut; typed instantiation handles the eta alternative separately. -/
theorem ProofShape.ComputedJointCompareDepth.pi_inert_lambda_depth_cut
    (H : ComputedJointCompareDepth (PiInertStage D n) depth Δ false (.lam A b) g) :
    ∃ A' b' C d, ScopedCompute (PiInertStage D n) Δ (.lam A b) (.lam A' b') ∧
      ScopedCompute (PiInertStage D n) Δ g (.lam C d) ∧
      InferredLambdaDepthBody (PiInertStage D n) depth Δ A' b' C d :=
  inferred_lambda_depth_cut H rfl (.inl ⟨A, b, rfl⟩)

open private erase_lam_inv erase_app_inv
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
open private lambda_common_context
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureComputedJointTransport
open private eta_inst_typed
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRecoveredHeadBeta
open private isProof_congr
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
open private source_realize
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureConstructorTypeExposure
open private control_realize
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureConstructorTypeReadout

private theorem terminal_depth_body_inst
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hp : env.HasType univs Γ p P) (HT : TerminalImage Γ p)
    (hf : env.HasType univs Γ f (.forallE P T)) (hg : env.HasType univs Γ g (.forallE P T))
    (Ef : proofErase Γ f = .lam A a) (Eg : proofErase Γ g = .lam B b)
    (H : ComputedJointCompareDepth (PiInertStage D 0) depth (A :: proofEraseCtx Γ) false a b) :
    ComputedJointCompareDepth (PiInertStage D 0) depth (proofEraseCtx Γ) false
      (a.inst (proofErase Γ p)) (b.inst (proofErase Γ p)) := by
  obtain ⟨A₀, a₀, rfl, _, EA, Ea⟩ := erase_lam_inv Ef
  obtain ⟨B₀, b₀, rfl, _, EB, Eb⟩ := erase_lam_inv Eg
  obtain ⟨u, C, hA, _, ha, hb, Ectx⟩ := lambda_common_context hΓ hf hg
  have hpA := argument_at_displayed_domain hΓ hf (HasType.lam hA ha) hp
  have hΓA : OnCtx (A₀ :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  have HC := pi_inert_zero_compare_depth_inst_terminal heq hs hΓ hpA HT ha hb
    (by simpa only [proofEraseCtx, EA, Ea, ← Ectx, Eb] using H)
  rw [proofErase_instN hΓA hpA Ctx.InstN.zero ha,
    proofErase_instN hΓA hpA Ctx.InstN.zero hb] at HC
  simpa only [Ea, ← Ectx, Eb] using HC

/-- Every terminal inferred lambda rule can be instantiated at a terminal
actual argument, even if both bodies depend on it and their written domains
differ. Both body-scope orientations and the proof-marker eta case are covered. -/
theorem InferredLambdaDepthBody.pi_inert_zero_inst_terminal
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hp : env.HasType univs Γ p P) (HT : TerminalImage Γ p)
    (hf : env.HasType univs Γ f (.forallE P T)) (hg : env.HasType univs Γ g (.forallE P T))
    (Ef : proofErase Γ f = .lam A a) (Eg : proofErase Γ g = .lam B b)
    (H : InferredLambdaDepthBody (PiInertStage D 0) depth (proofEraseCtx Γ) A a B b) :
    ComputedJointCompareDepth (PiInertStage D 0) depth (proofEraseCtx Γ) false
      (a.inst (proofErase Γ p)) (b.inst (proofErase Γ p)) := by
  rcases H with ⟨_, rfl⟩ | HL | HR | HE
  · exact .leaf .refl
  · exact terminal_depth_body_inst heq hs hΓ hp HT hf hg Ef Eg HL
  · exact .symm (terminal_depth_body_inst heq hs hΓ hp HT hg hf Eg Ef (.symm HR))
  · rcases HE with HE | HE
    · exact .compute (.beta (eta_inst_typed hΓ hp hf hg (by simpa only [Ef, Eg] using HE) Ef Eg))
        .refl (.leaf .refl)
    · exact .compute .refl
        (.beta (eta_inst_typed hΓ hp hg hf (by simpa only [Ef, Eg] using HE) Eg Ef)) (.leaf .refl)

/-- An inferred comparison with one displayed lambda survives contraction at
a terminal argument. The opposite function is arbitrary and its body may
depend on that argument. The resulting checker remains Pi-inert stage zero;
no forward beta-closure hypothesis or target lambda shape is assumed. -/
theorem proofErase_pi_inert_zero_terminal_lambda_application_depth
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hp : env.HasType univs Γ p P) (HT : TerminalImage Γ p)
    (hf : env.HasType univs Γ (.lam A a) (.forallE P T))
    (hg : env.HasType univs Γ g (.forallE P T)) (hnf : ¬ IsProof Γ (.lam A a))
    (H : ComputedJointCompareDepth (PiInertStage D 0) depth (proofEraseCtx Γ) false
      (proofErase Γ (.lam A a)) (proofErase Γ g)) :
    ComputedJointCompareDepth (PiInertStage D 0) depth (proofEraseCtx Γ) false
      (proofErase Γ (a.inst p)) (.app (proofErase Γ g) (proofErase Γ p)) := by
  have hd : ErasedScopedPrimitiveDescent (PiInertStage D 0) :=
    ErasedScopedPrimitiveCertificateDescent.descent (pi_inert_stage_certificate_descent heq hs 0)
  obtain ⟨⟨u, hA⟩, C, ha⟩ := hf.lam_inv henv hΓ
  have hpA := argument_at_displayed_domain hΓ hf (HasType.lam hA ha) hp
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  have EF : proofErase Γ (.lam A a) = .lam (proofErase Γ A) (proofErase (A :: Γ) a) := if_neg hnf
  have HR := H
  rw [EF] at HR
  obtain ⟨X, x, Y, y, RF, RG, HC⟩ := HR.pi_inert_lambda_depth_cut
  obtain ⟨f', HF, Ef⟩ := proofErase_scoped_compute_realize @hd hΓ hf rfl EF RF
  obtain ⟨g', HG, Eg⟩ := proofErase_scoped_compute_realize @hd hΓ hg rfl rfl RG
  have HI := HC.pi_inert_zero_inst_terminal heq hs hΓ hp HT HF.hasType.2 HG.hasType.2 Ef Eg
  obtain ⟨_, _, EE, _, RB⟩ := RF.pi_inert_zero_lam_parts
  cases EE
  have W := (Ctx.InstN.zero (Γ₀ := Γ) (e₀ := p) (A₀ := A)).substEq hΓA hpA
  have ES : ErasedSubstAgreement (A :: Γ) Γ (VExpr.Subst.one p)
      (ProofShape.Subst.one (proofErase Γ p)) := erasedSubstAgreement_one hΓA hpA
  have RI := proofErase_scoped_compute_subst_typed @hd pi_inert_zero_primitive_substitution
    hΓ W ES ha RB
  have RI' : ScopedCompute (PiInertStage D 0) (proofEraseCtx Γ)
      (proofErase Γ (a.inst p)) (x.inst (proofErase Γ p)) := by
    simpa only [VExpr.inst_eq, VExpr.Subst.liftN, ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using RI
  exact .compute RI' ((ScopedCompute.app RG .refl).trans (.beta .beta)) HI

/-- A constant function with a nonproof payload can be removed from an inferred
application comparison at a terminal target argument. The other function and
its body are arbitrary; only its actual typing is supplied. No argument
comparison, displayed target lambda or target binder-independence is needed. -/
theorem proofErase_pi_inert_zero_constant_function_application_depth
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort w))
    (ha : env.HasType univs Γ a T) (hna : ¬ IsProof Γ a)
    (hp : env.HasType univs Γ p A) (HT : TerminalImage Γ p)
    (hg : env.HasType univs Γ g G)
    (H : ComputedJointCompareDepth (PiInertStage D 0) depth (proofEraseCtx Γ) false
      (proofErase Γ (.lam A a.lift)) (proofErase Γ g)) :
    ComputedJointCompareDepth (PiInertStage D 0) depth (proofEraseCtx Γ) false
      (proofErase Γ a) (proofErase Γ (.app g p)) := by
  have hf : env.HasType univs Γ (.lam A a.lift) (.forallE A T.lift) :=
    .lam hA (ha.weak henv)
  have Hbeta : env.IsDefEq univs Γ (.app (.lam A a.lift) p) a T := by
    simpa only [VExpr.inst_lift] using IsDefEq.beta (ha.weak henv (B := A)) hp
  have hnapp : ¬ IsProof Γ (.app (.lam A a.lift) p) :=
    mt (isProof_congr hΓ Hbeta).1 hna
  have hnf := not_isProof_fn hΓ hf hp hnapp
  have EF : proofErase Γ (.lam A a.lift) =
      .lam (proofErase Γ A) (proofErase (A :: Γ) a.lift) := if_neg hnf
  have HR := H
  rw [EF] at HR
  obtain ⟨_, _, _, _, _, RG, _⟩ := HR.pi_inert_lambda_depth_cut
  have hng : ¬ IsProof Γ g := by
    intro hproof
    rw [proofErase_eq_proof.2 hproof] at RG
    cases RG.pi_inert_proof_fixed
  have hd : ErasedScopedPrimitiveDescent (PiInertStage D 0) :=
    ErasedScopedPrimitiveCertificateDescent.descent (pi_inert_stage_certificate_descent heq hs 0)
  have HE := (proofErase_computed_joint_compare_reflect @hd hΓ hf hg H.forget).2 rfl hnf hng
  have hgPi := (HE.of_l henv hΓ hf).hasType.2
  have HApp : env.IsDefEq univs Γ (.app (.lam A a.lift) p) (.app g p) T := by
    simpa only [VExpr.inst_lift] using IsDefEq.appDF (HE.of_l henv hΓ hf) hp
  have hngp := mt (isProof_congr hΓ HApp).2 hnapp
  have EG : proofErase Γ (.app g p) = .app (proofErase Γ g) (proofErase Γ p) :=
    if_neg hngp
  have HC := proofErase_pi_inert_zero_terminal_lambda_application_depth heq hs hΓ hp HT hf hgPi hnf H
  simpa only [VExpr.inst_lift, EG] using HC
/-- Inferred comparison of constant control functions retypes the target
application argument at the source domain. If the discarded source argument
is a type, the target argument is terminal automatically. The target body may
depend on it; neither an argument guard nor target native recovery is needed. -/
theorem proofErase_pi_inert_zero_constant_application_of_type_argument_depth
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort w))
    (ha : env.HasType univs Γ a T) (hna : ¬ IsProof Γ a)
    (hx : env.HasType univs Γ x A) (hxu : env.HasType univs Γ x (.sort u))
    (hgp : env.HasType univs Γ (.app g p) U)
    (H : ComputedJointCompareDepth (PiInertStage D 0) depth (proofEraseCtx Γ) false
      (proofErase Γ (.lam A a.lift)) (proofErase Γ g)) :
    ComputedJointCompareDepth (PiInertStage D 0) depth (proofEraseCtx Γ) false
      (proofErase Γ a) (proofErase Γ (.app g p)) := by
  have hf : env.HasType univs Γ (.lam A a.lift) (.forallE A T.lift) :=
    .lam hA (ha.weak henv)
  have Hbeta : env.IsDefEq univs Γ (.app (.lam A a.lift) x) a T := by
    simpa only [VExpr.inst_lift] using IsDefEq.beta (ha.weak henv (B := A)) hx
  have hnapp := mt (isProof_congr hΓ Hbeta).1 hna
  have hnf := not_isProof_fn hΓ hf hx hnapp
  have EF : proofErase Γ (.lam A a.lift) =
      .lam (proofErase Γ A) (proofErase (A :: Γ) a.lift) := if_neg hnf
  have HR := H
  rw [EF] at HR
  obtain ⟨_, _, _, _, _, RG, _⟩ := HR.pi_inert_lambda_depth_cut
  have hng : ¬ IsProof Γ g := by
    intro hproof
    rw [proofErase_eq_proof.2 hproof] at RG
    cases RG.pi_inert_proof_fixed
  obtain ⟨C, E, hg, hp⟩ := hgp.app_inv henv hΓ
  have hd : ErasedScopedPrimitiveDescent (PiInertStage D 0) :=
    ErasedScopedPrimitiveCertificateDescent.descent (pi_inert_stage_certificate_descent heq hs 0)
  have HE := (proofErase_computed_joint_compare_reflect @hd hΓ hf hg H.forget).2 rfl hnf hng
  have hgPi := (HE.of_l henv hΓ hf).hasType.2
  have hpA := argument_at_displayed_domain hΓ hg hgPi hp
  have hpu := hpA.defeqU_r henv hΓ (hx.uniqU henv hΓ hxu)
  exact proofErase_pi_inert_zero_constant_function_application_depth heq hs hΓ hA ha hna
    hpA (.type hpu) hg H

/-- An erased constant frame can be removed directly from an application
node's inferred function child. Only the erased body must omit the binder;
the actual body need not be a lift. Source application typing supplies a typed
nonproof lower payload by beta realization, and the discarded source argument
is sort-typed. No payload, target argument or target body certificate is an
additional premise. The output has the function child's depth, while each of
the three enclosing application rules adds one layer. Thus this readout gives
a strictly smaller bound for recursion on the rebuilt comparison. -/
theorem pi_inert_zero_constant_control_application_depth
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (HTX : TypedSource Δ (.app (.lam rawA (rawa.liftN 1)) rawx))
    (HTY : TypedSource Δ (.app rawg rawp))
    (HX : ControlTyping Δ rawx (.sort u))
    (HF : ComputedJointCompareDepth (PiInertStage D 0) depth Δ false
      (.lam rawA (rawa.liftN 1)) rawg) :
    ComputedJointCompareDepth (PiInertStage D 0) depth Δ false rawa (.app rawg rawp) := by
  obtain ⟨Γ, e, T, hΓ, EΓ, ht, Ee⟩ := HTX
  have hd : ErasedScopedPrimitiveDescent (PiInertStage D 0) :=
    ErasedScopedPrimitiveCertificateDescent.descent (pi_inert_stage_certificate_descent heq hs 0)
  have R : ScopedCompute (PiInertStage D 0) Δ
      (.app (.lam rawA (rawa.liftN 1)) rawx) rawa :=
    .beta ConstantHeadDeletion.drop.reduce
  obtain ⟨a, HA, Ea⟩ := proofErase_scoped_compute_realize @hd hΓ ht EΓ Ee R
  have hne : ¬ IsProof Γ e := by
    intro hp
    have E := Ee.symm.trans (proofErase_eq_proof.2 hp)
    cases E
  have ha := HA.hasType.2
  have hna := mt (isProof_congr hΓ HA).2 hne
  obtain ⟨f₀, x₀, rfl, _, Ef, Ex⟩ := erase_app_inv Ee
  obtain ⟨A₀, b₀, rfl, _, EA, _⟩ := erase_lam_inv Ef
  obtain ⟨P, Q, hf, hx⟩ := ht.app_inv henv hΓ
  obtain ⟨⟨w, hA⟩, B₀, hb⟩ := hf.lam_inv henv hΓ
  have hxA := argument_at_displayed_domain hΓ hf (HasType.lam hA hb) hx
  obtain ⟨x₁, hx₁, Ex₁⟩ := control_realize HX hΓ EΓ
  have hnx : ¬ IsProof Γ x₀ := fun hp => HX.ne_proof (Ex.symm.trans (proofErase_eq_proof.2 hp))
  obtain ⟨_, HE⟩ := (proofErase_reflect hΓ hxA hx₁ (Ex.trans Ex₁.symm)).2 hnx
  have hxSort := ((HE.defeq hΓ).of_r henv hΓ hx₁).hasType.1
  obtain ⟨e', T', ht', Ee'⟩ := source_realize HTY hΓ EΓ
  obtain ⟨g, p, rfl, _, Eg, _⟩ := erase_app_inv Ee'
  have hconst : env.HasType univs Γ (.lam A₀ a.lift) (.forallE A₀ T.lift) :=
    .lam hA (ha.weak henv)
  have Hbeta : env.IsDefEq univs Γ (.app (.lam A₀ a.lift) x₀) a T := by
    simpa only [VExpr.inst_lift] using IsDefEq.beta (ha.weak henv (B := A₀)) hxA
  have hnconst := not_isProof_fn hΓ hconst hxA (mt (isProof_congr hΓ Hbeta).1 hna)
  have hΓA : OnCtx (A₀ :: Γ) (env.IsType univs) := ⟨hΓ, w, hA⟩
  have EF : proofErase Γ (.lam A₀ a.lift) = .lam rawA (rawa.liftN 1) := by
    rw [show proofErase Γ (.lam A₀ a.lift) =
      .lam (proofErase Γ A₀) (proofErase (A₀ :: Γ) a.lift) from if_neg hnconst]
    rw [proofErase_liftN hΓ hΓA Ctx.LiftN.one ha, EA, Ea]
  have H := proofErase_pi_inert_zero_constant_application_of_type_argument_depth
    heq hs hΓ hA ha hna hxA hxSort ht'
      (by simpa only [EΓ, EF, Eg] using HF)
  simpa only [EΓ, Ea, Ee'] using H

end Lean4Lean.VEnv.Strengthening
