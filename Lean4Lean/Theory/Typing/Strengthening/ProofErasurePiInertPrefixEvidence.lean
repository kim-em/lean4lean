import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertEqHeadConsumer

/-! # Hereditary computation evidence before the Eq proof argument

An index carrier history repairs the independently computed arguments of the
five-argument prefix. The resulting certificate retains an ordinary-core tail
from the displayed lambda and survives every future typed substitution. It
therefore supplies the unsaturated input required by Eq-headed consumer closure.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
variable [Params] {D : Definitions}

/-- An ordinary-core path from the five-argument Eq prefix only computes its
arguments. Every possible root lies strictly before the registered major. -/
theorem ProofShape.Compute.eqRec_prefix_core_inv
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hD : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (R : Compute (ErasedIotaPrimitive D)
      (ProofShape.eqRecBeforeMajor v w α a M m b) out) :
    ∃ α' a' M' m' b', out = ProofShape.eqRecBeforeMajor v w α' a' M' m' b' ∧
      Compute (ErasedIotaPrimitive D) α α' ∧ Compute (ErasedIotaPrimitive D) a a' ∧
      Compute (ErasedIotaPrimitive D) M M' ∧ Compute (ErasedIotaPrimitive D) m m' ∧
      Compute (ErasedIotaPrimitive D) b b' := by
  have RS : ScopedCompute (fun _ => ErasedIotaPrimitive D) []
      (ProofShape.mkApps (.const ``Eq.rec [v,w]) [α,a,M,m,b]) out :=
    R.scoped (fun H => .base H)
  rcases RS.const_spine_or_head with ⟨args', E, HA⟩ | ⟨k, args', target, hk, HA, HS⟩
  · cases HA with | cons Rα HA =>
      cases HA with | cons Ra HA =>
        cases HA with | cons RM HA =>
          cases HA with | cons Rm HA =>
            cases HA with | cons Rb HA =>
              cases HA
              exact ⟨_, _, _, _, _, E, Rα.core_forget, Ra.core_forget,
                RM.core_forget, Rm.core_forget, Rb.core_forget⟩
  · apply (erased_iota_eqRec_no_root hreg hoff hD (constHead_mkApps _ _) ?_ HS).elim
    refine .inl ⟨_, _, rfl, ?_⟩
    have HL := HA.length_eq
    simp only [List.length_take, List.length_cons, List.length_nil] at HL
    omega

/-- The prefix's carrier residual repairs arbitrary full-core computation of
the source, including universe steps. Its displayed lambda keeps an ordinary
output tail; no common reduct of the indices is assumed. -/
theorem PiInertInterpret.eq_prefix
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (hl : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hD : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ (eqRecBeforeMajor v w α a M m b) T)
    (H : PiInertCarrierResidual D n (proofEraseCtx Γ) (proofErase Γ α)
      (proofErase Γ a) (proofErase Γ b)) :
    PiInertInterpret D (n+1) .compute (proofEraseCtx Γ)
      (proofErase Γ (eqRecBeforeMajor v w α a M m b))
      (proofErase Γ (.lam (eqApp w α a b) m.lift)) := by
  obtain ⟨_, hw, hα, ha, _, hm, hb⟩ := eqRecBeforeMajor_typings henv heq hΓ ⟨_, ht⟩
  have hab := proofErase_computed_joint_carrier_reflect
    (erased_static_structure_eta_expansion_stage_descent heq hs n) hΓ ha hb
    ((H .refl .refl .refl).mono (fun R => pi_inert_stage_embed R))
  have HE := eqRecBeforeMajor_simAt henv heq hΓ ⟨_, hab⟩ T ht
  refine ⟨⟨Γ, _, T, hΓ, rfl, HE.hasType.2, rfl⟩, ?_⟩
  intro out R
  obtain ⟨mid, RM, RT⟩ := proofErase_level_core_ordinary_return hs hl hcon hΓ ht R
  by_cases hp : IsProof Γ (eqRecBeforeMajor v w α a M m b)
  · have Et := proofErase_eq_proof.2 ((isProof_congr hΓ HE).1 hp)
    rw [proofErase_eq_proof.2 hp] at RM
    have E := (RM.scoped (Δ := []) (fun R => .base R)).proof_fixed
      (fun R => erased_iota_primitive_head R)
    subst mid
    exact ⟨.proof, RT.in_pi_inert_stage, Et ▸ .refl⟩
  · have hp' := mt (isProof_congr hΓ HE).2 hp
    have ES := proofErase_const_spine hΓ (args := [α, a, M, m, b]) ht hp
    change proofErase Γ (eqRecBeforeMajor v w α a M m b) = _ at ES
    rw [ES] at RM
    obtain ⟨α', a', M', m', b', rfl, Rα, Ra, _, Rm, Rb⟩ :=
      RM.eqRec_prefix_core_inv hreg hoff hD
    have HG := (H (Rα.mono (fun R => .inl R)) (Ra.mono (fun R => .inl R))
      (Rb.mono (fun R => .inl R))).mono (fun R => pi_inert_stage_embed R)
    have hE := HasType.eqApp heq hw hα ha hb
    have hΓE : OnCtx (eqApp w α a b :: Γ) (env.IsType univs) := ⟨hΓ, _, hE⟩
    rw [show proofErase Γ (.lam (eqApp w α a b) m.lift) =
      .lam (proofErase Γ (eqApp w α a b)) (proofErase (eqApp w α a b :: Γ) m.lift)
      from if_neg hp', proofErase_eqProofType heq hw hΓ hα ha hb,
      proofErase_liftN hΓ hΓE Ctx.LiftN.one hm]
    refine ⟨.lam (ProofShape.eqProofType w α' a' b') (m'.liftN 1),
      RT.in_pi_inert_stage.trans (.base ⟨.inr (.inr (.inl (.intro HG))), .inl trivial⟩), ?_⟩
    exact (Compute.lam (.app (.app (.app .refl Rα) Ra) Rb)
      (Rm.liftN (fun R => erased_iota_primitive_liftN R))).mono (fun R => .inl R)

omit [Params] in
/-- The actual five-argument recursor prefix commutes with substitution. -/
theorem eqRecBeforeMajor_subst : (eqRecBeforeMajor v w α a M m b).subst σ =
    eqRecBeforeMajor v w (α.subst σ) (a.subst σ) (M.subst σ) (m.subst σ) (b.subst σ) := rfl

/-- A complete index carrier history certifies the prefix before its proof
argument arrives. The certificate includes all future typed substitutions,
so subsequent typed consumers may duplicate or apply the resulting lambda. -/
theorem PiInertCarrierHistory.eq_prefix
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (hl : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hD : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ (eqRecBeforeMajor v w α a M m b) T)
    (H : PiInertCarrierHistory D n (proofEraseCtx Γ) (proofErase Γ α)
      (proofErase Γ a) (proofErase Γ b)) :
    PiInertEvidence D (n+1) .compute (proofEraseCtx Γ)
      (proofErase Γ (eqRecBeforeMajor v w α a M m b))
      (proofErase Γ (.lam (eqApp w α a b) m.lift)) := by
  refine ⟨PiInertInterpret.eq_prefix heq hs hl hcon hreg hoff hD hΓ ht H.base, ?_⟩
  intro Δ' τ W
  obtain ⟨Γ₀, σ, hΓ₀, EΓ₀, WS, ES⟩ := W hΓ rfl
  obtain ⟨_, _, hα, ha, _, _, hb⟩ := eqRecBeforeMajor_typings henv heq hΓ ⟨_, ht⟩
  have hab := proofErase_computed_joint_carrier_reflect
    (erased_static_structure_eta_expansion_stage_descent heq hs n) hΓ ha hb
    ((H.base .refl .refl .refl).mono (fun R => pi_inert_stage_embed R))
  have ht' := (eqRecBeforeMajor_simAt henv heq hΓ ⟨_, hab⟩ T ht).hasType.2
  have H' := H.substitute W
  rw [← EΓ₀, ← proofErase_subst_with hΓ₀ WS hα ES,
    ← proofErase_subst_with hΓ₀ WS ha ES, ← proofErase_subst_with hΓ₀ WS hb ES] at H'
  rw [← EΓ₀, ← proofErase_subst_with hΓ₀ WS ht ES,
    ← proofErase_subst_with hΓ₀ WS ht' ES, eqRecBeforeMajor_subst]
  simp only [VExpr.subst, VExpr.eqApp_subst, VExpr.lift_subst_lift]
  exact PiInertInterpret.eq_prefix heq hs hl hcon hreg hoff hD hΓ₀
    (by simpa only [eqRecBeforeMajor_subst] using ht.subst henv.orderedStrong WS hΓ₀) H'.base

/-- Index histories suffice to compute an unsaturated prefix inside any typed
consumer, including proof-valued prefixes. The consumer may use its argument
under binders or apply it; no guarded confluence or extra stage is required. -/
theorem PiInertCarrierHistory.eq_prefix_consumer
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (hl : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hD : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hr : env.HasType univs Γ (eqRecBeforeMajor v w α a M m b) T)
    (ht : env.HasType univs (T :: Γ) t S)
    (H : PiInertCarrierHistory D n (proofEraseCtx Γ) (proofErase Γ α)
      (proofErase Γ a) (proofErase Γ b)) :
    PiInertEvidence D (n+1) .compute (proofEraseCtx Γ)
      (proofErase Γ (t.inst (eqRecBeforeMajor v w α a M m b)))
      (proofErase Γ (t.inst (.lam (eqApp w α a b) m.lift))) := by
  obtain ⟨_, _, _, ha, _, _, hb⟩ := eqRecBeforeMajor_typings henv heq hΓ ⟨_, hr⟩
  have hab := proofErase_computed_joint_carrier_reflect
    (erased_static_structure_eta_expansion_stage_descent heq hs n) hΓ ha hb
    ((H.base .refl .refl .refl).mono (fun R => pi_inert_stage_embed R))
  have HE := eqRecBeforeMajor_simAt henv heq hΓ ⟨_, hab⟩ T hr
  have htarget := HE.hasType.2
  by_cases hp : IsProof Γ (eqRecBeforeMajor v w α a M m b)
  · have hΓT : OnCtx (T :: Γ) (env.IsType univs) := ⟨hΓ, hr.isType henv hΓ⟩
    have E : proofErase Γ (t.inst (eqRecBeforeMajor v w α a M m b)) =
        proofErase Γ (t.inst (.lam (eqApp w α a b) m.lift)) := by
      rw [proofErase_instN hΓT hr Ctx.InstN.zero ht,
        proofErase_instN hΓT htarget Ctx.InstN.zero ht,
        proofErase_eq_proof.2 hp, proofErase_eq_proof.2 ((isProof_congr hΓ HE).1 hp)]
    rw [E]
    have hright := ht.instN henv Ctx.InstN.zero htarget
    refine ⟨⟨⟨Γ, _, _, hΓ, rfl, hright, rfl⟩, fun R => ⟨_, .refl, R⟩⟩, ?_⟩
    intro Δ' τ W
    obtain ⟨Γ₀, σ, hΓ₀, EΓ₀, WS, ES⟩ := W hΓ rfl
    rw [← EΓ₀, ← proofErase_subst_with hΓ₀ WS hright ES]
    exact ⟨⟨Γ₀, _, _, hΓ₀, rfl, hright.subst henv.orderedStrong WS hΓ₀, rfl⟩,
      fun R => ⟨_, .refl, R⟩⟩
  · have ES := proofErase_const_spine hΓ (args := [α, a, M, m, b]) hr hp
    change proofErase Γ (eqRecBeforeMajor v w α a M m b) = _ at ES
    have HH : (proofErase Γ (eqRecBeforeMajor v w α a M m b)).constHead = some ``Eq.rec := by
      rw [ES]
      exact constHead_mkApps _ _
    exact (H.eq_prefix heq hs hl hcon hreg hoff hD hΓ hr).eq_head_consumer
      heq hs hreg hoff hD hΓ hr htarget ht HH

end Lean4Lean.VEnv.Strengthening
