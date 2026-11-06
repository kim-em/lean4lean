import Lean4Lean.Theory.Typing.Strengthening.ProofErasureRecoveredEqComputedPrefix

/-! # Lower a singleton before specializing a fresh Eq argument

The source prefix may live in a different context from its completed target.
Remove unused binders at the source, decode the generated family there, and
substitute only the resulting semantic index equality. In particular, a
singleton consuming a fresh eta argument can be read at its actual argument.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private ProofShape.const_spine_inj
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRecordAlignment
open private erased_carrier_recovered_singleton_rule_descent
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitiveRuleDescent
variable [Params]

/-- A recovered singleton on a typed source prefix forces index equality in
every typed substituted completion. The raw guard is never substituted. -/
theorem proofErase_recovered_singleton_eq_prefix_specialize
    (heq : env.HasCanonicalEq) (hstep : ErasedScopedPrimitiveDescent Step)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : VExpr.WF env univs Γ (VExpr.mkApps (.const ``Eq.rec [v,w]) pre))
    (hΔ : OnCtx Δ (env.IsType univs))
    (ht : env.HasType univs Δ (eqRecBeforeMajor v w α a M m b) T)
    (WS : Ctx.SubstEq env univs Δ σ σ Γ)
    (Eargs : pre.map (·.subst σ) ++ pending = [α,a,M,m,b])
    (H : SingletonPrimitiveWith (fun Ξ => CarrierRecoveredCompare Step Ξ true) (proofEraseCtx Γ)
      (ProofShape.mkApps (.const ``Eq.rec [v,w]) (pre.map (proofErase Γ))) out) :
    env.IsDefEq univs Δ a b α := by
  generalize ES : ProofShape.mkApps (.const ``Eq.rec [v,w]) (pre.map (proofErase Γ)) = source at H
  cases H with
  | @intro C raw domains result V ha hcalc HG =>
    obtain ⟨hn, hl, hp⟩ := ProofShape.const_spine_inj ES
    rw [← hp] at hcalc HG
    have hlen : pre.length = C.arity := by simpa only [← hp, List.length_map] using ha
    have hf' := hf
    rw [hn, hl] at hf'
    obtain ⟨program, hg, _, HF⟩ := V.realizeWith heq hΓ hlen hf' hcalc HG
    rw [← hl] at hg HF
    exact recovered_eq_prefix_completion heq hstep V.registered hn.symm
      (hl.symm ▸ V.zero) (hl.symm ▸ V.layout_eq) (hl.symm ▸ V.elim_eq)
      (hl.symm ▸ V.levels_wf) hΔ ht hΓ hg hf HF WS Eargs

/-- The completed target arguments need only be pointwise definitionally
equal to the specialized source arguments. This retains the original target
indices after computation of the supplied source prefix. -/
theorem proofErase_recovered_singleton_eq_prefix_specialize_congr
    (heq : env.HasCanonicalEq) (hstep : ErasedScopedPrimitiveDescent Step)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : VExpr.WF env univs Γ (VExpr.mkApps (.const ``Eq.rec [v,w]) pre))
    (hΔ : OnCtx Δ (env.IsType univs))
    (ht : env.HasType univs Δ (eqRecBeforeMajor v w α a M m b) T)
    (WS : Ctx.SubstEq env univs Δ σ σ Γ)
    (HA : List.Forall₂ (env.IsDefEqU univs Δ) [α,a,M,m,b] (pre.map (·.subst σ) ++ pending))
    (H : SingletonPrimitiveWith (fun Ξ => CarrierRecoveredCompare Step Ξ true) (proofEraseCtx Γ)
      (ProofShape.mkApps (.const ``Eq.rec [v,w]) (pre.map (proofErase Γ))) out) :
    env.IsDefEq univs Δ a b α := by
  generalize EE : pre.map (·.subst σ) ++ pending = completed at HA
  cases HA with | cons Hα HA =>
    cases HA with | cons Ha HA =>
      cases HA with | cons HM HA =>
        cases HA with | cons Hm HA =>
          cases HA with | cons Hb HA =>
            cases HA
            have hall := List.Forall₂.cons Hα (.cons Ha (.cons HM (.cons Hm (.cons Hb .nil))))
            have hc := VExpr.WF.of_mkApps henv.orderedStrong hΔ (show
              VExpr.WF env univs Δ (VExpr.mkApps (.const ``Eq.rec [v,w]) [α,a,M,m,b]) from ⟨_, ht⟩)
            have HE := IsDefEqU.mkApps_args hΔ hc hall ht
            have ht' := (HE.of_l henv hΔ ht).hasType.2
            have HR := proofErase_recovered_singleton_eq_prefix_specialize heq hstep
              hΓ hf hΔ ht' WS EE H
            obtain ⟨_, _, _, ha, _, _, _⟩ := eqRecBeforeMajor_typings henv heq hΔ ⟨_, ht⟩
            exact ((Ha.trans henv hΔ HR.toU).trans henv hΔ Hb.symm).of_l henv hΔ ha

/-- Source descent and target specialization can be performed in that order.
The target substitution need not interpret any of the removed upper binders. -/
theorem proofErase_recovered_singleton_eq_prefix_descend_specialize
    (heq : env.HasCanonicalEq)
    (hstep : ErasedScopedPrimitiveCertificateDescent Step Step)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.LiftN count offset Γ Γ')
    (hf : env.HasType univs Γ (VExpr.mkApps (.const ``Eq.rec [v,w]) pre) F)
    (hn : ¬ IsProof Γ (VExpr.mkApps (.const ``Eq.rec [v,w]) pre))
    (hΔ : OnCtx Δ (env.IsType univs))
    (ht : env.HasType univs Δ (eqRecBeforeMajor v w α a M m b) T)
    (WS : Ctx.SubstEq env univs Δ σ σ Γ)
    (Eargs : pre.map (·.subst σ) ++ pending = [α,a,M,m,b])
    (H : CarrierRecoveredSingletonPrimitive Step (proofEraseCtx Γ')
      ((proofErase Γ (VExpr.mkApps (.const ``Eq.rec [v,w]) pre)).liftN count offset) out) :
    env.IsDefEq univs Δ a b α := by
  obtain ⟨_, _, HL, _⟩ := erased_carrier_recovered_singleton_rule_descent heq hstep
    hΓ hΓ' W hf H
  rw [proofErase_const_spine hΓ hf hn] at HL
  exact proofErase_recovered_singleton_eq_prefix_specialize heq hstep.descent
    hΓ ⟨_, hf⟩ hΔ ht WS Eargs HL.2

/-- A singleton at an Eq eta body, including its newly opened argument,
forces the original completed equation below the ambient unused binders.
The fresh binder is specialized at the actual next argument only after the
singleton has descended. No raw substitution closure is required. -/
theorem proofErase_recovered_singleton_eq_fresh_eta_descend
    (heq : env.HasCanonicalEq)
    (hstep : ErasedScopedPrimitiveCertificateDescent Step Step)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.LiftN count offset Γ Γ')
    (hA : env.HasType univs Γ A (.sort u))
    (hf : env.HasType univs Γ (VExpr.mkApps (.const ``Eq.rec [v,w]) pre) (.forallE A B))
    (hn : ¬ IsProof Γ (VExpr.mkApps (.const ``Eq.rec [v,w]) pre))
    (hx : env.HasType univs Γ x A)
    (ht : env.HasType univs Γ (eqRecBeforeMajor v w α a M m b) T)
    (Eargs : pre ++ x :: pending = [α,a,M,m,b])
    (H : CarrierRecoveredSingletonPrimitive Step
      (proofEraseCtx (A.liftN count offset :: Γ'))
      (.app (((ProofShape.mkApps (.const ``Eq.rec [v,w]) (pre.map (proofErase Γ))).liftN count offset).liftN 1)
        (etaArgument u)) out) :
    env.IsDefEq univs Γ a b α := by
  let fresh := pre.map VExpr.lift ++ [.bvar 0]
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  have hΓA' : OnCtx (A.liftN count offset :: Γ') (env.IsType univs) :=
    ⟨hΓ', u, hA.weakN henv W⟩
  have EE : VExpr.mkApps (.const ``Eq.rec [v,w]) fresh =
      .app (VExpr.mkApps (.const ``Eq.rec [v,w]) pre).lift (.bvar 0) := by
    simp only [fresh, VExpr.mkApps_append, VExpr.mkApps_cons, VExpr.mkApps_nil,
      VExpr.lift, VExpr.liftN_mkApps, VExpr.liftN]
  have hfw : env.HasType univs (A :: Γ)
      (VExpr.mkApps (.const ``Eq.rec [v,w]) pre).lift
      (.forallE A.lift (B.liftN 1 1)) := hf.weak henv
  have hbody : env.HasType univs (A :: Γ) (VExpr.mkApps (.const ``Eq.rec [v,w]) fresh) B := by
    rw [EE]
    simpa only [VExpr.inst_liftN_bvar] using hfw.app (HasType.bvar .zero)
  have EB := proofErase_eta_body hΓ hA hf hn
  rw [proofErase_const_spine hΓ hf hn, ← EE] at EB
  have hnb : ¬ IsProof (A :: Γ) (VExpr.mkApps (.const ``Eq.rec [v,w]) fresh) := by
    intro hp
    rw [proofErase_eq_proof.2 hp] at EB
    cases EB
  have HL : CarrierRecoveredSingletonPrimitive Step
      (proofEraseCtx (A.liftN count offset :: Γ'))
      ((proofErase (A :: Γ) (VExpr.mkApps (.const ``Eq.rec [v,w]) fresh)).liftN count (offset+1)) out := by
    rw [EB]
    simp only [ProofShape.liftN, etaArgument_liftN]
    rw [← ProofShape.liftN_comm _ count 1 offset 0 (Nat.zero_le _)]
    exact H
  have WS : Ctx.SubstEq env univs Γ (VExpr.Subst.id.cons x) (VExpr.Subst.id.cons x) (A :: Γ) :=
    .cons (Ctx.SubstEq.id henv.ordered hΓ) hA (by
      change env.HasType univs Γ x (A.subst VExpr.Subst.id)
      simpa only [VExpr.subst_id] using hx)
  apply proofErase_recovered_singleton_eq_prefix_descend_specialize heq hstep
    hΓA hΓA' W.succ hbody hnb hΓ ht WS (pending := pending) _ HL
  have Ezero : VExpr.Subst.id.cons x 0 = x := rfl
  simpa only [fresh, List.map_append, List.map_map, Function.comp_def,
    VExpr.lift_subst_cons, VExpr.subst_id, List.map_id_fun', id,
    List.map_cons, List.map_nil, VExpr.subst, Ezero, List.append_assoc,
    List.cons_append, List.nil_append] using Eargs

end Lean4Lean.VEnv.Strengthening
