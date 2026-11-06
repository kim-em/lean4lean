import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqChainFrontier

/-! # Actual supplied-argument consumption through a paired insertion chain

A used binder's chosen image is the specialization of its actual original
argument. Descend the argument and body component paths through the same chain
before instantiating. The original paired frame and older chain survive.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives

/-- Instantiating an actual supplied argument commutes with the entire ordered
insertion path. The body follows the path beneath a binder; after consumption
it follows the old path. The argument need not be proof-valued or closed. -/
theorem EqInsertionPath.erased_inst (blocks : EqInsertionPath) (body x : ProofShape) :
    blocks.erased (body.inst x) = (blocks.underBinder.erased body).inst (blocks.erased x) := by
  induction blocks generalizing body x with
  | nil => rfl
  | cons p blocks ih =>
    obtain ⟨n,k⟩ := p
    change EqInsertionPath.erased blocks ((body.inst x).liftN n k) = _
    rw [show (body.inst x).liftN n k = (body.liftN n (k+1)).inst (x.liftN n k) by
      simpa only [Nat.add_zero] using ProofShape.liftN_instN body x n k 0]
    exact ih (body.liftN n (k+1)) (x.liftN n k)

variable [Params]

/-- Compute a body and its actual supplied argument through the same paired
chain, then consume the used binder. Its target-image agreement is derived
from the supplied argument's computation and original chosen specialization.
The exact upper endpoint map is constructed, and the original lower frame
and older insertion chain remain available after consumption. -/
theorem EqPrefixSpecializationAt.chain_supplied_components
    (hbody : ErasedScopedPrimitiveCertificateDescent BodyStep BodyStep)
    (harg : ErasedScopedPrimitiveCertificateDescent ArgStep ArgStep)
    (hΔ : OnCtx Δ (env.IsType univs))
    (H : EqPrefixSpecializationAt (A :: Γ) Δ v w v' w' original pre (σ.cons (x.subst σ)) pending)
    (W : EqSpecializationFrame Γ Γ' Δ σ σ' ρ τ)
    (J : EqFrameInsertionChain Γ Γ' ρ τ Λ Λ' κ υ blocks)
    (hA : env.HasType univs Γ A (.sort u)) (hx : env.HasType univs Γ x A)
    (hf : env.HasType univs (A :: Γ) (VExpr.mkApps (.const ``Eq.rec [v',w']) pre) F)
    (hn : ¬ IsProof (A :: Γ) (VExpr.mkApps (.const ``Eq.rec [v',w']) pre))
    (HC : env.IsDefEqU univs (A :: Γ) (.const ``Eq.rec [v',w']) (.const ``Eq.rec [v'',w'']))
    (HA : List.Forall₂ (ScopedCompute BodyStep (proofEraseCtx (blocks.actual A :: Λ)))
      ((pre.map (proofErase (A :: Γ))).map blocks.underBinder.erased) rawBody)
    (RX : ScopedCompute ArgStep (proofEraseCtx Λ) (blocks.erased (proofErase Γ x)) rawX) :
    ∃ (pre' : List VExpr) (x' : VExpr), env.IsDefEq univs Γ x x' A ∧ blocks.erased (proofErase Γ x') = rawX ∧
      EqSpecializationFrame (A :: Γ) Γ Δ (σ.cons (x.subst σ)) σ
        (VExpr.Subst.one x') (ProofShape.Subst.one (proofErase Γ x')) ∧
      ContextSubstitution (proofEraseCtx (blocks.actual A :: Λ)) (proofEraseCtx Λ)
        (ProofShape.Subst.one rawX) ∧
      EqPrefixSpecializationAt Γ Δ v w v'' w'' original (pre'.map (·.inst x')) σ pending ∧
      env.HasType univs Γ (VExpr.mkApps (.const ``Eq.rec [v'',w'']) (pre'.map (·.inst x'))) (F.inst x') ∧
      ¬ IsProof Γ (VExpr.mkApps (.const ``Eq.rec [v'',w'']) (pre'.map (·.inst x'))) ∧
      (((pre'.map (·.inst x')).map (proofErase Γ)).map blocks.erased) = rawBody.map (·.inst rawX) ∧
      EqPrefixSpecializationAt Γ' Δ v w v'' w'' original
        ((pre'.map (·.inst x')).map (·.subst ρ)) σ' pending ∧
      ((((pre'.map (·.inst x')).map (·.subst ρ)).map (proofErase Γ')).map blocks.erased) =
        (rawBody.map (·.inst rawX)).map (·.subst υ) := by
  have hy := hx.subst henv.orderedStrong W.agree.left hΔ
  have WF := W.under_binder hΔ hA hy
  have JF := J.under_binder W hA
  obtain ⟨pre', HP, _, _, Ebody, _, HE⟩ := H.compute_insertion_chain hbody hΔ WF JF hf HC HA
  obtain ⟨x', HX, _, EX⟩ := J.compute_certificate harg W hx RX
  have WI := EqSpecializationFrame.inst W.agree.left hA HX.hasType.2
    (HX.subst henv.orderedStrong W.agree.left hΔ)
  obtain ⟨HPi, hpi, Epi⟩ := HP.frame hΔ WI HE.hasType.2
  have HPi : EqPrefixSpecializationAt Γ Δ v w v'' w'' original (pre'.map (·.inst x')) σ pending := by
    simpa only [VExpr.inst_eq, VExpr.Subst.one] using HPi
  have hpi : env.HasType univs Γ (VExpr.mkApps (.const ``Eq.rec [v'',w'']) (pre'.map (·.inst x'))) (F.inst x') := by
    simpa only [VExpr.inst_eq, VExpr.Subst.one] using hpi
  have Epi : (pre'.map (·.inst x')).map (proofErase Γ) =
      (pre'.map (proofErase (A :: Γ))).map (·.inst (proofErase Γ x')) := by
    simpa only [VExpr.inst_eq, VExpr.Subst.one, ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using Epi
  have hnpre := fun hp => hn ((isProof_congr H.1.wf HE).2 hp)
  have hni : ¬ IsProof Γ (VExpr.mkApps (.const ``Eq.rec [v'',w'']) (pre'.map (·.inst x'))) := by
    intro hp
    apply hnpre ((isProof_subst WI.target.wf WI.actual HE.hasType.2).1 ?_)
    simpa only [VExpr.subst_mkApps, VExpr.subst, VExpr.inst_eq, VExpr.Subst.one] using hp
  have EI : (((pre'.map (·.inst x')).map (proofErase Γ)).map blocks.erased) =
      rawBody.map (·.inst rawX) := by
    rw [Epi, ← Ebody, ← EX]
    simp only [List.map_map, Function.comp_def, EqInsertionPath.erased_inst]
  obtain ⟨hΛ', S, _⟩ := J.actual W
  have hAup : env.HasType univs Λ (blocks.actual A) (.sort u) := by
    simpa only [EqInsertionPath.actual_sort] using J.weak hA
  have hΛA : OnCtx (blocks.actual A :: Λ) (env.IsType univs) := ⟨S.wf, u, hAup⟩
  have EXup : proofErase Λ (blocks.actual x') = rawX := (J.erase_actual W HX.hasType.2).trans EX
  have WX : ContextSubstitution (proofEraseCtx (blocks.actual A :: Λ)) (proofEraseCtx Λ)
      (ProofShape.Subst.one (proofErase Λ (blocks.actual x'))) :=
    ContextSubstitution.of_typed S.wf (Ctx.InstN.zero.substEq hΛA (J.weak HX.hasType.2))
      (erasedSubstAgreement_one hΛA (J.weak HX.hasType.2))
  obtain ⟨Hout, _, Eout⟩ := HPi.frame hΔ W hpi
  refine ⟨pre', x', HX, EX, WI, (by intro Ψ hΨ EΨ; simpa only [EXup] using WX hΨ EΨ), HPi, hpi, hni, EI, Hout, ?_⟩
  rw [Eout, ← EI]
  simp only [List.map_map, Function.comp_def, J.erased]

/-- Start from the actual whole supplied spine, open its selected eta prefix,
compute the body and supplied argument in their actual upper scopes, and
consume the used binder. The chosen image is derived from the omitted actual
argument. The conclusion preserves the original lower assignment and older
paired chain, with exact consumed and outgoing raw vectors. -/
theorem EqPrefixSpecializationAt.eta_chain_compute_inst
    (hbody : ErasedScopedPrimitiveCertificateDescent BodyStep BodyStep)
    (harg : ErasedScopedPrimitiveCertificateDescent ArgStep ArgStep)
    (hΔ : OnCtx Δ (env.IsType univs))
    (H : EqPrefixSpecializationAt Γ Δ v w v' w' original (pre ++ x :: rest) σ pending)
    (W : EqSpecializationFrame Γ Γ' Δ σ σ' ρ τ)
    (J : EqFrameInsertionChain Γ Γ' ρ τ Λ Λ' κ υ blocks)
    (ht : env.HasType univs Δ (VExpr.mkApps (.const ``Eq.rec [v,w]) original) T)
    (hwhole : env.HasType univs Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) (pre ++ x :: rest)) F)
    (hA : env.HasType univs Γ A (.sort u))
    (hf : env.HasType univs Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre) (.forallE A B))
    (hn : ¬ IsProof Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre))
    (HC : env.IsDefEqU univs (A :: Γ) (.const ``Eq.rec [v',w']) (.const ``Eq.rec [v'',w'']))
    (HA : List.Forall₂ (ScopedCompute BodyStep (proofEraseCtx (blocks.actual A :: Λ)))
      (((pre.map VExpr.lift ++ [VExpr.bvar 0]).map (proofErase (A :: Γ))).map blocks.underBinder.erased) rawBody)
    (RX : ScopedCompute ArgStep (proofEraseCtx Λ) (blocks.erased (proofErase Γ x)) rawX) :
    ∃ (x' : VExpr) (final : List VExpr), env.IsDefEq univs Γ x x' A ∧
      EqSpecializationFrame (A :: Γ) Γ Δ (σ.cons (x.subst σ)) σ
        (VExpr.Subst.one x') (ProofShape.Subst.one (proofErase Γ x')) ∧
      ContextSubstitution (proofEraseCtx (blocks.actual A :: Λ)) (proofEraseCtx Λ)
        (ProofShape.Subst.one rawX) ∧
      EqPrefixSpecializationAt Γ Δ v w v'' w'' original final σ (rest.map (·.subst σ) ++ pending) ∧
      env.HasType univs Γ (VExpr.mkApps (.const ``Eq.rec [v'',w'']) final) (B.inst x') ∧
      ¬ IsProof Γ (VExpr.mkApps (.const ``Eq.rec [v'',w'']) final) ∧
      ((final.map (proofErase Γ)).map blocks.erased) = rawBody.map (·.inst rawX) ∧
      EqPrefixSpecializationAt Γ' Δ v w v'' w'' original (final.map (·.subst ρ)) σ'
        (rest.map (·.subst σ) ++ pending) ∧
      (((final.map (·.subst ρ)).map (proofErase Γ')).map blocks.erased) =
        (rawBody.map (·.inst rawX)).map (·.subst υ) := by
  obtain ⟨Hfresh, _, HX, _, _⟩ := H.eta_supply_frame harg.descent hΔ ht hwhole hA hf
    (ScopedCompute.refl (Step := ArgStep) (e := proofErase Γ x))
  have hx := HX.hasType.1
  have hfw : env.HasType univs (A :: Γ)
      (VExpr.mkApps (.const ``Eq.rec [v',w']) pre).lift
      (.forallE A.lift (B.liftN 1 1)) := hf.weak henv
  have EE : VExpr.mkApps (.const ``Eq.rec [v',w']) (pre.map VExpr.lift ++ [VExpr.bvar 0]) =
      .app (VExpr.mkApps (.const ``Eq.rec [v',w']) pre).lift (.bvar 0) := by
    simp only [VExpr.mkApps_append, VExpr.mkApps_cons, VExpr.mkApps_nil,
      VExpr.lift, VExpr.liftN_mkApps, VExpr.liftN]
  have hb : env.HasType univs (A :: Γ)
      (VExpr.mkApps (.const ``Eq.rec [v',w']) (pre.map VExpr.lift ++ [VExpr.bvar 0])) B := by
    rw [EE]
    simpa only [VExpr.inst_liftN_bvar] using hfw.app (HasType.bvar .zero)
  have EB := proofErase_eta_body H.1.wf hA hf hn
  rw [← EE] at EB
  have hnb : ¬ IsProof (A :: Γ)
      (VExpr.mkApps (.const ``Eq.rec [v',w']) (pre.map VExpr.lift ++ [VExpr.bvar 0])) := by
    intro hp
    rw [proofErase_eq_proof.2 hp] at EB
    cases EB
  obtain ⟨pre', x', HX', _, WI, WX, HP, hfinal, hnfinal, Efinal, Hout, Eout⟩ :=
    Hfresh.chain_supplied_components hbody harg hΔ W J hA hx hb hnb HC HA RX
  exact ⟨x', pre'.map (·.inst x'), HX', WI, WX, HP, hfinal, hnfinal, Efinal, Hout, Eout⟩

/-- A selected underfilled root either omits an actual lower supplied
argument, whose specialization is the next chosen image, or exhausts the
current lower spine and has no actual upper suffix at all. The latter case
must obtain supply from the later continuation; it is not covered by the
shared-argument consumption theorem merely because a target image is pending. -/
theorem EqPrefixSpecializationAt.chain_short_supply
    (H : EqPrefixSpecializationAt Γ Δ v w v' w' original pre σ pending)
    (hextra : extra = [] ∨ pending = []) (hk : arity ≤ pre.length + extra.length)
    (hshort : arity < original.length) (blocks : EqInsertionPath) :
    (∃ x rest, pre = pre.take arity ++ x :: rest ∧
      EqPrefixSpecializationAt Γ Δ v w v' w' original (pre.take arity) σ
        (x.subst σ :: (rest.map (·.subst σ) ++ pending)) ∧
      ((((pre.map (proofErase Γ)).map blocks.erased) ++ extra).drop arity) =
        blocks.erased (proofErase Γ x) :: (((rest.map (proofErase Γ)).map blocks.erased) ++ extra)) ∨
    (arity = pre.length ∧ extra = [] ∧ pending ≠ [] ∧
      ((((pre.map (proofErase Γ)).map blocks.erased) ++ extra).drop arity) = []) := by
  have HL := H.2.2.length_eq
  simp only [List.length_append, List.length_map] at HL
  have hkpre : arity ≤ pre.length := by
    rcases hextra with rfl | rfl <;> simp only [List.length_nil] at * <;> omega
  cases E : pre.drop arity with
  | nil =>
    have EL := congrArg List.length E
    simp only [List.length_drop, List.length_nil] at EL
    have harity : arity = pre.length := by omega
    have hp : pending ≠ [] := by intro hp; simp only [hp, List.length_nil] at HL; omega
    have hext : extra = [] := hextra.resolve_right hp
    refine .inr ⟨harity, hext, hp, ?_⟩
    simp only [hext, harity, List.append_nil, ← List.map_drop, List.drop_length, List.map_nil]
  | cons x rest =>
    have EP : pre = pre.take arity ++ x :: rest := by rw [← E, List.take_append_drop]
    refine .inl ⟨x, rest, EP, ?_, ?_⟩
    · simpa only [E, List.map_cons, List.cons_append] using H.take arity
    · rw [List.drop_append_of_le_length (by simpa only [List.length_map] using hkpre)]
      simp only [← List.map_drop, E, List.map_cons, List.cons_append]

end Lean4Lean.VEnv.Strengthening
