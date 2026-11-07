import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqPendingCountedReadout

/-! # Realize a returned body with its source application typing

Read the original body computation before applying its actual return square.
The resulting lower function has the exact returned erasure, while semantic
source equalities restore typing of its whole waiting application. No native
body path is transported by substitution.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private isProof_congr
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
open private nonproof_spine_head
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureRecoveredEqComputedPrefix
variable [Params]

/-- Realize the whole original body path, then apply the actual agreeing return
square to its source equality. The returned lower function has precisely the
substituted raw endpoint. Only the semantic equality and erasure are mapped;
no substituted native computation is asserted. -/
theorem EqSupplyInsertionSquare.compute_source_return
    (hstep : ErasedScopedPrimitiveCertificateDescent Step Step)
    (hΔ : OnCtx Δ (env.IsType univs))
    (Q : EqSupplyInsertionSquare Γ Γ' Δ σ σ' ρ τ Λ Λ' κ υ incoming outgoing)
    (he : env.HasType univs Γ e T)
    (R : ScopedCompute Step (proofEraseCtx Λ) (incoming.erased (proofErase Γ e)) raw) :
    ∃ f, env.IsDefEq univs Γ' (e.subst ρ) f (T.subst ρ) ∧
      outgoing.erased (proofErase Γ' f) = raw.subst υ := by
  have W := EqSpecializationFrame.of_conversion hΔ Q.lower.agree.left (.refl Q.lower.actual.wf)
  obtain ⟨e', HE, _, EE⟩ := Q.source.compute_certificate hstep W he R
  have HE' := HE.subst henv.orderedStrong Q.lower.actual Q.lower.target.wf
  refine ⟨e'.subst ρ, HE', ?_⟩
  rw [proofErase_subst_with Q.lower.target.wf Q.lower.actual HE.hasType.2 Q.lower.erase]
  exact (Q.erased (proofErase Γ e')).symm.trans (congrArg (·.subst υ) EE)

/-- The original instantiated-body application typing survives whole body
computation and actual waiting-argument computation. The same returned function
has the exact raw endpoint, its original mapped head type, and nonproofness.
The source application premise is retained explicitly rather than inferred from
chosen-image agreement or individual typings of waiting terms. -/
theorem EqSupplyInsertionSquare.compute_waiting_application {previous actual : List VExpr}
    (hstep : ErasedScopedPrimitiveCertificateDescent Step Step)
    (hΔ : OnCtx Δ (env.IsType univs))
    (Q : EqSupplyInsertionSquare Γ Γ' Δ σ σ' ρ τ Λ Λ' κ υ incoming outgoing)
    (he : env.HasType univs Γ e T)
    (R : ScopedCompute Step (proofEraseCtx Λ) (incoming.erased (proofErase Γ e)) raw)
    (Hargs : List.Forall₂ (env.IsDefEqU univs Γ') previous actual)
    (happ : env.HasType univs Γ' (VExpr.mkApps (e.subst ρ) previous) F)
    (hn : ¬ IsProof Γ' (VExpr.mkApps (e.subst ρ) previous)) :
    ∃ f, env.IsDefEq univs Γ' (e.subst ρ) f (T.subst ρ) ∧
      env.IsDefEq univs Γ' (VExpr.mkApps (e.subst ρ) previous) (VExpr.mkApps f actual) F ∧
      ¬ IsProof Γ' (VExpr.mkApps f actual) ∧ ¬ IsProof Γ' f ∧
      outgoing.erased (proofErase Γ' f) = raw.subst υ := by
  obtain ⟨f, HF, EF⟩ := Q.compute_source_return hstep hΔ he R
  have HE := (IsDefEqU.mkApps_args Q.lower.target.wf HF.toU Hargs happ).of_l
    henv Q.lower.target.wf happ
  have hn' : ¬ IsProof Γ' (VExpr.mkApps f actual) :=
    fun hp => hn ((isProof_congr Q.lower.target.wf HE).2 hp)
  exact ⟨f, HF, HE, hn', nonproof_spine_head Q.lower.target.wf HE.hasType.2 hn', EF⟩

/-- A consumed lambda supplies the whole application typing needed for source
return. Beta at the actual computed argument and congruence of the waiting
arguments connect the original typed application to the realized body endpoint.
The body computation stays beneath the original domain. -/
theorem EqSupplyInsertionSquare.compute_consumed_application {previous actual : List VExpr}
    (hstep : ErasedScopedPrimitiveCertificateDescent Step Step)
    (hΔ : OnCtx Δ (env.IsType univs))
    (Q : EqSupplyInsertionSquare (A :: Γ) Γ Δ (σ.cons y) σ
      (VExpr.Subst.one actualX) (ProofShape.Subst.one (proofErase Γ actualX))
      (blocks.actual A :: Λ) Λ (VExpr.Subst.one (blocks.actual actualX))
      (ProofShape.Subst.one rawX) blocks.underBinder blocks)
    (hA : env.HasType univs Γ A (.sort u))
    (he : env.HasType univs (A :: Γ) e T)
    (HX : env.IsDefEq univs Γ x actualX A)
    (R : ScopedCompute Step (proofEraseCtx (blocks.actual A :: Λ))
      (blocks.underBinder.erased (proofErase (A :: Γ) e)) raw)
    (Hargs : List.Forall₂ (env.IsDefEqU univs Γ) previous actual)
    (happ : env.HasType univs Γ (VExpr.mkApps (.app (.lam A e) x) previous) F)
    (hn : ¬ IsProof Γ (VExpr.mkApps (.app (.lam A e) x) previous)) :
    ∃ f, env.IsDefEq univs Γ (e.inst actualX) f (T.inst actualX) ∧
      env.IsDefEq univs Γ (VExpr.mkApps (.app (.lam A e) x) previous)
        (VExpr.mkApps f actual) F ∧
      ¬ IsProof Γ (VExpr.mkApps f actual) ∧ ¬ IsProof Γ f ∧
      blocks.erased (proofErase Γ f) = raw.inst rawX := by
  obtain ⟨f, HF, EF⟩ := Q.compute_source_return hstep hΔ he R
  have HF : env.IsDefEq univs Γ (e.inst actualX) f (T.inst actualX) := by
    simpa only [VExpr.inst_eq, VExpr.Subst.one] using HF
  have Hhead := (IsDefEq.appDF (HasType.lam hA he) HX).toU.trans henv Q.lower.target.wf
    (IsDefEq.beta he HX.hasType.2).toU
  have HE := (IsDefEqU.mkApps_args Q.lower.target.wf
    (Hhead.trans henv Q.lower.target.wf HF.toU) Hargs happ).of_l henv Q.lower.target.wf happ
  have hn' : ¬ IsProof Γ (VExpr.mkApps f actual) :=
    fun hp => hn ((isProof_congr Q.lower.target.wf HE).2 hp)
  exact ⟨f, HF, HE, hn', nonproof_spine_head Q.lower.target.wf HE.hasType.2 hn',
    by simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using EF⟩

/-- Derive a consumed source return from the actual body and argument paths.
The original whole lambda application supplies dependent typing; the stored
chosen argument vector supplies its image agreement. Both are preserved in the
returned function and waiting vector. Upper extras keep their actual paths.
This is a local consumption theorem, not recursive endpoint recognition. -/
theorem EqArgumentSupplyAt.compute_consumed_source
    (hbody : ErasedScopedPrimitiveCertificateDescent BodyStep BodyStep)
    (hargs : ErasedScopedPrimitiveCertificateDescent ArgStep ArgStep)
    (hΔ : OnCtx Δ (env.IsType univs))
    (H : EqArgumentSupplyAt Γ Δ σ (y :: supplied) (x :: previous))
    (W : EqSpecializationFrame Γ Γ' Δ σ σ' ρ τ)
    (J : EqFrameInsertionChain Γ Γ' ρ τ Λ Λ' κ υ blocks)
    (hA : env.HasType univs Γ A (.sort u))
    (he : env.HasType univs (A :: Γ) e T)
    (hx : env.HasType univs Γ x A)
    (happ : env.HasType univs Γ (VExpr.mkApps (.app (.lam A e) x) previous) F)
    (hn : ¬ IsProof Γ (VExpr.mkApps (.app (.lam A e) x) previous))
    (RB : ScopedCompute BodyStep (proofEraseCtx (blocks.actual A :: Λ))
      (blocks.underBinder.erased (proofErase (A :: Γ) e)) rawBody)
    (RA : List.Forall₂ (ScopedCompute ArgStep (proofEraseCtx Λ))
      ((((x :: previous).map (proofErase Γ)).map blocks.erased) ++ extra) (rawX :: rawRest)) :
    ∃ actualX actual rawExtra f,
      env.IsDefEq univs Γ x actualX A ∧
      blocks.erased (proofErase Γ actualX) = rawX ∧
      EqArgumentSupplyAt Γ Δ σ supplied actual ∧
      List.Forall₂ (env.IsDefEqU univs Γ) previous actual ∧
      ((actual.map (proofErase Γ)).map blocks.erased) ++ rawExtra = rawRest ∧
      List.Forall₂ (ScopedCompute ArgStep (proofEraseCtx Λ)) extra rawExtra ∧
      EqSupplyInsertionSquare (A :: Γ) Γ Δ (σ.cons y) σ
        (VExpr.Subst.one actualX) (ProofShape.Subst.one (proofErase Γ actualX))
        (blocks.actual A :: Λ) Λ (VExpr.Subst.one (blocks.actual actualX))
        (ProofShape.Subst.one rawX) blocks.underBinder blocks ∧
      env.IsDefEq univs Γ (e.inst actualX) f (T.inst actualX) ∧
      env.IsDefEq univs Γ (VExpr.mkApps (.app (.lam A e) x) previous)
        (VExpr.mkApps f actual) F ∧
      ¬ IsProof Γ (VExpr.mkApps f actual) ∧ ¬ IsProof Γ f ∧
      blocks.erased (proofErase Γ f) = rawBody.inst rawX := by
  obtain ⟨args, rawExtra, HS, HE, EE, RX⟩ := H.chain_compute_prefix hargs hΔ W J RA
  cases args with
  | nil => cases HE
  | cons actualX actual =>
    obtain ⟨EX, ER⟩ := List.cons.inj EE
    cases HE with
    | cons HX Hrest =>
      have HX := HX.of_l henv W.actual.wf hx
      obtain ⟨_, Htail⟩ := HS.consume_head hΔ W.agree.left hA HX.hasType.2
      have HY := (List.forall₂_cons.mp HS.2).1.of_r henv hΔ
        (HX.hasType.2.subst henv.orderedStrong W.agree.left hΔ)
      have Q := EqSupplyInsertionSquare.of_chosen_argument hΔ W J hA HX.hasType.2 HY
      rw [EX] at Q
      obtain ⟨f, HF, Hwhole, hnwhole, hnf, EF⟩ :=
        Q.compute_consumed_application hbody hΔ hA he HX RB Hrest happ hn
      exact ⟨actualX, actual, rawExtra, f, HX, EX, Htail, Hrest, ER, RX, Q,
        HF, Hwhole, hnwhole, hnf, EF⟩

/-- Restore and rejoin a returned pending history using a realized source
function. Its whole application typing is derived from the original body path
and waiting source equalities. The path needed for domain alignment is reflexive
at the exact realized endpoint; no new native return-path premise is required.
Recursive construction of the returned history and its endpoint equation is
still required, as is the original instantiated-body application typing. -/
theorem EqPendingSupplyHistory.realized_source_rejoin
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hstep : ErasedScopedPrimitiveCertificateDescent Step Step)
    (hΔ : OnCtx Δ (env.IsType univs))
    (Q : EqSupplyInsertionSquare sourceΓ Γ₀ Δ sourceσ σ₀ ρ τ sourceΛ Λ₀ κ υ
      sourceBlocks blocks₀)
    (he : env.HasType univs sourceΓ e T)
    (R : ScopedCompute Step (proofEraseCtx sourceΛ)
      (sourceBlocks.erased (proofErase sourceΓ e)) raw)
    (O : EqPendingSupplyHistory D Δ baseΓ baseΛ baseσ baseBlocks basePending baseTarget baseMap
      Γ₀ Λ₀ σ₀ blocks₀ pending₀ oldTarget oldMap oldPlug oldChosen oldDepth)
    (H : EqPendingSupplyHistory D Δ Γ₀ Λ₀ σ₀ blocks₀ (supplied ++ pending₀) Ψ₀ υ₀
      Γ Λ σ blocks pending Ψ χ plug chosen depth)
    (ER : raw.subst υ = plug body)
    (HS : EqArgumentSupplyAt Γ₀ Δ σ₀ supplied actual)
    (Hargs : List.Forall₂ (env.IsDefEqU univs Γ₀) previous actual)
    (hextra : extra = [] ∨ pending₀ = [])
    (happ : env.HasType univs Γ₀ (VExpr.mkApps (e.subst ρ) previous) F)
    (hn : ¬ IsProof Γ₀ (VExpr.mkApps (e.subst ρ) previous))
    (hd : 0 < depth) :
    ∃ (f : VExpr) (returned : ProofShape → ProofShape)
      (joinedTarget : List ProofShape) (joinedMap : ProofShape.Subst),
      env.IsDefEq univs Γ₀ (e.subst ρ) f (T.subst ρ) ∧
      env.IsDefEq univs Γ₀ (VExpr.mkApps (e.subst ρ) previous) (VExpr.mkApps f actual) F ∧
      ¬ IsProof Γ₀ (VExpr.mkApps f actual) ∧ ¬ IsProof Γ₀ f ∧
      blocks₀.erased (proofErase Γ₀ f) = plug body ∧
      EqPendingSupplyHistory D Δ Γ₀ Λ₀ σ₀ blocks₀ pending₀ Ψ₀ υ₀
        Γ Λ σ blocks pending Ψ χ returned chosen depth ∧
      EqPendingSupplyHistory D Δ baseΓ baseΛ baseσ baseBlocks basePending baseTarget baseMap
        Γ Λ σ blocks pending joinedTarget joinedMap (fun b => oldPlug (returned b))
        (oldChosen+chosen) (oldDepth+depth) ∧
      ∀ b, returned b = ProofShape.mkApps (plug b)
        (((actual.map (proofErase Γ₀)).map blocks₀.erased) ++ extra) := by
  obtain ⟨f, HF, HE, hn', hnf, EF⟩ := Q.compute_waiting_application hstep hΔ he R Hargs happ hn
  have EF := EF.trans ER
  have W := EqSpecializationFrame.of_conversion hΔ Q.lower.target (.refl Q.lower.target.wf)
  have RF : ScopedCompute (PiInertStage D 0) (proofEraseCtx Λ₀)
      (blocks₀.erased (proofErase Γ₀ f)) (plug body) := by
    rw [EF]; exact .refl
  obtain ⟨returned, Ξ, ω, HR, Hjoined, EW⟩ := EqPendingSupplyHistory.restore_rejoin
    heq hs (pi_inert_stage_certificate_descent heq hs 0) O H W Q.target HS hextra HE.hasType.2 RF hd
  exact ⟨f, returned, Ξ, ω, HF, HE, hn', hnf, EF, HR, Hjoined, EW⟩

end Lean4Lean.VEnv.Strengthening
