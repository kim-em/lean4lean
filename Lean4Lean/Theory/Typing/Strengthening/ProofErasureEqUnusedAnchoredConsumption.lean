import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqAnchoredPendingHistory

/-! # Consume actual unused binders with anchored histories

An unused upper binder has no chosen lower image. Its actual interpreted
argument nevertheless gives the concrete upper substitution square. All lower
assignments stay fixed, and waiting upper extras require no lower realization.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private typed_lambda_readout typed_lambda_argument_map
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqRetainedFrameProgress
open private typed_spine_head
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedSpineCut
open private actual_id_liftN raw_id_liftN
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqPendingCountedReadout
variable [Params]

/-- Realize the actual interpreted argument of an unused upper binder. The
lower substitution is identity and the outgoing insertion path drops precisely
that upper binder. No chosen target inhabitant or exact proof-argument erasure
is required; erased substitution agreement is the appropriate evidence. -/
theorem EqSupplyInsertionSquare.unused_argument
    (hΔ : OnCtx Δ (env.IsType univs))
    (W : EqSpecializationFrame Γ Γ' Δ σ σ' ρ τ)
    (J : EqFrameInsertionChain Γ Γ' ρ τ Λ Λ' κ υ blocks)
    (hA : env.HasType univs Λ A (.sort u))
    (WX : ContextSubstitution (proofEraseCtx (A :: Λ)) (proofEraseCtx Λ)
      (ProofShape.Subst.one rawX)) :
    ∃ x, env.HasType univs Λ x A ∧
      ErasedSubstAgreement (A :: Λ) Λ (VExpr.Subst.one x) (ProofShape.Subst.one rawX) ∧
      EqSupplyInsertionSquare Γ Γ Δ σ σ VExpr.Subst.id ProofShape.Subst.id
        (A :: Λ) Λ (VExpr.Subst.one x) (ProofShape.Subst.one rawX) (blocks ++ [(1,0)]) blocks := by
  have Q := EqSupplyInsertionSquare.source_identity hΔ W J
  obtain ⟨x, hx, _, EX⟩ := WX.realize_one ⟨Q.target_wf, u, hA⟩
  refine ⟨x, hx, EX, Q.lower, ?_, Q.target, Q.target_wf,
    Ctx.InstN.zero.substEq ⟨Q.target_wf, u, hA⟩ hx, EX, ?_, ?_⟩
  · simpa only [VExpr.subst_id, VExpr.id_lift, ProofShape.Subst.id_lift] using
      Q.source.insert_domain Q.lower hA
  · intro e
    simp only [EqInsertionPath.actual_snoc, VExpr.Subst.one, VExpr.lift_subst_cons, VExpr.subst_id]
  · intro e
    simp only [EqInsertionPath.erased_snoc, ProofShape.Subst.one, ProofShape.lift_subst_cons,
      ProofShape.subst_id]

/-- Read an actual unused-lambda suffix with its original body scope and
primitive-cost split. Consumption derives the concrete upper square from the
actual computed argument path, while retaining every raw waiting argument.
This local readout does not require a continuation minimum. -/
theorem unused_counted_lambda_readout
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΔ : OnCtx Δ (env.IsType univs))
    (W : EqSpecializationFrame Γ Γ' Δ σ σ' ρ τ)
    (J : EqFrameInsertionChain Γ Γ' ρ τ Λ Λ' κ υ blocks)
    (hA : env.HasType univs Λ A (.sort u))
    (HT : TypedSource (proofEraseCtx Λ)
      (ProofShape.mkApps (.lam (proofErase Λ A) body) args))
    (R : ScopedComputeCount (PiInertStage D n) cost (proofEraseCtx Λ)
      (ProofShape.mkApps (.lam (proofErase Λ A) body) args) endpoint) :
    TypedSource (proofEraseCtx (A :: Λ)) body ∧ (
      (∃ rawA' body' args' cd cb ca m,
        cd+cb+ca ≤ cost ∧ endpoint = ProofShape.mkApps (.lam rawA' body') args' ∧
        ScopedComputeCount (PiInertStage D n) cd (proofEraseCtx Λ) (proofErase Λ A) rawA' ∧
        ScopedComputeCount (PiInertStage D m) cb (proofEraseCtx (A :: Λ)) body body' ∧
        ScopedArgumentsCount (PiInertStage D n) (proofEraseCtx Λ) ca args args') ∨
      (∃ x rawX rawRest rawA' body' cd cb ca cs m,
        cd+cb+ca+cs ≤ cost ∧ env.HasType univs Λ x A ∧
        ErasedSubstAgreement (A :: Λ) Λ (VExpr.Subst.one x) (ProofShape.Subst.one rawX) ∧
        EqSupplyInsertionSquare Γ Γ Δ σ σ VExpr.Subst.id ProofShape.Subst.id
          (A :: Λ) Λ (VExpr.Subst.one x) (ProofShape.Subst.one rawX) (blocks ++ [(1,0)]) blocks ∧
        ScopedComputeCount (PiInertStage D n) cd (proofEraseCtx Λ) (proofErase Λ A) rawA' ∧
        ScopedComputeCount (PiInertStage D m) cb (proofEraseCtx (A :: Λ)) body body' ∧
        ScopedArgumentsCount (PiInertStage D n) (proofEraseCtx Λ) ca args (rawX :: rawRest) ∧
        TypedSource (proofEraseCtx Λ) (ProofShape.mkApps (body'.inst rawX) rawRest) ∧
        ScopedComputeCount (PiInertStage D n) cs (proofEraseCtx Λ)
          (ProofShape.mkApps (body'.inst rawX) rawRest) endpoint)) := by
  have HTlam := typed_spine_head HT
  have HTbody := (ScopedHole.lamBody (proofErase Λ A) .hole).typed HTlam
  refine ⟨HTbody, ?_⟩
  rcases R.pi_inert_lambda_spine_or_beta with
    ⟨rawA', body', args', cf, ca, hc, EO, RF, RX⟩ |
    ⟨rawA', body', rawX, rawRest, cf, ca, cs, hc, RF, RX, RS⟩
  · obtain ⟨v, cd, cb, m, _, hsplit, RD, RB⟩ := typed_lambda_readout heq hs HTlam RF
    exact .inl ⟨rawA', body', args', cd, cb, ca, m, by omega, EO, RD, RB, RX⟩
  · obtain ⟨v, cd, cb, m, _, hsplit, RD, RB⟩ := typed_lambda_readout heq hs HTlam RF
    have WX : ContextSubstitution (proofEraseCtx (A :: Λ)) (proofEraseCtx Λ)
        (ProofShape.Subst.one rawX) := typed_lambda_argument_map heq hs HT RX
    obtain ⟨x, hx, EX, Q⟩ := EqSupplyInsertionSquare.unused_argument hΔ W J hA WX
    have Rbeta : ScopedComputeCount (PiInertStage D n) 0 (proofEraseCtx Λ)
        (ProofShape.mkApps (.lam rawA' body') (rawX :: rawRest))
        (ProofShape.mkApps (body'.inst rawX) rawRest) := by
      simpa only [ProofShape.mkApps] using
        (ScopedComputeCount.beta (Step := PiInertStage D n)
          (BetaRed.beta (A := rawA') (b := body') (a := rawX))).mkApps
          (ScopedArgumentsCount.refl (args := rawRest))
    have HTnext := HT.pi_inert_compute heq hs ((RF.mkApps RX).trans Rbeta).forget
    exact .inr ⟨x, rawX, rawRest, rawA', body', cd, cb, ca, cs, m,
      by omega, hx, EX, Q, RD, RB, RX, HTnext, RS⟩

/-- Extra upper arguments can be attached once the enclosing chosen vector is
empty. The original lower source application and its body path stay unchanged;
no lower representatives or typings are invented for these upper extras. -/
theorem EqRetainedSourceAnchor.append_extra
    (H : EqRetainedSourceAnchor D Γ Λ Δ σ blocks A y [] remaining body args)
    (extra : List ProofShape) :
    EqRetainedSourceAnchor D Γ Λ Δ σ blocks A y [] remaining body (args ++ extra) := by
  obtain ⟨hΓ, e, T, supplied, actual, oldExtra, F, n, he, happ, hn, HS, EP, _, ER, RB⟩ := H
  refine ⟨hΓ, e, T, supplied, actual, oldExtra ++ extra, F, n,
    he, happ, hn, HS, EP, .inr rfl, ?_, RB⟩
  rw [← ER, List.append_assoc]

/-- Attach waiting upper extras to the outer frame of a positive completed
history, preserving every source anchor. The chosen pending vector is empty;
this operation needs no lower function whose erasure includes the extras. -/
theorem EqAnchoredPendingHistory.append_outer_extra
    (H : EqAnchoredPendingHistory D Δ Γ₀ Λ₀ σ₀ blocks₀ [] Ψ₀ υ₀
      Γ Λ σ blocks pending Ψ υ plug body chosen depth)
    (extra : List ProofShape) (hd : 0 < depth) :
    ∃ plug', EqAnchoredPendingHistory D Δ Γ₀ Λ₀ σ₀ blocks₀ [] Ψ₀ υ₀
      Γ Λ σ blocks pending Ψ υ plug' body chosen depth ∧
      ∀ e, plug' e = ProofShape.mkApps (plug e) extra := by
  induction H with
  | base => omega
  | @retained Γ Λ σ blocks pending Ψ υ plug rawA body args chosen depth A u y n cd remaining H hA hy RD HA ih =>
    by_cases hz : depth = 0
    · subst depth
      cases H with
      | base =>
        refine ⟨_, EqAnchoredPendingHistory.retained (args := args ++ extra)
          .base hA hy RD (HA.append_extra extra), ?_⟩
        intro e; exact ProofShape.mkApps_append _ _ _
    · obtain ⟨plug', HR, EW⟩ := ih (by omega)
      exact ⟨_, EqAnchoredPendingHistory.retained HR hA hy RD HA,
        fun e => EW (ProofShape.mkApps (.lam rawA e) args)⟩
  | @unused Γ Λ σ blocks Ψ υ plug rawA body args chosen depth A u n cd H hA RD ih =>
    by_cases hz : depth = 0
    · subst depth
      cases H with
      | base =>
        refine ⟨_, EqAnchoredPendingHistory.unused (args := args ++ extra) .base hA RD, ?_⟩
        intro e; exact ProofShape.mkApps_append _ _ _
    · obtain ⟨plug', HR, EW⟩ := ih (by omega)
      exact ⟨_, EqAnchoredPendingHistory.unused HR hA RD,
        fun e => EW (ProofShape.mkApps (.lam rawA e) args)⟩

/-- An upper-only scope change preserves the literal chosen lower prefix,
its type and nonproofness. Its inserted raw vector follows the actual upper
substitution, which may consume a binder and need not be identity. -/
theorem EqSupplyInsertionSquare.lower_identity_prefix
    (hΔ : OnCtx Δ (env.IsType univs))
    (Q : EqSupplyInsertionSquare Γ Γ' Δ σ σ' VExpr.Subst.id ProofShape.Subst.id
      Λ Λ' κ υ incoming outgoing)
    (H : EqPrefixSpecializationAt Γ Δ v w v' w' original pre σ pending)
    (hf : env.HasType univs Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre) F)
    (hn : ¬ IsProof Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre)) :
    EqPrefixSpecializationAt Γ' Δ v w v' w' original pre σ' pending ∧
      env.HasType univs Γ' (VExpr.mkApps (.const ``Eq.rec [v',w']) pre) F ∧
      ¬ IsProof Γ' (VExpr.mkApps (.const ``Eq.rec [v',w']) pre) ∧
      ((pre.map (proofErase Γ')).map outgoing.erased) =
        (((pre.map (proofErase Γ)).map incoming.erased).map (·.subst υ)) := by
  obtain ⟨HP, ht, EE⟩ := H.frame hΔ Q.lower hf
  simp only [VExpr.subst_id, ProofShape.subst_id, List.map_id_fun', id] at HP ht EE
  have EF : proofErase Γ' (VExpr.mkApps (.const ``Eq.rec [v',w']) pre) =
      proofErase Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre) := by
    simpa only [VExpr.subst_id, ProofShape.subst_id] using
      proofErase_subst_with Q.lower.target.wf Q.lower.actual hf Q.lower.erase
  refine ⟨HP, ht, ?_, ?_⟩
  · intro hp
    exact hn (proofErase_eq_proof.1 (EF.symm.trans (proofErase_eq_proof.2 hp)))
  · rw [EE]
    simp only [List.map_map, Function.comp_def, Q.erased, ProofShape.subst_id]

/-- Consume an actual unused upper binder through every anchored inner frame.
Outgoing annotations and body witnesses are realized at their new scopes;
chosen lower substitutions are identity. The endpoint equation is exact and
both inner counts are unchanged. The recursively produced history remains an
input; this theorem does not recognize an arbitrary body endpoint. -/
theorem EqAnchoredPendingHistory.consume_unused
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΔ : OnCtx Δ (env.IsType univs))
    (W : EqSpecializationFrame Γ₀ Γ₀' Δ σ₀ σ₀' ρ τ)
    (J : EqFrameInsertionChain Γ₀ Γ₀' ρ τ Λ₀ Λ₀' κ ω blocks₀)
    (hA : env.HasType univs Λ₀ A (.sort u))
    (WX : ContextSubstitution (proofEraseCtx (A :: Λ₀)) (proofEraseCtx Λ₀)
      (ProofShape.Subst.one rawX))
    (H : EqAnchoredPendingHistory D Δ Γ₀ (A :: Λ₀) σ₀ (blocks₀ ++ [(1,0)]) [] sourceTarget sourceMap
      Γ Λ σ blocks pending Ψ υ plug body chosen depth) :
    ∃ x Γ' Λ' σ' outblocks returned χ,
      env.HasType univs Λ₀ x A ∧
      ErasedSubstAgreement (A :: Λ₀) Λ₀ (VExpr.Subst.one x) (ProofShape.Subst.one rawX) ∧
      EqSupplyInsertionSquare Γ Γ' Δ σ σ' VExpr.Subst.id ProofShape.Subst.id
        Λ Λ' ((VExpr.Subst.one x).liftN depth) χ blocks outblocks ∧
      EqAnchoredPendingHistory D Δ Γ₀ Λ₀ σ₀ blocks₀ [] (proofEraseCtx Λ₀) ProofShape.Subst.id
        Γ' Λ' σ' outblocks pending (proofEraseCtx Λ') ProofShape.Subst.id returned
        (body.subst χ) chosen depth ∧
      ∀ e, (plug e).inst rawX = returned (e.subst χ) := by
  obtain ⟨x, hx, EX, Q⟩ := EqSupplyInsertionSquare.unused_argument hΔ W J hA WX
  obtain ⟨Ξ, χ, HR⟩ := H.rebase_endpoint (proofEraseCtx Λ₀) (ProofShape.Subst.one rawX)
  obtain ⟨Γ', Λ', σ', outblocks, returned, Qout, _, Hout, EW⟩ :=
    HR.realize_returning heq hs hΔ Q rfl
  refine ⟨x, Γ', Λ', σ', outblocks, returned, χ, hx, EX, ?_, Hout, ?_⟩
  · simpa only [actual_id_liftN, raw_id_liftN] using Qout
  · intro e
    simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using EW e

/-- Consume an unused binder, restore its raw waiting tail, and rejoin older
anchored ancestry. The older anchors must already describe the actual post-beta
endpoint; updating them uses the actual native path, not a substituted path.
The recursively returned inner history and its positive depth are explicit
inputs. All source anchors and additive counts survive the rejoin. -/
theorem EqAnchoredPendingHistory.consume_unused_rejoin
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΔ : OnCtx Δ (env.IsType univs))
    (W : EqSpecializationFrame Γ₀ Γ₀' Δ σ₀ σ₀' ρ τ)
    (J : EqFrameInsertionChain Γ₀ Γ₀' ρ τ Λ₀ Λ₀' κ ω blocks₀)
    (hA : env.HasType univs Λ₀ A (.sort u))
    (WX : ContextSubstitution (proofEraseCtx (A :: Λ₀)) (proofEraseCtx Λ₀)
      (ProofShape.Subst.one rawX))
    (H : EqAnchoredPendingHistory D Δ Γ₀ (A :: Λ₀) σ₀ (blocks₀ ++ [(1,0)]) [] sourceTarget sourceMap
      Γ Λ σ blocks pending Ψ υ plug body chosen depth)
    (O : EqAnchoredPendingHistory D Δ baseΓ baseΛ baseσ baseBlocks basePending baseTarget baseMap
      Γ₀ Λ₀ σ₀ blocks₀ [] oldTarget oldMap oldPlug
      (ProofShape.mkApps ((plug body).inst rawX) rawRest) oldChosen oldDepth)
    (hd : 0 < depth) :
    ∃ x Γ' Λ' σ' outblocks returned χ joinedTarget joinedMap,
      env.HasType univs Λ₀ x A ∧
      ErasedSubstAgreement (A :: Λ₀) Λ₀ (VExpr.Subst.one x) (ProofShape.Subst.one rawX) ∧
      EqSupplyInsertionSquare Γ Γ' Δ σ σ' VExpr.Subst.id ProofShape.Subst.id
        Λ Λ' ((VExpr.Subst.one x).liftN depth) χ blocks outblocks ∧
      EqAnchoredPendingHistory D Δ Γ₀ Λ₀ σ₀ blocks₀ [] (proofEraseCtx Λ₀) ProofShape.Subst.id
        Γ' Λ' σ' outblocks pending (proofEraseCtx Λ') ProofShape.Subst.id returned
        (body.subst χ) chosen depth ∧
      EqAnchoredPendingHistory D Δ baseΓ baseΛ baseσ baseBlocks basePending baseTarget baseMap
        Γ' Λ' σ' outblocks pending joinedTarget joinedMap (fun e => oldPlug (returned e))
        (body.subst χ) (oldChosen+chosen) (oldDepth+depth) ∧
      ∀ e, ProofShape.mkApps ((plug e).inst rawX) rawRest = returned (e.subst χ) := by
  obtain ⟨x, Γ', Λ', σ', outblocks, returned, χ, hx, EX, Q, HR, EW⟩ :=
    H.consume_unused heq hs hΔ W J hA WX
  obtain ⟨returned', HR', Eapp⟩ := HR.append_outer_extra rawRest hd
  have Eall : ∀ e, ProofShape.mkApps ((plug e).inst rawX) rawRest = returned' (e.subst χ) := by
    intro e; rw [Eapp, EW]
  obtain ⟨Ξ, ψ, Hrebased⟩ := HR'.rebase_endpoint oldTarget oldMap
  have O' : EqAnchoredPendingHistory D Δ baseΓ baseΛ baseσ baseBlocks basePending baseTarget baseMap
      Γ₀ Λ₀ σ₀ blocks₀ [] oldTarget oldMap oldPlug (returned' (body.subst χ)) oldChosen oldDepth :=
    (Eall body) ▸ O
  exact ⟨x, Γ', Λ', σ', outblocks, returned', χ, Ξ, ψ, hx, EX, Q, HR', Hrebased.append O', Eall⟩

/-- If no inner wrappers survive, a recognized completed prefix returns
through the unused binder directly. Only the raw upper extras are instantiated;
all lower chosen components and their typings remain the same. The waiting raw
tail is restored after those extras. Recognition of this body is still an input. -/
theorem EqPrefixSpecializationAt.unused_recognized_return
    (H : EqPrefixSpecializationAt Γ Δ v w v' w' original pre σ [])
    (W : EqSpecializationFrame Γ Γ' Δ σ σ' ρ τ)
    (J : EqFrameInsertionChain Γ Γ' ρ τ Λ Λ' κ υ blocks)
    (hf : env.HasType univs Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre) F)
    (hn : ¬ IsProof Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre))
    (EB : body = ProofShape.mkApps (.const ``Eq.rec [v',w'])
      (((pre.map (proofErase Γ)).map (blocks ++ [(1,0)]).erased) ++ extra)) :
    ProofShape.mkApps (body.inst rawX) rawRest =
      ProofShape.mkApps (.const ``Eq.rec [v',w'])
        (((pre.map (proofErase Γ)).map blocks.erased) ++ (extra.map (·.inst rawX) ++ rawRest)) ∧
      EqTargetPrefixCompletion Δ v w original (proofEraseCtx Λ)
        (ProofShape.mkApps (body.inst rawX) rawRest) := by
  have EI : (((pre.map (proofErase Γ)).map (blocks ++ [(1,0)]).erased).map (·.inst rawX)) =
      ((pre.map (proofErase Γ)).map blocks.erased) := by
    simp only [List.map_map, Function.comp_def, EqInsertionPath.erased_snoc,
      ProofShape.inst_eq_subst, ProofShape.Subst.liftN, ProofShape.Subst.one,
      ProofShape.lift_subst_cons, ProofShape.subst_id]
  have EE : ProofShape.mkApps (body.inst rawX) rawRest =
      ProofShape.mkApps (.const ``Eq.rec [v',w'])
        (((pre.map (proofErase Γ)).map blocks.erased) ++ (extra.map (·.inst rawX) ++ rawRest)) := by
    rw [EB, ProofShape.inst_eq_subst, ProofShape.subst_mkApps]
    simp only [ProofShape.subst, ← ProofShape.inst_eq_subst, List.map_append, EI,
      ← ProofShape.mkApps_append, List.append_assoc]
  refine ⟨EE, ?_⟩
  rw [EE]
  exact H.saturated_chain_completion W J hf hn (extra.map (·.inst rawX) ++ rawRest)

end Lean4Lean.VEnv.Strengthening
