import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqUnusedAnchoredConsumption

/-! # Exact anchored states for endpoint recognition

A recognized endpoint keeps the actual base scope and pending target vector,
while its current leaf scope may contain realized retained binders. The history
is normalized to its actual displayed contexts and the current leaf is a typed,
nonproof chosen Eq prefix. This file does not prove the global recognizer.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private isProof_congr
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
open private actual_id_liftN raw_id_liftN
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqPendingCountedReadout
variable [Params]

/-- Actual argument computation preserves a retained frame's whole source
application witness, not just the individual typings in its forgotten supply.
The body path stays in its original scope and untracked extras keep their
actual computations. This is needed by the retained branch of recognition. -/
theorem EqRetainedSourceAnchor.compute_arguments
    (hstep : ErasedScopedPrimitiveCertificateDescent Step Step)
    (hΔ : OnCtx Δ (env.IsType univs))
    (H : EqRetainedSourceAnchor D Γ Λ Δ σ blocks A y pending remaining body args)
    (W : EqSpecializationFrame Γ Γ' Δ σ σ' ρ τ)
    (J : EqFrameInsertionChain Γ Γ' ρ τ Λ Λ' κ υ blocks)
    (RA : List.Forall₂ (ScopedCompute Step (proofEraseCtx Λ)) args args') :
    EqRetainedSourceAnchor D Γ Λ Δ σ blocks A y pending remaining body args' := by
  obtain ⟨hΓ, e, E, supplied, actual, extra, F, n, he, happ, hn, HS, EP, hxtra, ER, RB⟩ := H
  rw [← ER] at RA
  obtain ⟨actual', extra', HS', HE, ER', RX⟩ := HS.chain_compute_prefix hstep hΔ W J RA
  obtain ⟨Tf, hf⟩ := VExpr.WF.of_mkApps henv.orderedStrong hΓ ⟨_, happ⟩
  have HF := (IsDefEqU.mkApps_args hΓ hf.toU HE happ).of_l henv hΓ happ
  refine ⟨hΓ, e, E, supplied, actual', extra', F, n, he, HF.hasType.2,
    (fun hp => hn ((isProof_congr hΓ HF).2 hp)), HS', EP, ?_, ER', RB⟩
  rcases hxtra with rfl | hp
  · cases RX; exact .inl rfl
  · exact .inr hp

/-- A history's source frames are determined by its base source frame and its
actual chosen/unused binders. Computed annotations do not alter this original
source chain. This supplies the leaf chain when unfolding a recognition state. -/
theorem EqAnchoredPendingHistory.source_identity
    (hΔ : OnCtx Δ (env.IsType univs))
    (H : EqAnchoredPendingHistory D Δ Γ₀ Λ₀ σ₀ blocks₀ pending₀ Ψ₀ υ₀
      Γ Λ σ blocks pending Ψ υ plug body chosen depth)
    (W : EqSpecializationFrame Γ₀ Γ₀ Δ σ₀ σ₀ VExpr.Subst.id ProofShape.Subst.id)
    (J : EqFrameInsertionChain Γ₀ Γ₀ VExpr.Subst.id ProofShape.Subst.id
      Λ₀ Λ₀ VExpr.Subst.id ProofShape.Subst.id blocks₀) :
    EqSpecializationFrame Γ Γ Δ σ σ VExpr.Subst.id ProofShape.Subst.id ∧
      EqFrameInsertionChain Γ Γ VExpr.Subst.id ProofShape.Subst.id
        Λ Λ VExpr.Subst.id ProofShape.Subst.id blocks := by
  induction H with
  | base => exact ⟨W, J⟩
  | retained _ hA hy _ _ ih =>
    obtain ⟨W, J⟩ := ih
    exact ⟨by simpa only [VExpr.subst_id, VExpr.id_lift, ProofShape.Subst.id_lift] using W.under_binder hΔ hA hy,
      by simpa only [VExpr.subst_id, VExpr.id_lift, ProofShape.Subst.id_lift] using J.under_binder W hA⟩
  | unused _ hA _ ih =>
    obtain ⟨W, J⟩ := ih
    exact ⟨W, by simpa only [VExpr.subst_id, VExpr.id_lift, ProofShape.Subst.id_lift] using J.insert_domain W hA⟩

/-- An exact recognized endpoint at a fixed base scope and pending vector.
Every source anchor is tied to this actual endpoint, all displayed contexts
are normalized, and the current leaf is a typed nonproof chosen Eq prefix.
The depth is explicit so recognition must prove a bound on it. -/
def EqAnchoredEndpoint (D : Definitions) (Δ Γ₀ Λ₀ : List VExpr) (σ₀ : VExpr.Subst)
    (blocks₀ : EqInsertionPath) (pending₀ : List VExpr) (v w : VLevel)
    (original : List VExpr) (endpoint : ProofShape) (depth : Nat) : Prop :=
  ∃ Γ Λ σ blocks pending v' w' pre extra F plug chosen,
    EqAnchoredPendingHistory D Δ Γ₀ Λ₀ σ₀ blocks₀ pending₀ (proofEraseCtx Λ₀) ProofShape.Subst.id
      Γ Λ σ blocks pending (proofEraseCtx Λ) ProofShape.Subst.id plug
      (ProofShape.mkApps (.const ``Eq.rec [v',w']) (((pre.map (proofErase Γ)).map blocks.erased) ++ extra))
      chosen depth ∧
    EqPrefixSpecializationAt Γ Δ v w v' w' original pre σ pending ∧
    env.HasType univs Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre) F ∧
    (¬ IsProof Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre)) ∧
    (extra = [] ∨ pending = []) ∧
    endpoint = plug (ProofShape.mkApps (.const ``Eq.rec [v',w'])
      (((pre.map (proofErase Γ)).map blocks.erased) ++ extra))

/-- A chosen source spine is a recognized endpoint with no wrappers. -/
theorem EqAnchoredEndpoint.of_spine
    (H : EqPrefixSpecializationAt Γ Δ v w v' w' original pre σ pending)
    (hf : env.HasType univs Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre) F)
    (hn : ¬ IsProof Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre))
    (hextra : extra = [] ∨ pending = []) :
    EqAnchoredEndpoint D Δ Γ Λ σ blocks pending v w original
      (ProofShape.mkApps (.const ``Eq.rec [v',w']) (((pre.map (proofErase Γ)).map blocks.erased) ++ extra)) 0 :=
  ⟨Γ, Λ, σ, blocks, pending, v', w', pre, extra, F, id, 0, .base, H, hf, hn, hextra, rfl⟩

/-- Normalize an actual anchored history without changing its raw endpoint or
its depth. The agreeing identity square realizes annotations and source bodies;
it does not transport a native path to a different context. The same lower
chosen prefix survives in the realized leaf scope. -/
theorem EqAnchoredEndpoint.of_history
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΔ : OnCtx Δ (env.IsType univs))
    (W : EqSpecializationFrame Γ₀ Γ₀' Δ σ₀ σ₀' ρ τ)
    (J : EqFrameInsertionChain Γ₀ Γ₀' ρ τ Λ₀ Λ₀' κ ω blocks₀)
    (H : EqAnchoredPendingHistory D Δ Γ₀ Λ₀ σ₀ blocks₀ pending₀ sourceTarget sourceMap
      Γ Λ σ blocks pending Ψ υ plug
      (ProofShape.mkApps (.const ``Eq.rec [v',w']) (((pre.map (proofErase Γ)).map blocks.erased) ++ extra))
      chosen depth)
    (HP : EqPrefixSpecializationAt Γ Δ v w v' w' original pre σ pending)
    (hf : env.HasType univs Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre) F)
    (hn : ¬ IsProof Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre))
    (hextra : extra = [] ∨ pending = []) :
    EqAnchoredEndpoint D Δ Γ₀ Λ₀ σ₀ blocks₀ pending₀ v w original
      (plug (ProofShape.mkApps (.const ``Eq.rec [v',w'])
        (((pre.map (proofErase Γ)).map blocks.erased) ++ extra))) depth := by
  have Q := EqSupplyInsertionSquare.source_identity hΔ W J
  obtain ⟨Ξ, χ, HR⟩ := H.rebase_endpoint (proofEraseCtx Λ₀) ProofShape.Subst.id
  have Eχ := HR.endpoint_map_eq_id rfl
  obtain ⟨Γ', Λ', σ', outblocks, normalized, Qout, _, Hout, EW⟩ :=
    HR.realize_returning heq hs hΔ Q rfl
  simp only [Eχ, actual_id_liftN, raw_id_liftN, ProofShape.subst_id] at Qout Hout EW
  obtain ⟨HP', hf', hn', ER⟩ := Qout.identity_prefix hΔ HP hf hn
  refine ⟨Γ', Λ', σ', outblocks, pending, v', w', pre, extra, F, normalized, chosen,
    ?_, HP', hf', hn', hextra, ?_⟩
  · simpa only [ER] using Hout
  · simpa only [ER] using EW (ProofShape.mkApps (.const ``Eq.rec [v',w'])
      (((pre.map (proofErase Γ)).map blocks.erased) ++ extra))

/-- Anchored wrappers preserve the syntactic retained constant head. No typing
or native computation principle is used in this endpoint-shape fact. -/
theorem EqAnchoredPendingHistory.retained_head
    (H : EqAnchoredPendingHistory D Δ Γ₀ Λ₀ σ₀ blocks₀ pending₀ Ψ₀ υ₀
      Γ Λ σ blocks pending Ψ υ plug body chosen depth)
    (HC : RetainedConstHead c body) : RetainedConstHead c (plug body) := by
  revert HC
  induction H with
  | base => intro HC; exact HC
  | retained _ _ _ _ _ ih => intro HC; exact ih ((RetainedConstHead.lam HC).mkApps _)
  | unused _ _ _ ih => intro HC; exact ih ((RetainedConstHead.lam HC).mkApps _)

/-- A recognized endpoint is incompatible with exposed carrier syntax. This
is the closing contradiction once the actual recursive recognizer is proved. -/
theorem EqAnchoredEndpoint.not_exposed
    (heq : env.HasCanonicalEq)
    (H : EqAnchoredEndpoint D Δ Γ₀ Λ₀ σ₀ blocks₀ pending₀ v w original endpoint depth) :
    ¬ CarrierExposure endpoint := by
  obtain ⟨Γ, Λ, σ, blocks, pending, v', w', pre, extra, F, plug, chosen,
    HH, _, _, _, _, rfl⟩ := H
  exact (HH.retained_head ((RetainedConstHead.const).mkApps _)).eq_not_exposed heq

/-- A component-only path already produces the recognizer's exact output
state with zero wrappers. Otherwise the actual first non-level cut, including
its supplied suffix and primitive budget, is retained for the recursive case. -/
theorem EqPrefixSpecializationAt.anchored_spine_or_cut
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΔ : OnCtx Δ (env.IsType univs))
    (H : EqPrefixSpecializationAt Γ Δ v w v' w' original pre σ pending)
    (W : EqSpecializationFrame Γ Γ' Δ σ σ' ρ τ)
    (J : EqFrameInsertionChain Γ Γ' ρ τ Λ Λ' κ υ blocks)
    (hf : env.HasType univs Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre) F)
    (hn : ¬ IsProof Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre))
    (hextra : extra = [] ∨ pending = [])
    (HT : TypedSource (proofEraseCtx Λ)
      (ProofShape.mkApps (.const ``Eq.rec [v',w']) (((pre.map (proofErase Γ)).map blocks.erased) ++ extra)))
    (R : ScopedComputeCount (PiInertStage D n) cost (proofEraseCtx Λ)
      (ProofShape.mkApps (.const ``Eq.rec [v',w']) (((pre.map (proofErase Γ)).map blocks.erased) ++ extra)) endpoint) :
    EqAnchoredEndpoint D Δ Γ Λ σ blocks pending v w original endpoint 0 ∨
      ChosenEqChainSpineCut D Γ Δ Λ blocks v w original σ pending n
        (ProofShape.mkApps (.const ``Eq.rec [v',w']) (((pre.map (proofErase Γ)).map blocks.erased) ++ extra)) endpoint cost := by
  rcases H.chain_counted_spine_or_cut heq hs hΔ W J hf hn hextra HT R with
    ⟨v'', w'', pre', extra', rfl, HP, HE, _, _, _, hxtra⟩ | HC
  · exact .inl (EqAnchoredEndpoint.of_spine HP HE.hasType.2
      (fun hp => hn ((isProof_congr H.1.wf HE).2 hp)) hxtra)
  · exact .inr HC

/-- The depth-zero, zero-primitive-cost recognition case is unconditional:
a non-level cut would consume one primitive, so only a computed chosen spine
can remain. This is a proved base case, not the general recursive recognizer. -/
theorem EqPrefixSpecializationAt.zero_cost_anchored_endpoint
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΔ : OnCtx Δ (env.IsType univs))
    (H : EqPrefixSpecializationAt Γ Δ v w v' w' original pre σ pending)
    (W : EqSpecializationFrame Γ Γ' Δ σ σ' ρ τ)
    (J : EqFrameInsertionChain Γ Γ' ρ τ Λ Λ' κ υ blocks)
    (hf : env.HasType univs Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre) F)
    (hn : ¬ IsProof Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre))
    (hextra : extra = [] ∨ pending = [])
    (HT : TypedSource (proofEraseCtx Λ)
      (ProofShape.mkApps (.const ``Eq.rec [v',w']) (((pre.map (proofErase Γ)).map blocks.erased) ++ extra)))
    (R : ScopedComputeCount (PiInertStage D n) 0 (proofEraseCtx Λ)
      (ProofShape.mkApps (.const ``Eq.rec [v',w']) (((pre.map (proofErase Γ)).map blocks.erased) ++ extra)) endpoint) :
    EqAnchoredEndpoint D Δ Γ Λ σ blocks pending v w original endpoint 0 := by
  rcases H.anchored_spine_or_cut heq hs hΔ W J hf hn hextra HT R with HE | HC
  · exact HE
  · obtain ⟨v'', w'', pre', extra', arity, F', target, cp, ct, _, _, _, _, _, hc, _⟩ := HC
    omega

/-- A zero-depth history has exactly its base source scopes, insertion path,
pending vector and identity wrapper. Keeping the depth equation separate avoids
dependent elimination through computed annotation-context equalities. -/
theorem EqAnchoredPendingHistory.zero_depth
    (H : EqAnchoredPendingHistory D Δ Γ₀ Λ₀ σ₀ blocks₀ pending₀ Ψ₀ υ₀
      Γ Λ σ blocks pending Ψ υ plug body chosen depth)
    (hd : depth = 0) :
    Γ = Γ₀ ∧ Λ = Λ₀ ∧ σ = σ₀ ∧ blocks = blocks₀ ∧ pending = pending₀ ∧ plug = id := by
  cases H with
  | base => exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  | retained => omega
  | unused => omega

/-- A depth-zero recognition state is exactly a chosen spine in its base
scope. No hidden frame or changed pending assignment survives this inversion. -/
theorem EqAnchoredEndpoint.zero_depth_spine
    (H : EqAnchoredEndpoint D Δ Γ Λ σ blocks pending v w original source 0) :
    ∃ v' w' pre extra F,
      EqPrefixSpecializationAt Γ Δ v w v' w' original pre σ pending ∧
      env.HasType univs Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre) F ∧
      (¬ IsProof Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre)) ∧
      (extra = [] ∨ pending = []) ∧
      source = ProofShape.mkApps (.const ``Eq.rec [v',w'])
        (((pre.map (proofErase Γ)).map blocks.erased) ++ extra) := by
  obtain ⟨Γ', Λ', σ', blocks', pending', v', w', pre, extra, F, plug, chosen,
    HH, HP, hf, hn, hxtra, rfl⟩ := H
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := HH.zero_depth rfl
  exact ⟨v', w', pre, extra, F, HP, hf, hn, hxtra, rfl⟩

/-- The `(primitive cost, incoming depth) = (0,0)` case of the proposed
recognizer is proved without continuation assumptions. A chosen source spine
can only retain its head at zero primitive cost. -/
theorem EqAnchoredEndpoint.zero_cost_zero_depth
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΔ : OnCtx Δ (env.IsType univs))
    (W : EqSpecializationFrame Γ Γ' Δ σ σ' ρ τ)
    (J : EqFrameInsertionChain Γ Γ' ρ τ Λ Λ' κ υ blocks)
    (H : EqAnchoredEndpoint D Δ Γ Λ σ blocks pending v w original source 0)
    (HT : TypedSource (proofEraseCtx Λ) source)
    (R : ScopedComputeCount (PiInertStage D n) 0 (proofEraseCtx Λ) source endpoint) :
    EqAnchoredEndpoint D Δ Γ Λ σ blocks pending v w original endpoint 0 := by
  obtain ⟨v', w', pre, extra, F, HP, hf, hn, hxtra, rfl⟩ := H.zero_depth_spine
  exact HP.zero_cost_anchored_endpoint heq hs hΔ W J hf hn hxtra HT R

/-- Realize a recognized endpoint through an actual agreeing base square.
All source anchors and the chosen prefix survive, and the raw endpoint follows
exactly the base upper map. Depth is unchanged. Only endpoint syntax and source
equalities are mapped; no native path or continuation minimum is transported. -/
theorem EqAnchoredEndpoint.realize
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΔ : OnCtx Δ (env.IsType univs))
    (Q : EqSupplyInsertionSquare Γ₀ Γ₀' Δ σ₀ σ₀' ρ₀ τ₀ Λ₀ Λ₀' κ₀ υ₀ incoming outgoing)
    (H : EqAnchoredEndpoint D Δ Γ₀ Λ₀ σ₀ incoming pending₀ v w original endpoint depth) :
    EqAnchoredEndpoint D Δ Γ₀' Λ₀' σ₀' outgoing pending₀ v w original (endpoint.subst υ₀) depth := by
  obtain ⟨Γ, Λ, σ, blocks, pending, v', w', pre, extra, F, plug, chosen,
    HH, HP, hf, hn, hxtra, rfl⟩ := H
  obtain ⟨Ξ, χ, HR⟩ := HH.rebase_endpoint (proofEraseCtx Λ₀') υ₀
  obtain ⟨Γ', Λ', σ', outblocks, returned, Qout, _, Hout, EW⟩ :=
    HR.realize_returning heq hs hΔ Q rfl
  obtain ⟨HP', hf', EP⟩ := HP.frame hΔ Qout.lower hf
  have hn' : ¬ IsProof Γ'
      (VExpr.mkApps (.const ``Eq.rec [v',w']) (pre.map (·.subst (ρ₀.liftN chosen)))) := by
    intro hp
    apply hn
    apply (isProof_subst Qout.lower.target.wf Qout.lower.actual hf).1
    simpa only [VExpr.subst_mkApps, VExpr.subst] using hp
  have ER : (((pre.map (·.subst (ρ₀.liftN chosen))).map (proofErase Γ')).map outblocks.erased) =
      (((pre.map (proofErase Γ)).map blocks.erased).map (·.subst χ)) := by
    rw [EP]
    simp only [List.map_map, Function.comp_def, Qout.erased]
  have EB : (ProofShape.mkApps (.const ``Eq.rec [v',w'])
      (((pre.map (proofErase Γ)).map blocks.erased) ++ extra)).subst χ =
      ProofShape.mkApps (.const ``Eq.rec [v',w'])
        ((((pre.map (·.subst (ρ₀.liftN chosen))).map (proofErase Γ')).map outblocks.erased) ++
          extra.map (·.subst χ)) := by
    simp only [ProofShape.subst_mkApps, ProofShape.subst, List.map_append, ER]
  refine ⟨Γ', Λ', σ', outblocks, pending, v', w', pre.map (·.subst (ρ₀.liftN chosen)),
    extra.map (·.subst χ), F.subst (ρ₀.liftN chosen), returned, chosen,
    ?_, HP', hf', hn', ?_, ?_⟩
  · simpa only [EB] using Hout
  · rcases hxtra with rfl | hp
    · exact .inl rfl
    · exact .inr hp
  · simpa only [EB] using EW (ProofShape.mkApps (.const ``Eq.rec [v',w'])
      (((pre.map (proofErase Γ)).map blocks.erased) ++ extra))

/-- Rebuild a retained chosen lambda around a recursively recognized body.
The source anchor refers to that exact body endpoint. Rebase and append keep
all inner witnesses, then identity realization normalizes the new displayed
domain. The output depth is exactly one more than the body's depth. -/
theorem EqAnchoredEndpoint.retain_chosen
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΔ : OnCtx Δ (env.IsType univs))
    (W : EqSpecializationFrame Γ₀ Γ₀' Δ σ₀ σ₀' ρ τ)
    (J : EqFrameInsertionChain Γ₀ Γ₀' ρ τ Λ₀ Λ₀' κ ω blocks₀)
    (hA : env.HasType univs Γ₀ A (.sort u)) (hy : env.HasType univs Δ y (A.subst σ₀))
    (RD : ScopedComputeCount (PiInertStage D n) cd (proofEraseCtx Λ₀)
      (blocks₀.erased (proofErase Γ₀ A)) rawA)
    (HA : EqRetainedSourceAnchor D Γ₀ Λ₀ Δ σ₀ blocks₀ A y pending₀ remaining body args)
    (HB : EqAnchoredEndpoint D Δ (A :: Γ₀) (blocks₀.actual A :: Λ₀) (σ₀.cons y)
      blocks₀.underBinder remaining v w original body depth) :
    EqAnchoredEndpoint D Δ Γ₀ Λ₀ σ₀ blocks₀ pending₀ v w original
      (ProofShape.mkApps (.lam rawA body) args) (depth+1) := by
  obtain ⟨Γ, Λ, σ, blocks, pending, v', w', pre, extra, F, plug, chosen,
    HH, HP, hf, hn, hxtra, rfl⟩ := HB
  have HO : EqAnchoredPendingHistory D Δ Γ₀ Λ₀ σ₀ blocks₀ pending₀ (proofEraseCtx Λ₀) ProofShape.Subst.id
      (A :: Γ₀) (blocks₀.actual A :: Λ₀) (σ₀.cons y) blocks₀.underBinder remaining
      (rawA :: proofEraseCtx Λ₀) ProofShape.Subst.id
      (fun e => ProofShape.mkApps (.lam rawA e) args)
      (plug (ProofShape.mkApps (.const ``Eq.rec [v',w'])
        (((pre.map (proofErase Γ)).map blocks.erased) ++ extra))) 1 1 := by
    simpa only [ProofShape.subst_id, ProofShape.Subst.id_lift, id_eq] using
      EqAnchoredPendingHistory.retained (Ψ₀ := proofEraseCtx Λ₀) (υ₀ := ProofShape.Subst.id)
        .base hA hy RD HA
  obtain ⟨Ξ, χ, HI⟩ := HH.rebase_endpoint (rawA :: proofEraseCtx Λ₀) ProofShape.Subst.id
  have Hjoined := HI.append HO
  simpa only [Nat.add_comm 1 depth] using
    EqAnchoredEndpoint.of_history heq hs hΔ W J Hjoined HP hf hn hxtra

/-- Rebuild a retained unused lambda around a recognized completed body.
Only the upper scope gains a binder, and its arbitrary raw argument vector
requires no lower chosen images. Depth increases by exactly one. -/
theorem EqAnchoredEndpoint.retain_unused
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΔ : OnCtx Δ (env.IsType univs))
    (W : EqSpecializationFrame Γ₀ Γ₀' Δ σ₀ σ₀' ρ τ)
    (J : EqFrameInsertionChain Γ₀ Γ₀' ρ τ Λ₀ Λ₀' κ ω blocks₀)
    (hA : env.HasType univs Λ₀ A (.sort u))
    (RD : ScopedComputeCount (PiInertStage D n) cd (proofEraseCtx Λ₀) (proofErase Λ₀ A) rawA)
    (HB : EqAnchoredEndpoint D Δ Γ₀ (A :: Λ₀) σ₀ (blocks₀ ++ [(1,0)]) [] v w original body depth) :
    EqAnchoredEndpoint D Δ Γ₀ Λ₀ σ₀ blocks₀ [] v w original
      (ProofShape.mkApps (.lam rawA body) args) (depth+1) := by
  obtain ⟨Γ, Λ, σ, blocks, pending, v', w', pre, extra, F, plug, chosen,
    HH, HP, hf, hn, hxtra, rfl⟩ := HB
  have HO : EqAnchoredPendingHistory D Δ Γ₀ Λ₀ σ₀ blocks₀ [] (proofEraseCtx Λ₀) ProofShape.Subst.id
      Γ₀ (A :: Λ₀) σ₀ (blocks₀ ++ [(1,0)]) []
      (rawA :: proofEraseCtx Λ₀) ProofShape.Subst.id
      (fun e => ProofShape.mkApps (.lam rawA e) args)
      (plug (ProofShape.mkApps (.const ``Eq.rec [v',w'])
        (((pre.map (proofErase Γ)).map blocks.erased) ++ extra))) 0 1 := by
    simpa only [ProofShape.subst_id, ProofShape.Subst.id_lift, id_eq] using
      EqAnchoredPendingHistory.unused (Ψ₀ := proofEraseCtx Λ₀) (υ₀ := ProofShape.Subst.id)
        .base hA RD
  obtain ⟨Ξ, χ, HI⟩ := HH.rebase_endpoint (rawA :: proofEraseCtx Λ₀) ProofShape.Subst.id
  have Hjoined := HI.append HO
  simpa only [Nat.add_comm 1 depth] using
    EqAnchoredEndpoint.of_history heq hs hΔ W J Hjoined HP hf hn hxtra

/-- The retained chosen-frame recursive case preserves the required depth
bound. Actual body and argument computation update the original source anchor;
the recursive body's exact recognized state is then wrapped and normalized.
The body's recognition and depth bound remain explicit induction hypotheses. -/
theorem EqRetainedSourceAnchor.retained_recognition
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΔ : OnCtx Δ (env.IsType univs))
    (W : EqSpecializationFrame Γ Γ' Δ σ σ' ρ τ)
    (J : EqFrameInsertionChain Γ Γ' ρ τ Λ Λ' κ ω blocks)
    (hA : env.HasType univs Γ A (.sort u)) (hy : env.HasType univs Δ y (A.subst σ))
    (H : EqRetainedSourceAnchor D Γ Λ Δ σ blocks A y pending remaining body args)
    (RD : ScopedComputeCount (PiInertStage D n) cd (proofEraseCtx Λ)
      (blocks.erased (proofErase Γ A)) rawA)
    (RB : ScopedComputeCount (PiInertStage D m) cb (proofEraseCtx (blocks.actual A :: Λ)) body body')
    (RA : ScopedArgumentsCount (PiInertStage D n) (proofEraseCtx Λ) ca args args')
    (HB : EqAnchoredEndpoint D Δ (A :: Γ) (blocks.actual A :: Λ) (σ.cons y)
      blocks.underBinder remaining v w original body' returnedDepth)
    (hdepth : returnedDepth ≤ incomingDepth+cb) (hcost : cd+cb+ca ≤ cost) :
    ∃ depth, depth ≤ (incomingDepth+1)+cost ∧
      EqAnchoredEndpoint D Δ Γ Λ σ blocks pending v w original
        (ProofShape.mkApps (.lam rawA body') args') depth := by
  have HA := H.compute_arguments (pi_inert_stage_certificate_descent heq hs n) hΔ W J RA.forget
  have HA' := HA.compute_body RB.forget
  exact ⟨returnedDepth+1, by omega, HB.retain_chosen heq hs hΔ W J hA hy RD HA'⟩

/-- Agreement of a history's final placeholder context with its actual
source context forces the same agreement at its base. Every constructor adds
one upper binder to both sides, so taking tails preserves this evidence. -/
theorem EqAnchoredPendingHistory.base_context_eq
    (H : EqAnchoredPendingHistory D Δ Γ₀ Λ₀ σ₀ blocks₀ pending₀ Ψ₀ υ₀
      Γ Λ σ blocks pending Ψ υ plug body chosen depth)
    (E : Ψ = proofEraseCtx Λ) : Ψ₀ = proofEraseCtx Λ₀ := by
  revert E
  induction H with
  | base => exact id
  | retained _ _ _ _ _ ih => intro E; exact ih (List.cons.inj E).2
  | unused _ _ _ ih => intro E; exact ih (List.cons.inj E).2

/-- A positive recognized state exposes an outer lambda whose displayed
annotation is exactly its actual source domain, together with the recognized
inner endpoint. Chosen frames additionally return the full source application
anchor. Thus a history-recognition call can read the actual lambda suffix in
its original body scope without assuming context-conversion invariance. -/
theorem EqAnchoredEndpoint.outermost
    (W : EqSpecializationFrame Γ₀ Γ₀' Δ σ₀ σ₀' ρ τ)
    (J : EqFrameInsertionChain Γ₀ Γ₀' ρ τ Λ₀ Λ₀' κ ω blocks₀)
    (H : EqAnchoredEndpoint D Δ Γ₀ Λ₀ σ₀ blocks₀ pending₀ v w original source depth)
    (hd : 0 < depth) :
    (∃ A u y args remaining body innerDepth,
      env.HasType univs Γ₀ A (.sort u) ∧ env.HasType univs Δ y (A.subst σ₀) ∧
      EqRetainedSourceAnchor D Γ₀ Λ₀ Δ σ₀ blocks₀ A y pending₀ remaining body args ∧
      EqAnchoredEndpoint D Δ (A :: Γ₀) (blocks₀.actual A :: Λ₀) (σ₀.cons y)
        blocks₀.underBinder remaining v w original body innerDepth ∧
      depth = innerDepth+1 ∧
      source = ProofShape.mkApps (.lam (blocks₀.erased (proofErase Γ₀ A)) body) args) ∨
    (∃ A u args body innerDepth, pending₀ = [] ∧ env.HasType univs Λ₀ A (.sort u) ∧
      EqAnchoredEndpoint D Δ Γ₀ (A :: Λ₀) σ₀ (blocks₀ ++ [(1,0)]) []
        v w original body innerDepth ∧ depth = innerDepth+1 ∧
      source = ProofShape.mkApps (.lam (proofErase Λ₀ A) body) args) := by
  obtain ⟨Γ, Λ, σ, blocks, pending, v', w', pre, extra, F, plug, chosen,
    HH, HP, hf, hn, hxtra, rfl⟩ := H
  rcases HH.outermost hd with
    ⟨A, u, y, rawA, args, remaining, n, cd, inner, chosen', depth', hA, hy, RD, HA, HI, hc, hd', EW⟩ |
    ⟨A, u, rawA, args, n, cd, inner, depth', hp, hA, RD, HI, hd', EW⟩
  · have Ebase := HI.base_context_eq rfl
    have EA : rawA = proofErase Λ₀ (blocks₀.actual A) := by
      simpa only [ProofShape.subst_id] using (List.cons.inj Ebase).1
    refine .inl ⟨A, u, y, args, remaining, _, depth', hA, hy, HA,
      ⟨Γ, Λ, σ, blocks, pending, v', w', pre, extra, F, inner, chosen',
        ?_, HP, hf, hn, hxtra, rfl⟩, hd', ?_⟩
    · simpa only [Ebase, ProofShape.Subst.id_lift] using HI
    · simpa only [EA, J.erase_actual W hA] using EW (ProofShape.mkApps (.const ``Eq.rec [v',w'])
        (((pre.map (proofErase Γ)).map blocks.erased) ++ extra))
  · have Ebase := HI.base_context_eq rfl
    have EA : rawA = proofErase Λ₀ A := by
      simpa only [ProofShape.subst_id] using (List.cons.inj Ebase).1
    refine .inr ⟨A, u, args, _, depth', hp, hA,
      ⟨Γ, Λ, σ, blocks, pending, v', w', pre, extra, F, inner, chosen,
        ?_, HP, hf, hn, hxtra, rfl⟩, hd', ?_⟩
    · simpa only [Ebase, ProofShape.Subst.id_lift] using HI
    · simpa only [EA] using EW (ProofShape.mkApps (.const ``Eq.rec [v',w'])
        (((pre.map (proofErase Γ)).map blocks.erased) ++ extra))

/-- The global recognition specification, proved by `eq_anchored_recognition`
in `ProofErasureEqAnchoredRecognition`. It preserves the exact
base scopes and pending vector, returning a normalized anchored endpoint with
depth at most incoming depth plus primitive cost, or reading the original target Eq.
The selected typed continuation, exposed terminal carrier and all-stage minimum
are retained: root classification cannot currently discard these hypotheses.
This module establishes local cases and conditional sufficiency. The later
module supplies fresh-eta initialization and the complete cost/depth induction;
no irreducibility or strict comparison with PropFront is claimed. -/
def EqAnchoredRecognition (D : Definitions) : Prop :=
  ∀ {Δ Γ₀ Λ₀ : List VExpr} {σ₀ : VExpr.Subst} {blocks₀ : EqInsertionPath}
    {pending₀ : List VExpr} {v w : VLevel} {α a M minor b T : VExpr}
    {source endpoint out : ProofShape} {Ω : List ProofShape} {outU : VLevel}
    {K : ProofShape → Nat → Prop} {depth n cost ck : Nat},
    env.HasCanonicalEq → D.Sound env univs →
    (∃ data, recursorData ``Eq.rec = some data ∧ data.majorOffset = 5) →
    (∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs) →
    OnCtx Δ (env.IsType univs) →
    env.HasType univs Δ (eqRecBeforeMajor v w α a M minor b) T →
    EqSpecializationFrame Γ₀ Γ₀ Δ σ₀ σ₀ VExpr.Subst.id ProofShape.Subst.id →
    EqFrameInsertionChain Γ₀ Γ₀ VExpr.Subst.id ProofShape.Subst.id
      Λ₀ Λ₀ VExpr.Subst.id ProofShape.Subst.id blocks₀ →
    EqAnchoredEndpoint D Δ Γ₀ Λ₀ σ₀ blocks₀ pending₀ v w [α,a,M,minor,b] source depth →
    TypedSource (proofEraseCtx Λ₀) source →
    ScopedComputeCount (PiInertStage D n) cost (proofEraseCtx Λ₀) source endpoint →
    PiInertTypedContinuationRun D Ω out (proofEraseCtx Λ₀) K endpoint ck →
    CarrierExposure out → ControlTyping Ω out (.sort outU) →
    (∀ later j tail k, ScopedComputeCount (PiInertStage D later) j
      (proofEraseCtx Λ₀) source tail → K tail k → cost+ck ≤ j+k) →
    env.IsDefEq univs Δ a b α ∨ ∃ returnedDepth, returnedDepth ≤ depth+cost ∧
      EqAnchoredEndpoint D Δ Γ₀ Λ₀ σ₀ blocks₀ pending₀ v w [α,a,M,minor,b] endpoint returnedDepth

/-- The stated recognition obligation suffices to read the original target
Eq when an anchored source reaches an exposed carrier. This theorem is
conditional on `EqAnchoredRecognition`, proved in the later recognition module. -/
theorem EqAnchoredRecognition.eq_of_exposed
    (recognize : EqAnchoredRecognition D)
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hRec : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hΔ : OnCtx Δ (env.IsType univs))
    (ht : env.HasType univs Δ (eqRecBeforeMajor v w α a M minor b) T)
    (W : EqSpecializationFrame Γ₀ Γ₀ Δ σ₀ σ₀ VExpr.Subst.id ProofShape.Subst.id)
    (J : EqFrameInsertionChain Γ₀ Γ₀ VExpr.Subst.id ProofShape.Subst.id
      Λ₀ Λ₀ VExpr.Subst.id ProofShape.Subst.id blocks₀)
    (H : EqAnchoredEndpoint D Δ Γ₀ Λ₀ σ₀ blocks₀ pending₀ v w [α,a,M,minor,b] source depth)
    (HT : TypedSource (proofEraseCtx Λ₀) source)
    (R : ScopedCompute (PiInertStage D n) (proofEraseCtx Λ₀) source endpoint)
    (HE : CarrierExposure endpoint)
    (HO : ControlTyping (proofEraseCtx Λ₀) endpoint (.sort outU)) :
    env.IsDefEq univs Δ a b α := by
  obtain ⟨initial, RC₀⟩ := R.count
  obtain ⟨stage, cost, RC, HM⟩ := RC₀.minimal_across_stages
  have HK : PiInertTypedContinuationRun D (proofEraseCtx Λ₀) endpoint (proofEraseCtx Λ₀)
      (fun e k => e = endpoint ∧ k = 0) endpoint 0 :=
    .terminal (HT.pi_inert_compute heq hs RC.forget)
  rcases recognize heq hs ⟨data, hreg, hoff⟩ hRec hΔ ht W J H HT RC HK HE HO
      (by rintro later j tail k RJ ⟨rfl, rfl⟩; simpa only [Nat.add_zero] using HM later j RJ) with
    HEq | ⟨d, _, Hend⟩
  · exact HEq
  · exact (Hend.not_exposed heq HE).elim

/-- Conditional closure of the original lifted Eq probe from the exact
anchored-recognition obligation. The initial state and insertion chain are
constructed from the original lower typing and actual lift. No frontier or
scope-agreement hypothesis is substituted for the recognizer; its unconditional
instance is `pi_inert_lifted_eq_probe_descend` in the later recognition module. -/
theorem EqAnchoredRecognition.lifted_probe
    (recognize : EqAnchoredRecognition D)
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hRec : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.LiftN count offset Γ Γ')
    (ht : env.HasType univs Γ (eqRecBeforeMajor v w α a M minor b) T)
    (hn : ¬ IsProof Γ (eqRecBeforeMajor v w α a M minor b))
    (Eargs : args = (([α,a,M,minor,b].map (proofErase Γ)).map (·.liftN count offset)) ++ [.proof])
    (HT : ControlTyping (proofEraseCtx Γ') (ProofShape.mkApps (.const ``Eq.rec [v,w]) args) (.sort u))
    (R : ScopedCompute (PiInertStage D n) (proofEraseCtx Γ')
      (ProofShape.mkApps (.const ``Eq.rec [v,w]) args) out) (HE : CarrierExposure out) :
    env.IsDefEq univs Γ a b α := by
  have HTsource : TypedSource (proofEraseCtx Γ') (ProofShape.mkApps (.const ``Eq.rec [v,w]) args) := by
    obtain ⟨Ξ, e, hΞ, EΞ, he, Ee⟩ := HT
    exact ⟨Ξ, e, _, hΞ, EΞ, he, Ee⟩
  have HO := HT.compute
    (ErasedScopedPrimitiveCertificateDescent.descent (pi_inert_stage_certificate_descent heq hs n)) R
  obtain ⟨σ, pending, HP⟩ := EqPrefixSpecialization.of_typed hΓ ht
  have hp : pending = [] := by
    have HL := HP.2.2.length_eq
    simp only [List.length_append, List.length_map] at HL
    exact List.length_eq_zero_iff.mp (by omega)
  cases hp
  have WF := EqSpecializationFrame.of_conversion hΓ HP.1 (.refl hΓ)
  have I : EqFrameInsertion Γ Γ Γ' Γ' count offset
      VExpr.Subst.id ProofShape.Subst.id VExpr.Subst.id ProofShape.Subst.id := by
    refine ⟨W, W, hΓ', Ctx.SubstEq.id henv.ordered hΓ', ?_, ?_, ?_⟩
    · intro i A hl hnp
      simp only [VExpr.Subst.id, ProofShape.Subst.id, proofErase, if_neg hnp]
    · intro e; simp only [VExpr.subst_id]
    · intro e; simp only [ProofShape.subst_id]
  have J : EqFrameInsertionChain Γ Γ VExpr.Subst.id ProofShape.Subst.id Γ' Γ'
      VExpr.Subst.id ProofShape.Subst.id [(count,offset)] := EqFrameInsertionChain.refl.step I
  have Hstart : EqAnchoredEndpoint D Γ Γ Γ' σ [(count,offset)] [] v w [α,a,M,minor,b]
      (ProofShape.mkApps (.const ``Eq.rec [v,w]) args) 0 := by
    simpa only [Eargs, EqInsertionPath.erased] using
      (EqAnchoredEndpoint.of_spine (D := D) (Λ := Γ') (blocks := [(count,offset)]) HP ht hn
        (extra := [.proof]) (.inr rfl))
  exact recognize.eq_of_exposed heq hs hreg hoff hRec hΓ ht WF J Hstart HTsource R HE HO

end Lean4Lean.VEnv.Strengthening
