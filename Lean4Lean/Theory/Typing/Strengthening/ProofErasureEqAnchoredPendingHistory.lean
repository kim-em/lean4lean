import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqPendingSourceReturn

/-! # Source application witnesses throughout retained pending histories

A retained lambda records an actual source body, its original native path, and
whole application typing with the very same waiting supply. Realization updates
these witnesses by source equality and exact erasure, without substituting native
paths. Recursive recognition still has to construct and maintain this history.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private isProof_congr
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
open private nonproof_spine_head
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureRecoveredEqComputedPrefix
variable [Params]

/-- A source body and its actual computation are attached to the same lower
argument vector as the whole typed lambda application. This is stronger than
individual argument typing. The endpoint is the actual body under this frame,
including any nested wrappers, rather than an arbitrary future hole. -/
def EqRetainedSourceAnchor (D : Definitions) (Γ Λ Δ : List VExpr) (σ : VExpr.Subst)
    (blocks : EqInsertionPath) (A y : VExpr) (pending remaining : List VExpr)
    (body : ProofShape) (args : List ProofShape) : Prop :=
  OnCtx Γ (env.IsType univs) ∧ ∃ e T supplied actual extra F n,
    env.HasType univs (A :: Γ) e T ∧
    env.HasType univs Γ (VExpr.mkApps (.lam A e) actual) F ∧
    ¬ IsProof Γ (VExpr.mkApps (.lam A e) actual) ∧
    EqArgumentSupplyAt Γ Δ σ supplied actual ∧
    supplied ++ pending = y :: remaining ∧ (extra = [] ∨ pending = []) ∧
    ((actual.map (proofErase Γ)).map blocks.erased) ++ extra = args ∧
    ScopedCompute (PiInertStage D n) (proofEraseCtx (blocks.actual A :: Λ))
      (blocks.underBinder.erased (proofErase (A :: Γ) e)) body

/-- Whole source application typing implies the displayed-domain typing of a
nonempty local head, so an anchor contains the old retained supply invariant. -/
theorem EqRetainedSourceAnchor.forget
    (H : EqRetainedSourceAnchor D Γ Λ Δ σ blocks A y pending remaining body args) :
    EqRetainedArgumentSupply Γ Δ σ blocks A y pending remaining args := by
  obtain ⟨hΓ, e, T, supplied, actual, extra, F, n, _, happ, _, HS, EP, hxtra, ER, _⟩ := H
  refine ⟨supplied, actual, extra, HS, ?_, EP, hxtra, ER⟩
  intro x xs EX
  subst actual
  have Hhead : VExpr.WF env univs Γ (.app (.lam A e) x) :=
    VExpr.WF.of_mkApps henv.orderedStrong hΓ ⟨_, happ⟩
  exact HasType.app_lam_arg hΓ Hhead.choose_spec

/-- An actual function eta body initializes an anchor. The function's whole
application typing and the stored actual supply give the lambda application's
typing by eta equality; its body path remains in the original fresh scope. -/
theorem EqRetainedSourceAnchor.of_eta
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (.forallE A B))
    (happ : env.HasType univs Γ (VExpr.mkApps f actual) F)
    (hn : ¬ IsProof Γ (VExpr.mkApps f actual))
    (HS : EqArgumentSupplyAt Γ Δ σ supplied actual)
    (EP : supplied ++ pending = y :: remaining)
    (hxtra : extra = [] ∨ pending = [])
    (ER : ((actual.map (proofErase Γ)).map blocks.erased) ++ extra = args)
    (RB : ScopedCompute (PiInertStage D n) (proofEraseCtx (blocks.actual A :: Λ))
      (blocks.underBinder.erased (proofErase (A :: Γ) (.app f.lift (.bvar 0)))) body) :
    EqRetainedSourceAnchor D Γ Λ Δ σ blocks A y pending remaining body args := by
  have hfw : env.HasType univs (A :: Γ) f.lift (.forallE A.lift (B.liftN 1 1)) := hf.weak henv
  have hb : env.HasType univs (A :: Γ) (.app f.lift (.bvar 0)) B := by
    simpa only [VExpr.inst_liftN_bvar] using hfw.app (HasType.bvar .zero)
  have HE := (IsDefEqU.mkApps_args hΓ (IsDefEq.eta hf).symm.toU
    (List.Forall₂.rfl HS.1) happ).of_l henv hΓ happ
  exact ⟨hΓ, _, B, supplied, actual, extra, F, n, hb, HE.hasType.2,
    (fun hp => hn ((isProof_congr hΓ HE).2 hp)), HS, EP, hxtra, ER, RB⟩

/-- Realize a retained source anchor through the actual square below its binder.
The domain equality aligns the old lambda with the newly realized body, keeping
whole application typing and the same chosen images. The outgoing body path is
reflexive at its realized source; no native computation is substituted. -/
theorem EqRetainedSourceAnchor.frame
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΔ : OnCtx Δ (env.IsType univs))
    (H : EqRetainedSourceAnchor D Γ Λ Δ σ incoming A y pending remaining body args)
    (Q : EqSupplyInsertionSquare Γ Γ' Δ σ σ' ρ τ Λ Λ' κ υ incoming outgoing)
    (HAB : env.IsDefEq univs Γ A B (.sort u))
    (QB : EqSupplyInsertionSquare (A :: Γ) (B.subst ρ :: Γ') Δ (σ.cons y) (σ'.cons y)
      ρ.lift τ.lift (incoming.actual A :: Λ) (outgoing.actual (B.subst ρ) :: Λ')
      κ.lift υ.lift incoming.underBinder outgoing.underBinder) :
    EqRetainedSourceAnchor D Γ' Λ' Δ σ' outgoing (B.subst ρ) y pending remaining
      (body.subst υ.lift) (args.map (·.subst υ)) := by
  obtain ⟨_, e, T, supplied, actual, extra, F, n, he, happ, hn, HS, EP, hxtra, ER, RB⟩ := H
  obtain ⟨e', HE, EE⟩ := QB.compute_source_return
    (pi_inert_stage_certificate_descent heq hs n) hΔ he RB
  obtain ⟨HS', ES⟩ := HS.frame hΔ Q.lower
  have HD := HAB.subst henv.orderedStrong Q.lower.actual Q.lower.target.wf
  have HL := (IsDefEq.lamDF HD.symm HE.symm).symm.toU
  have happ' : env.HasType univs Γ'
      (VExpr.mkApps (.lam (A.subst ρ) (e.subst ρ.lift)) (actual.map (·.subst ρ))) (F.subst ρ) := by
    simpa only [VExpr.subst_mkApps, VExpr.subst] using
      happ.subst henv.orderedStrong Q.lower.actual Q.lower.target.wf
  have HEwhole := (IsDefEqU.mkApps_args Q.lower.target.wf HL
    (List.Forall₂.rfl HS'.1) happ').of_l henv Q.lower.target.wf happ'
  have hn' : ¬ IsProof Γ'
      (VExpr.mkApps (.lam (B.subst ρ) e') (actual.map (·.subst ρ))) := by
    intro hp
    apply hn
    apply (isProof_subst Q.lower.target.wf Q.lower.actual happ).1
    simpa only [VExpr.subst_mkApps, VExpr.subst] using
      (isProof_congr Q.lower.target.wf HEwhole).2 hp
  refine ⟨Q.lower.target.wf, e', T.subst ρ.lift, supplied, actual.map (·.subst ρ),
    extra.map (·.subst υ), F.subst ρ, 0, HE.hasType.2, HEwhole.hasType.2, hn', HS', EP, ?_, ?_, ?_⟩
  · rcases hxtra with rfl | h
    · exact .inl rfl
    · exact .inr h
  · rw [ES, ← ER]
    simp only [List.map_append, List.map_map, Function.comp_def, Q.erased]
  · rw [EE]; exact .refl

/-- Extend the actual body path at a retained source anchor. Its original
whole application witness and actual waiting vector stay attached to the new
endpoint; the finite stage increases only to the maximum of the two paths. -/
theorem EqRetainedSourceAnchor.compute_body
    (H : EqRetainedSourceAnchor D Γ Λ Δ σ blocks A y pending remaining body args)
    (RB : ScopedCompute (PiInertStage D n) (proofEraseCtx (blocks.actual A :: Λ)) body body') :
    EqRetainedSourceAnchor D Γ Λ Δ σ blocks A y pending remaining body' args := by
  obtain ⟨hΓ, e, T, supplied, actual, extra, F, m, he, happ, hn, HS, EP, hxtra, ER, R⟩ := H
  exact ⟨hΓ, e, T, supplied, actual, extra, F, max m n, he, happ, hn, HS, EP, hxtra, ER,
    (R.mono (pi_inert_stage_mono (Nat.le_max_left m n))).trans
      (RB.mono (pi_inert_stage_mono (Nat.le_max_right m n)))⟩

omit [Params] in
private theorem erased_mkApps (blocks : EqInsertionPath) (f : ProofShape) (args : List ProofShape) :
    blocks.erased (ProofShape.mkApps f args) =
      ProofShape.mkApps (blocks.erased f) (args.map blocks.erased) := by
  induction args generalizing f with
  | nil => rfl
  | cons a args ih => simpa only [ProofShape.mkApps, List.map_cons, EqInsertionPath.erased_app] using ih (.app f a)

private theorem compute_common_endpoint
    (hfirst : ErasedScopedPrimitiveCertificateDescent First First)
    (hsecond : ErasedScopedPrimitiveCertificateDescent Second Second)
    (W : EqSpecializationFrame Γ Γ' Δ σ σ' ρ τ)
    (J : EqFrameInsertionChain Γ Γ' ρ τ Λ Λ' κ υ blocks)
    (hf : env.HasType univs Γ f F) (hg : env.HasType univs Γ g G)
    (hng : ¬ IsProof Γ g)
    (RF : ScopedCompute First (proofEraseCtx Λ) (blocks.erased (proofErase Γ f)) raw)
    (RG : ScopedCompute Second (proofEraseCtx Λ) (blocks.erased (proofErase Γ g)) raw) :
    env.IsDefEqU univs Γ f g := by
  obtain ⟨f', HF, _, EF⟩ := J.compute_certificate hfirst W hf RF
  obtain ⟨g', HG, _, EG⟩ := J.compute_certificate hsecond W hg RG
  have hn' : ¬ IsProof Γ g' := fun hp => hng ((isProof_congr W.actual.wf HG).2 hp)
  obtain ⟨_, HE⟩ := (proofErase_reflect W.actual.wf HG.hasType.2 HF.hasType.2
    (blocks.erased_injective (EG.trans EF.symm))).2 hn'
  exact HF.toU.trans henv W.actual.wf
    (((HE.defeq W.actual.wf).symm).trans henv W.actual.wf HG.symm.toU)

/-- Restore a waiting supply to a retained source anchor. When waiting actual
arguments are present, the original local lambda application and the returned
function compute to the same whole endpoint, so erasure reflection transfers
whole application typing. A nonempty untracked local extra forces the waiting
tracked vector to be empty. No dependent typing is inferred from individual
argument typings. -/
theorem EqRetainedSourceAnchor.append_supply
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hstep : ErasedScopedPrimitiveCertificateDescent Step Step)
    (H : EqRetainedSourceAnchor D Γ Λ Δ σ blocks A y (supplied ++ pending) remaining body args)
    (W : EqSpecializationFrame Γ Γ' Δ σ σ' ρ τ)
    (J : EqFrameInsertionChain Γ Γ' ρ τ Λ Λ' κ υ blocks)
    (hA : env.HasType univs Γ A (.sort u))
    (RD : ScopedCompute (PiInertStage D n) (proofEraseCtx Λ)
      (blocks.erased (proofErase Γ A)) rawA)
    (HS : EqArgumentSupplyAt Γ Δ σ supplied actual)
    (hextra : extra = [] ∨ pending = [])
    (happ : env.HasType univs Γ (VExpr.mkApps f actual) T)
    (hn : ¬ IsProof Γ (VExpr.mkApps f actual))
    (RF : ScopedCompute Step (proofEraseCtx Λ) (blocks.erased (proofErase Γ f))
      (ProofShape.mkApps (.lam rawA body) args)) :
    EqRetainedSourceAnchor D Γ Λ Δ σ blocks A y pending remaining body
      (args ++ (((actual.map (proofErase Γ)).map blocks.erased) ++ extra)) := by
  obtain ⟨hΓ, e, E, localChosen, localActual, localExtra, F, m,
    he, hlocal, hnlocal, HL, EP, hlocalExtra, ER, RB⟩ := H
  have HSnil : supplied = [] → actual = [] := by
    intro he
    have hlen := HS.2.length_eq
    simp only [he, List.length_nil, List.length_map] at hlen
    exact List.length_eq_zero_iff.mp hlen.symm
  have Horder : localExtra = [] ∨ actual = [] := by
    rcases hlocalExtra with h | h
    · exact .inl h
    · exact .inr (HSnil (List.append_eq_nil_iff.mp h).1)
  have Hwhole : ∃ G, env.HasType univs Γ (VExpr.mkApps (.lam A e) (localActual ++ actual)) G ∧
      ¬ IsProof Γ (VExpr.mkApps (.lam A e) (localActual ++ actual)) := by
    rcases Horder with hlocalEmpty | hactualEmpty
    · have hnlam := nonproof_spine_head hΓ hlocal hnlocal
      have RB' : ScopedCompute (PiInertStage D (max n m))
          (blocks.erased (proofErase Γ A) :: proofEraseCtx Λ)
          (blocks.underBinder.erased (proofErase (A :: Γ) e)) body := by
        simpa only [proofEraseCtx, J.erase_actual W hA] using
          RB.mono (pi_inert_stage_mono (Nat.le_max_right n m))
      have RL : ScopedCompute (PiInertStage D (max n m)) (proofEraseCtx Λ)
          (blocks.erased (proofErase Γ (VExpr.mkApps (.lam A e) localActual)))
          (ProofShape.mkApps (.lam rawA body) args) := by
        have EL : ((localActual.map (proofErase Γ)).map blocks.erased) = args := by
          simpa only [hlocalEmpty, List.append_nil] using ER
        rw [proofErase_mkApps hΓ hlocal hnlocal, erased_mkApps,
          show proofErase Γ (.lam A e) = .lam (proofErase Γ A) (proofErase (A :: Γ) e) from
            by simp only [proofErase, if_neg hnlam], EqInsertionPath.erased_lam, ← EL]
        exact ((RD.mono (pi_inert_stage_mono (Nat.le_max_left n m))).lam RB').mkApps
          (List.Forall₂.rfl (fun _ _ => .refl))
      obtain ⟨Tf, hf⟩ := VExpr.WF.of_mkApps henv.orderedStrong hΓ ⟨_, happ⟩
      have HE := compute_common_endpoint hstep (pi_inert_stage_certificate_descent heq hs (max n m))
        W J hf hlocal hnlocal RF RL
      have HEwhole := (IsDefEqU.mkApps_args hΓ HE (List.Forall₂.rfl HS.1) happ).of_l henv hΓ happ
      refine ⟨T, ?_, ?_⟩
      · simpa only [VExpr.mkApps_append] using HEwhole.hasType.2
      · simpa only [VExpr.mkApps_append] using
          (show ¬ IsProof Γ (VExpr.mkApps (VExpr.mkApps (.lam A e) localActual) actual) from
            fun hp => hn ((isProof_congr hΓ HEwhole).2 hp))
    · subst actual
      exact ⟨F, by simpa only [List.append_nil] using hlocal,
        by simpa only [List.append_nil] using hnlocal⟩
  obtain ⟨G, hwhole, hnwhole⟩ := Hwhole
  refine ⟨hΓ, e, E, localChosen ++ supplied, localActual ++ actual, localExtra ++ extra, G, m,
    he, hwhole, hnwhole, ⟨?_, ?_⟩, ?_, ?_, ?_, RB⟩
  · intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact HL.1 a ha
    · exact HS.1 a ha
  · simpa only [List.map_append] using HL.2.append' HS.2
  · simpa only [List.append_assoc] using EP
  · rcases hlocalExtra with h | h
    · rcases hextra with h' | h'
      · exact .inl (by simp only [h, h', List.append_nil])
      · exact .inr h'
    · exact .inr (List.append_eq_nil_iff.mp h).2
  · rw [← ER]
    rcases Horder with rfl | rfl
    · simp only [List.map_append, List.nil_append, List.append_nil, List.append_assoc]
    · simp only [List.map_nil, List.nil_append, List.append_nil, List.append_assoc]

/-- A pending history whose chosen retained frames all retain source application
witnesses for this actual endpoint. A parent's endpoint includes its complete
child wrapper. Unused frames need no chosen argument witness. Producing this
history through every recursive cut remains a separate recognition obligation. -/
inductive EqAnchoredPendingHistory (D : Definitions) (Δ Γ₀ Λ₀ : List VExpr)
    (σ₀ : VExpr.Subst) (blocks₀ : EqInsertionPath) (pending₀ : List VExpr)
    (Ψ₀ : List ProofShape) (υ₀ : ProofShape.Subst) :
    List VExpr → List VExpr → VExpr.Subst → EqInsertionPath → List VExpr →
    List ProofShape → ProofShape.Subst → (ProofShape → ProofShape) → ProofShape → Nat → Nat → Prop where
  | base : EqAnchoredPendingHistory D Δ Γ₀ Λ₀ σ₀ blocks₀ pending₀ Ψ₀ υ₀
      Γ₀ Λ₀ σ₀ blocks₀ pending₀ Ψ₀ υ₀ id body 0 0
  | retained : EqAnchoredPendingHistory D Δ Γ₀ Λ₀ σ₀ blocks₀ pending₀ Ψ₀ υ₀
        Γ Λ σ blocks pending Ψ υ plug (ProofShape.mkApps (.lam rawA body) args) chosen depth →
      env.HasType univs Γ A (.sort u) → env.HasType univs Δ y (A.subst σ) →
      ScopedComputeCount (PiInertStage D n) cd (proofEraseCtx Λ)
        (blocks.erased (proofErase Γ A)) rawA →
      EqRetainedSourceAnchor D Γ Λ Δ σ blocks A y pending remaining body args →
      EqAnchoredPendingHistory D Δ Γ₀ Λ₀ σ₀ blocks₀ pending₀ Ψ₀ υ₀
        (A :: Γ) (blocks.actual A :: Λ) (σ.cons y) blocks.underBinder remaining
        (rawA.subst υ :: Ψ) υ.lift
        (fun e => plug (ProofShape.mkApps (.lam rawA e) args)) body (chosen+1) (depth+1)
  | unused : EqAnchoredPendingHistory D Δ Γ₀ Λ₀ σ₀ blocks₀ pending₀ Ψ₀ υ₀
        Γ Λ σ blocks [] Ψ υ plug (ProofShape.mkApps (.lam rawA body) args) chosen depth →
      env.HasType univs Λ A (.sort u) →
      ScopedComputeCount (PiInertStage D n) cd (proofEraseCtx Λ) (proofErase Λ A) rawA →
      EqAnchoredPendingHistory D Δ Γ₀ Λ₀ σ₀ blocks₀ pending₀ Ψ₀ υ₀
        Γ (A :: Λ) σ (blocks ++ [(1,0)]) [] (rawA.subst υ :: Ψ) υ.lift
        (fun e => plug (ProofShape.mkApps (.lam rawA e) args)) body chosen (depth+1)

/-- Forget source witnesses while retaining the exact pending supplies, wrapper,
contexts, maps and binder counts of the existing history. -/
theorem EqAnchoredPendingHistory.forget
    (H : EqAnchoredPendingHistory D Δ Γ₀ Λ₀ σ₀ blocks₀ pending₀ Ψ₀ υ₀
      Γ Λ σ blocks pending Ψ υ plug body chosen depth) :
    EqPendingSupplyHistory D Δ Γ₀ Λ₀ σ₀ blocks₀ pending₀ Ψ₀ υ₀
      Γ Λ σ blocks pending Ψ υ plug chosen depth := by
  induction H with
  | base => exact .base
  | retained _ hA hy RD HA ih => exact .retained ih hA hy RD HA.forget
  | unused _ hA RD ih => exact .unused ih hA RD

/-- Realize every source application witness throughout a finite history.
Each retained frame reifies its original body path at the outgoing scope, and
all outgoing annotations receive reflexive paths at their computed domains.
The actual endpoint, pending images, wrapper equation and both counts survive.
No endpoint-recognition or output-depth bound is assumed or proved here. -/
theorem EqAnchoredPendingHistory.realize_returning
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΔ : OnCtx Δ (env.IsType univs))
    (H : EqAnchoredPendingHistory D Δ Γ₀ Λ₀ σ₀ incoming pending₀ Ψ₀ υ₀
      Γ Λ σ blocks pending Ψ υ plug body chosen depth)
    (Q : EqSupplyInsertionSquare Γ₀ Γ₀' Δ σ₀ σ₀' ρ₀ τ₀ Λ₀ Λ₀' κ₀ υ₀ incoming outgoing)
    (EΨ : Ψ₀ = proofEraseCtx Λ₀') :
    ∃ (Γ' Λ' : List VExpr) (σ' : VExpr.Subst) (outblocks : EqInsertionPath) (plug' : ProofShape → ProofShape),
      EqSupplyInsertionSquare Γ Γ' Δ σ σ' (ρ₀.liftN chosen) (τ₀.liftN chosen)
        Λ Λ' (κ₀.liftN depth) υ blocks outblocks ∧ Ψ = proofEraseCtx Λ' ∧
      EqAnchoredPendingHistory D Δ Γ₀' Λ₀' σ₀' outgoing pending₀ (proofEraseCtx Λ₀') ProofShape.Subst.id
        Γ' Λ' σ' outblocks pending (proofEraseCtx Λ') ProofShape.Subst.id plug' (body.subst υ) chosen depth ∧
      ∀ e : ProofShape, (plug e).subst υ₀ = plug' (e.subst υ) := by
  induction H with
  | base => exact ⟨Γ₀', Λ₀', σ₀', outgoing, id, Q, EΨ, .base, fun _ => rfl⟩
  | @retained Γ Λ σ blocks pending Ψ υ plug rawA' body args chosen depth A u y n cd remaining H hA hy RD HA ih =>
    obtain ⟨Γ', Λ', σ', outblocks, plug', Q, EΨ, HR, EW⟩ := ih
    obtain ⟨B, HAB, _, Qnew, EB⟩ := Q.retained heq hs hΔ hA hy RD.forget
    have hBout : env.HasType univs Γ' (B.subst (ρ₀.liftN chosen)) (.sort u) := by
      simpa only [VExpr.subst] using HAB.hasType.2.subst henv.orderedStrong Q.lower.actual Q.lower.target.wf
    have hyout : env.HasType univs Δ y ((B.subst (ρ₀.liftN chosen)).subst σ') := by
      cases Qnew.lower.target with | cons _ _ hy => exact hy.hasType.1
    have WT := EqSpecializationFrame.of_conversion hΔ Q.lower.target (.refl Q.lower.target.wf)
    have ER : outblocks.erased (proofErase Γ' (B.subst (ρ₀.liftN chosen))) = rawA'.subst υ :=
      (Q.target.erase_actual WT hBout).symm.trans EB
    have RDout : ScopedComputeCount (PiInertStage D 0) 0 (proofEraseCtx Λ')
        (outblocks.erased (proofErase Γ' (B.subst (ρ₀.liftN chosen)))) (rawA'.subst υ) := by
      rw [ER]; exact .beta .refl
    have HRnew := EqAnchoredPendingHistory.retained (args := args.map (·.subst υ)) (by simpa only [ProofShape.subst_mkApps, ProofShape.subst] using HR) hBout hyout RDout (HA.frame heq hs hΔ Q HAB Qnew)
    refine ⟨_, _, _, _, (fun e => plug' (ProofShape.mkApps (.lam (rawA'.subst υ) e) (args.map (·.subst υ)))),
      Qnew, (by simp only [proofEraseCtx, ← EΨ, EB]), ?_, ?_⟩
    · simpa only [ProofShape.Subst.id_lift, ProofShape.subst_id, proofEraseCtx, EB] using HRnew
    · intro e
      simpa only [ProofShape.subst_mkApps, ProofShape.subst] using EW (ProofShape.mkApps (.lam rawA' e) args)
  | @unused Γ Λ σ blocks Ψ υ plug rawA' body args chosen depth A u n cd H hA RD ih =>
    obtain ⟨Γ', Λ', σ', outblocks, plug', Q, EΨ, HR, EW⟩ := ih
    obtain ⟨B, HAB, _, Qnew, EB⟩ := Q.unused heq hs hΔ hA RD.forget
    have hBout : env.HasType univs Λ' (B.subst (κ₀.liftN depth)) (.sort u) := by
      simpa only [VExpr.subst] using HAB.hasType.2.subst henv.orderedStrong Q.actual Q.target_wf
    have RDout : ScopedComputeCount (PiInertStage D 0) 0 (proofEraseCtx Λ')
        (proofErase Λ' (B.subst (κ₀.liftN depth))) (rawA'.subst υ) := by
      rw [EB]; exact .beta .refl
    have HRnew := EqAnchoredPendingHistory.unused (args := args.map (·.subst υ)) (by simpa only [ProofShape.subst_mkApps, ProofShape.subst] using HR) hBout RDout
    refine ⟨_, _, _, _, (fun e => plug' (ProofShape.mkApps (.lam (rawA'.subst υ) e) (args.map (·.subst υ)))),
      Qnew, (by simp only [proofEraseCtx, ← EΨ, EB]), ?_, ?_⟩
    · simpa only [ProofShape.Subst.id_lift, ProofShape.subst_id, proofEraseCtx, EB] using HRnew
    · intro e
      simpa only [ProofShape.subst_mkApps, ProofShape.subst] using EW (ProofShape.mkApps (.lam rawA' e) args)

/-- Identity outgoing placeholders remain identity under every chosen or
unused binder. This allows final context agreement to read every displayed
annotation of a realized history. -/
theorem EqAnchoredPendingHistory.endpoint_map_eq_id
    (H : EqAnchoredPendingHistory D Δ Γ₀ Λ₀ σ₀ blocks₀ pending₀ Ψ₀ υ₀
      Γ Λ σ blocks pending Ψ υ plug body chosen depth)
    (E : υ₀ = ProofShape.Subst.id) : υ = ProofShape.Subst.id := by
  induction H with
  | base => exact E
  | retained _ _ _ _ _ ih => rw [ih, ProofShape.Subst.id_lift]
  | unused _ _ _ ih => rw [ih, ProofShape.Subst.id_lift]

/-- Actual computation of the current body preserves every enclosing source
application witness in a realized history. Identity placeholders and final
context agreement imply that each displayed annotation is already the actual
source domain. Thus the path can be wrapped at each frame in its original
context, without a conversion or substitution principle for native paths. -/
theorem EqAnchoredPendingHistory.compute_body
    (Eυ₀ : υ₀ = ProofShape.Subst.id)
    (H : EqAnchoredPendingHistory D Δ Γ₀ Λ₀ σ₀ blocks₀ pending₀ Ψ₀ υ₀
      Γ Λ σ blocks pending Ψ υ plug body chosen depth)
    (EΨ : Ψ = proofEraseCtx Λ)
    (RB : ScopedCompute (PiInertStage D n) (proofEraseCtx Λ) body body') :
    EqAnchoredPendingHistory D Δ Γ₀ Λ₀ σ₀ blocks₀ pending₀ Ψ₀ υ₀
      Γ Λ σ blocks pending Ψ υ plug body' chosen depth := by
  revert EΨ RB
  induction H generalizing body' with
  | base => intro _ _; exact .base
  | @retained Γ Λ σ blocks pending Ψ υ plug rawA body args chosen depth A u y m cd remaining H hA hy RD HA ih =>
    intro EΨ RB
    have EI := H.endpoint_map_eq_id Eυ₀
    have EP : rawA = proofErase Λ (blocks.actual A) ∧ Ψ = proofEraseCtx Λ := by
      simpa only [proofEraseCtx, EI, ProofShape.subst_id, List.cons.injEq] using EΨ
    have RB' : ScopedCompute (PiInertStage D n) (rawA :: proofEraseCtx Λ) body body' := by
      simpa only [proofEraseCtx, EP.1] using RB
    have RW : ScopedCompute (PiInertStage D n) (proofEraseCtx Λ)
        (ProofShape.mkApps (.lam rawA body) args) (ProofShape.mkApps (.lam rawA body') args) :=
      (ScopedCompute.lam .refl RB').mkApps (List.Forall₂.rfl (fun _ _ => .refl))
    exact .retained (ih EP.2 RW) hA hy RD (HA.compute_body RB)
  | @unused Γ Λ σ blocks Ψ υ plug rawA body args chosen depth A u m cd H hA RD ih =>
    intro EΨ RB
    have EI := H.endpoint_map_eq_id Eυ₀
    have EP : rawA = proofErase Λ A ∧ Ψ = proofEraseCtx Λ := by
      simpa only [proofEraseCtx, EI, ProofShape.subst_id, List.cons.injEq] using EΨ
    have RB' : ScopedCompute (PiInertStage D n) (rawA :: proofEraseCtx Λ) body body' := by
      simpa only [proofEraseCtx, EP.1] using RB
    have RW : ScopedCompute (PiInertStage D n) (proofEraseCtx Λ)
        (ProofShape.mkApps (.lam rawA body) args) (ProofShape.mkApps (.lam rawA body') args) :=
      (ScopedCompute.lam .refl RB').mkApps (List.Forall₂.rfl (fun _ _ => .refl))
    exact .unused (ih EP.2 RW) hA RD

/-- Rebase outgoing placeholders without changing source witnesses or the
actual current body. This operation does not transport a native path. -/
theorem EqAnchoredPendingHistory.rebase_endpoint
    (H : EqAnchoredPendingHistory D Δ Γ₀ Λ₀ σ₀ blocks₀ pending₀ Ψ₀ υ₀
      Γ Λ σ blocks pending Ψ υ plug body chosen depth)
    (newTarget : List ProofShape) (newMap : ProofShape.Subst) :
    ∃ Ψ' υ', EqAnchoredPendingHistory D Δ Γ₀ Λ₀ σ₀ blocks₀ pending₀ newTarget newMap
      Γ Λ σ blocks pending Ψ' υ' plug body chosen depth := by
  induction H with
  | base => exact ⟨_, _, .base⟩
  | retained _ hA hy RD HA ih =>
    obtain ⟨Ψ', υ', HR⟩ := ih
    exact ⟨_, _, .retained HR hA hy RD HA⟩
  | unused _ hA RD ih =>
    obtain ⟨Ψ', υ', HR⟩ := ih
    exact ⟨_, _, .unused HR hA RD⟩

/-- Join two histories with source witnesses for the same actual intermediate
endpoint. The older history must be anchored at the complete younger wrapper;
its witnesses therefore remain tied to the exact joined body. -/
theorem EqAnchoredPendingHistory.append
    (K : EqAnchoredPendingHistory D Δ Γ₁ Λ₁ σ₁ blocks₁ pending₁ Ψ₁ υ₁
      Γ₂ Λ₂ σ₂ blocks₂ pending₂ Ψ₂ υ₂ plug₂ body chosen₂ depth₂)
    (H : EqAnchoredPendingHistory D Δ Γ₀ Λ₀ σ₀ blocks₀ pending₀ Ψ₀ υ₀
      Γ₁ Λ₁ σ₁ blocks₁ pending₁ Ψ₁ υ₁ plug₁ (plug₂ body) chosen₁ depth₁) :
    EqAnchoredPendingHistory D Δ Γ₀ Λ₀ σ₀ blocks₀ pending₀ Ψ₀ υ₀
      Γ₂ Λ₂ σ₂ blocks₂ pending₂ Ψ₂ υ₂ (fun e => plug₁ (plug₂ e)) body
      (chosen₁+chosen₂) (depth₁+depth₂) := by
  revert H
  induction K with
  | base => intro H; simpa only [id_eq, Nat.add_zero] using H
  | retained _ hA hy RD HA ih =>
    intro H
    simpa only [Nat.add_assoc] using EqAnchoredPendingHistory.retained (ih H) hA hy RD HA
  | unused _ hA RD ih =>
    intro H
    simpa only [Nat.add_assoc] using EqAnchoredPendingHistory.unused (ih H) hA RD

/-- Restore a waiting supply to the actual outer frame while preserving all
source application witnesses. The returned whole function supplies typing and
nonproofness of the enlarged application; the anchor's native path and chosen
images remain attached. This does not construct the recursively returned history. -/
theorem EqAnchoredPendingHistory.append_outer_supply
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hstep : ErasedScopedPrimitiveCertificateDescent Step Step)
    (H : EqAnchoredPendingHistory D Δ Γ₀ Λ₀ σ₀ blocks₀ basePending Ψ₀ υ₀
      Γ Λ σ blocks pending Ψ υ plug body chosen depth)
    (W : EqSpecializationFrame Γ₀ Γ₀' Δ σ₀ σ₀' ρ τ)
    (J : EqFrameInsertionChain Γ₀ Γ₀' ρ τ Λ₀ Λ₀' κ ω blocks₀)
    (EP : basePending = supplied ++ pending₀)
    (HS : EqArgumentSupplyAt Γ₀ Δ σ₀ supplied actual)
    (hextra : extra = [] ∨ pending₀ = [])
    (happ : env.HasType univs Γ₀ (VExpr.mkApps f actual) T)
    (hn : ¬ IsProof Γ₀ (VExpr.mkApps f actual))
    (RF : ScopedCompute Step (proofEraseCtx Λ₀)
      (blocks₀.erased (proofErase Γ₀ f)) (plug body))
    (hd : 0 < depth) :
    ∃ plug', EqAnchoredPendingHistory D Δ Γ₀ Λ₀ σ₀ blocks₀ pending₀ Ψ₀ υ₀
      Γ Λ σ blocks pending Ψ υ plug' body chosen depth ∧
      ∀ b, plug' b = ProofShape.mkApps (plug b)
        (((actual.map (proofErase Γ₀)).map blocks₀.erased) ++ extra) := by
  revert RF hd
  induction H with
  | base => intro _ hd; omega
  | @retained Γ Λ σ blocks pending Ψ υ plug rawA body args chosen depth A u y n cd remaining H hA hy RD HA ih =>
    intro RF hd
    by_cases hz : depth = 0
    · subst depth
      cases H with
      | base =>
        have HA : EqRetainedSourceAnchor D Γ₀ Λ₀ Δ σ₀ blocks₀ A y
            (supplied ++ pending₀) remaining body args := by simpa only [EP] using HA
        have HA' := HA.append_supply heq hs hstep W J hA RD.forget HS hextra happ hn RF
        refine ⟨_, EqAnchoredPendingHistory.retained (args := args ++
          (((actual.map (proofErase Γ₀)).map blocks₀.erased) ++ extra)) .base hA hy RD HA', ?_⟩
        intro b; exact ProofShape.mkApps_append _ _ _
    · obtain ⟨plug', HR, EW⟩ := ih RF (by omega)
      exact ⟨_, EqAnchoredPendingHistory.retained HR hA hy RD HA,
        fun b => EW (ProofShape.mkApps (.lam rawA b) args)⟩
  | @unused Γ Λ σ blocks Ψ υ plug rawA body args chosen depth A u n cd H hA RD ih =>
    intro RF hd
    by_cases hz : depth = 0
    · subst depth
      cases H with
      | base =>
        have hp : pending₀ = [] := (List.append_eq_nil_iff.mp EP.symm).2
        subst pending₀
        refine ⟨_, EqAnchoredPendingHistory.unused (args := args ++
          (((actual.map (proofErase Γ₀)).map blocks₀.erased) ++ extra)) .base hA RD, ?_⟩
        intro b; exact ProofShape.mkApps_append _ _ _
    · obtain ⟨plug', HR, EW⟩ := ih RF (by omega)
      exact ⟨_, EqAnchoredPendingHistory.unused HR hA RD,
        fun b => EW (ProofShape.mkApps (.lam rawA b) args)⟩

/-- Expose the outer source frame together with its actual body anchor and
anchored inner history. The anchor endpoint is exactly the inner wrapper applied
to the current body. This supplies the original whole application witness for
consumption after a later recursive body readout; recognition remains unproved. -/
theorem EqAnchoredPendingHistory.outermost
    (H : EqAnchoredPendingHistory D Δ Γ₀ Λ₀ σ₀ blocks₀ pending₀ Ψ₀ υ₀
      Γ Λ σ blocks pending Ψ υ plug body chosen depth)
    (hd : 0 < depth) :
    (∃ A u y rawA args remaining n cd inner chosen' depth',
      env.HasType univs Γ₀ A (.sort u) ∧ env.HasType univs Δ y (A.subst σ₀) ∧
      ScopedComputeCount (PiInertStage D n) cd (proofEraseCtx Λ₀)
        (blocks₀.erased (proofErase Γ₀ A)) rawA ∧
      EqRetainedSourceAnchor D Γ₀ Λ₀ Δ σ₀ blocks₀ A y pending₀ remaining (inner body) args ∧
      EqAnchoredPendingHistory D Δ (A :: Γ₀) (blocks₀.actual A :: Λ₀) (σ₀.cons y)
        blocks₀.underBinder remaining (rawA.subst υ₀ :: Ψ₀) υ₀.lift
        Γ Λ σ blocks pending Ψ υ inner body chosen' depth' ∧
      chosen = chosen'+1 ∧ depth = depth'+1 ∧
      ∀ e, plug e = ProofShape.mkApps (.lam rawA (inner e)) args) ∨
    (∃ A u rawA args n cd inner depth', pending₀ = [] ∧
      env.HasType univs Λ₀ A (.sort u) ∧
      ScopedComputeCount (PiInertStage D n) cd (proofEraseCtx Λ₀) (proofErase Λ₀ A) rawA ∧
      EqAnchoredPendingHistory D Δ Γ₀ (A :: Λ₀) σ₀ (blocks₀ ++ [(1,0)]) []
        (rawA.subst υ₀ :: Ψ₀) υ₀.lift Γ Λ σ blocks pending Ψ υ inner body chosen depth' ∧
      depth = depth'+1 ∧ ∀ e, plug e = ProofShape.mkApps (.lam rawA (inner e)) args) := by
  induction H with
  | base => omega
  | @retained Γ Λ σ blocks pending Ψ υ plug rawA' body args chosen depth A u y n cd remaining H hA hy RD HA ih =>
    by_cases hz : depth = 0
    · subst depth
      cases H with
      | base => exact .inl ⟨A, u, y, rawA', args, remaining, n, cd, id, 0, 0,
          hA, hy, RD, HA, .base, rfl, rfl, fun _ => rfl⟩
    · rcases ih (by omega) with
        ⟨A₀, u₀, y₀, rawA₀, args₀, remaining₀, n₀, cd₀, inner, chosen', depth',
          hA₀, hy₀, RD₀, HA₀, HI, hc, hd', EW⟩ |
        ⟨A₀, u₀, rawA₀, args₀, n₀, cd₀, inner, depth', hp, hA₀, RD₀, HI, hd', EW⟩
      · exact .inl ⟨A₀, u₀, y₀, rawA₀, args₀, remaining₀, n₀, cd₀, (fun e => inner (ProofShape.mkApps (.lam rawA' e) args)), chosen'+1, depth'+1,
          hA₀, hy₀, RD₀, HA₀, .retained HI hA hy RD HA, by omega, by omega,
          fun e => EW (ProofShape.mkApps (.lam rawA' e) args)⟩
      · exact .inr ⟨A₀, u₀, rawA₀, args₀, n₀, cd₀, (fun e => inner (ProofShape.mkApps (.lam rawA' e) args)), depth'+1,
          hp, hA₀, RD₀, .retained HI hA hy RD HA, by omega,
          fun e => EW (ProofShape.mkApps (.lam rawA' e) args)⟩
  | @unused Γ Λ σ blocks Ψ υ plug rawA' body args chosen depth A u n cd H hA RD ih =>
    by_cases hz : depth = 0
    · subst depth
      cases H with
      | base => exact .inr ⟨A, u, rawA', args, n, cd, id, 0, rfl, hA, RD, .base,
          rfl, fun _ => rfl⟩
    · rcases ih (by omega) with
        ⟨A₀, u₀, y₀, rawA₀, args₀, remaining₀, n₀, cd₀, inner, chosen', depth',
          hA₀, hy₀, RD₀, HA₀, HI, hc, hd', EW⟩ |
        ⟨A₀, u₀, rawA₀, args₀, n₀, cd₀, inner, depth', hp, hA₀, RD₀, HI, hd', EW⟩
      · exact .inl ⟨A₀, u₀, y₀, rawA₀, args₀, remaining₀, n₀, cd₀, (fun e => inner (ProofShape.mkApps (.lam rawA' e) args)), chosen', depth'+1,
          hA₀, hy₀, RD₀, HA₀, .unused HI hA RD, hc, by omega,
          fun e => EW (ProofShape.mkApps (.lam rawA' e) args)⟩
      · exact .inr ⟨A₀, u₀, rawA₀, args₀, n₀, cd₀, (fun e => inner (ProofShape.mkApps (.lam rawA' e) args)), depth'+1,
          hp, hA₀, RD₀, .unused HI hA RD, by omega,
          fun e => EW (ProofShape.mkApps (.lam rawA' e) args)⟩

end Lean4Lean.VEnv.Strengthening
