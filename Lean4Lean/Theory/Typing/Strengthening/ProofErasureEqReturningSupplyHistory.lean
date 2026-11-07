import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqInterleavedSupplyHistory

/-! # Rebuild and rejoin ancestry after supplied consumption

Realization already determines every outgoing computed annotation. Record
reflexive paths at those annotations, rather than substituting old guarded
paths. The resulting source history carries the exact substituted wrapper and
can be appended to an older history.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params]

/-- Compose two actual source histories at their shared lower/upper scope.
The wrapper composition and both binder counts are exact. -/
theorem EqInterleavedSupplyHistory.append
    (H : EqInterleavedSupplyHistory D Δ Γ₀ Λ₀ σ₀ blocks₀ Ψ₀ υ₀
      Γ₁ Λ₁ σ₁ blocks₁ Ψ₁ υ₁ plug₁ chosen₁ depth₁)
    (K : EqInterleavedSupplyHistory D Δ Γ₁ Λ₁ σ₁ blocks₁ Ψ₁ υ₁
      Γ₂ Λ₂ σ₂ blocks₂ Ψ₂ υ₂ plug₂ chosen₂ depth₂) :
    EqInterleavedSupplyHistory D Δ Γ₀ Λ₀ σ₀ blocks₀ Ψ₀ υ₀
      Γ₂ Λ₂ σ₂ blocks₂ Ψ₂ υ₂ (fun e => plug₁ (plug₂ e)) (chosen₁+chosen₂) (depth₁+depth₂) := by
  induction K with
  | base => simpa only [id_eq, Nat.add_zero] using H
  | retained _ hA hy RD ih =>
    simpa only [Nat.add_assoc] using EqInterleavedSupplyHistory.retained ih hA hy RD
  | unused _ hA RD ih =>
    simpa only [Nat.add_assoc] using EqInterleavedSupplyHistory.unused ih hA RD

/-- Fill an inner history's outgoing placeholders from an older source history
before joining them. Original source paths and wrappers are unchanged. -/
theorem EqInterleavedSupplyHistory.append_rebased
    (H : EqInterleavedSupplyHistory D Δ Γ₀ Λ₀ σ₀ blocks₀ Ψ₀ υ₀
      Γ₁ Λ₁ σ₁ blocks₁ Ψ₁ υ₁ plug₁ chosen₁ depth₁)
    (K : EqInterleavedSupplyHistory D Δ Γ₁ Λ₁ σ₁ blocks₁ target₂ map₂
      Γ₂ Λ₂ σ₂ blocks₂ Ψ₂ υ₂ plug₂ chosen₂ depth₂) :
    ∃ Ψ υ, EqInterleavedSupplyHistory D Δ Γ₀ Λ₀ σ₀ blocks₀ Ψ₀ υ₀
      Γ₂ Λ₂ σ₂ blocks₂ Ψ υ (fun e => plug₁ (plug₂ e)) (chosen₁+chosen₂) (depth₁+depth₂) := by
  obtain ⟨Ψ, υ, K'⟩ := K.rebase_endpoint Ψ₁ υ₁
  exact ⟨Ψ, υ, H.append K'⟩

/-- Realization also rebuilds a source history on its outgoing side. Each
annotation path there is reflexive at the computed substituted domain; no old
guarded path is transported. The wrapper equation holds for every raw body,
including its actual upper arguments, and both binder counts are preserved. -/
theorem EqInterleavedSupplyHistory.realize_returning
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΔ : OnCtx Δ (env.IsType univs))
    (H : EqInterleavedSupplyHistory D Δ Γ₀ Λ₀ σ₀ incoming Ψ₀ υ₀
      Γ Λ σ blocks Ψ υ plug chosen depth)
    (Q : EqSupplyInsertionSquare Γ₀ Γ₀' Δ σ₀ σ₀' ρ₀ τ₀ Λ₀ Λ₀' κ₀ υ₀ incoming outgoing)
    (EΨ : Ψ₀ = proofEraseCtx Λ₀') :
    ∃ (Γ' Λ' : List VExpr) (σ' : VExpr.Subst) (outblocks : EqInsertionPath) (plug' : ProofShape → ProofShape),
      EqSupplyInsertionSquare Γ Γ' Δ σ σ' (ρ₀.liftN chosen) (τ₀.liftN chosen)
        Λ Λ' (κ₀.liftN depth) υ blocks outblocks ∧ Ψ = proofEraseCtx Λ' ∧
      EqInterleavedSupplyHistory D Δ Γ₀' Λ₀' σ₀' outgoing (proofEraseCtx Λ₀') ProofShape.Subst.id
        Γ' Λ' σ' outblocks (proofEraseCtx Λ') ProofShape.Subst.id plug' chosen depth ∧
      ∀ e : ProofShape, (plug e).subst υ₀ = plug' (e.subst υ) := by
  induction H with
  | base => exact ⟨Γ₀', Λ₀', σ₀', outgoing, id, Q, EΨ, .base, fun _ => rfl⟩
  | @retained Γ Λ σ blocks Ψ υ plug chosen depth A u y n cd rawA' args H hA hy RD ih =>
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
    have HRnew := EqInterleavedSupplyHistory.retained (args := args.map (·.subst υ)) HR hBout hyout RDout
    refine ⟨_, _, _, _, (fun e => plug' (ProofShape.mkApps (.lam (rawA'.subst υ) e) (args.map (·.subst υ)))),
      Qnew, (by simp only [proofEraseCtx, ← EΨ, EB]), ?_, ?_⟩
    · simpa only [ProofShape.Subst.id_lift, ProofShape.subst_id, proofEraseCtx, EB] using HRnew
    · intro e
      simpa only [ProofShape.subst_mkApps, ProofShape.subst] using EW (ProofShape.mkApps (.lam rawA' e) args)
  | @unused Γ Λ σ blocks Ψ υ plug chosen depth A u n cd rawA' args H hA RD ih =>
    obtain ⟨Γ', Λ', σ', outblocks, plug', Q, EΨ, HR, EW⟩ := ih
    obtain ⟨B, HAB, _, Qnew, EB⟩ := Q.unused heq hs hΔ hA RD.forget
    have hBout : env.HasType univs Λ' (B.subst (κ₀.liftN depth)) (.sort u) := by
      simpa only [VExpr.subst] using HAB.hasType.2.subst henv.orderedStrong Q.actual Q.target_wf
    have RDout : ScopedComputeCount (PiInertStage D 0) 0 (proofEraseCtx Λ')
        (proofErase Λ' (B.subst (κ₀.liftN depth))) (rawA'.subst υ) := by
      rw [EB]; exact .beta .refl
    have HRnew := EqInterleavedSupplyHistory.unused (args := args.map (·.subst υ)) HR hBout RDout
    refine ⟨_, _, _, _, (fun e => plug' (ProofShape.mkApps (.lam (rawA'.subst υ) e) (args.map (·.subst υ)))),
      Qnew, (by simp only [proofEraseCtx, ← EΨ, EB]), ?_, ?_⟩
    · simpa only [ProofShape.Subst.id_lift, ProofShape.subst_id, proofEraseCtx, EB] using HRnew
    · intro e
      simpa only [ProofShape.subst_mkApps, ProofShape.subst] using EW (ProofShape.mkApps (.lam rawA' e) args)

/-- Append the actual waiting arguments to the outermost retained wrapper.
A positive retained depth guarantees such a wrapper. No annotation, source
scope, chosen image or binder count changes; the exact whole application is
recorded. The depth-zero case instead needs whole-spine supply restoration. -/
theorem EqInterleavedSupplyHistory.append_outer_arguments
    (H : EqInterleavedSupplyHistory D Δ Γ₀ Λ₀ σ₀ blocks₀ Ψ₀ υ₀
      Γ Λ σ blocks Ψ υ plug chosen depth)
    (hd : 0 < depth) (pending : List ProofShape) :
    ∃ plug', EqInterleavedSupplyHistory D Δ Γ₀ Λ₀ σ₀ blocks₀ Ψ₀ υ₀
      Γ Λ σ blocks Ψ υ plug' chosen depth ∧
      ∀ e, plug' e = ProofShape.mkApps (plug e) pending := by
  induction H with
  | base => omega
  | @retained Γ Λ σ blocks Ψ υ plug chosen depth A u y n cd rawA' args H hA hy RD ih =>
    by_cases hz : depth = 0
    · subst depth
      cases H with
      | base =>
        refine ⟨_, EqInterleavedSupplyHistory.retained (args := args ++ pending) .base hA hy RD, ?_⟩
        intro e; exact ProofShape.mkApps_append _ _ _
    · obtain ⟨plug', HR, EW⟩ := ih (by omega)
      exact ⟨_, EqInterleavedSupplyHistory.retained (args := args) HR hA hy RD,
        fun e => EW (ProofShape.mkApps (.lam rawA' e) args)⟩
  | @unused Γ Λ σ blocks Ψ υ plug chosen depth A u n cd rawA' args H hA RD ih =>
    by_cases hz : depth = 0
    · subst depth
      cases H with
      | base =>
        refine ⟨_, EqInterleavedSupplyHistory.unused (args := args ++ pending) .base hA RD, ?_⟩
        intro e; exact ProofShape.mkApps_append _ _ _
    · obtain ⟨plug', HR, EW⟩ := ih (by omega)
      exact ⟨_, EqInterleavedSupplyHistory.unused (args := args) HR hA RD,
        fun e => EW (ProofShape.mkApps (.lam rawA' e) args)⟩


/-- The computed argument equality and exact erasure already retained by an
actual eta continuation suffice to build its supply square. No replay of the
original argument path is required. Both actual maps use that same argument. -/
theorem EqSupplyInsertionSquare.of_supplied_argument
    (hΔ : OnCtx Δ (env.IsType univs))
    (W : EqSpecializationFrame Γ Γ' Δ σ σ' ρ τ)
    (J : EqFrameInsertionChain Γ Γ' ρ τ Λ Λ' κ υ blocks)
    (hA : env.HasType univs Γ A (.sort u))
    (HX : env.IsDefEq univs Γ x actualX A)
    (EX : blocks.erased (proofErase Γ actualX) = rawX) :
    EqSupplyInsertionSquare (A :: Γ) Γ Δ (σ.cons (x.subst σ)) σ
      (VExpr.Subst.one actualX) (ProofShape.Subst.one (proofErase Γ actualX))
      (blocks.actual A :: Λ) Λ (VExpr.Subst.one (blocks.actual actualX))
      (ProofShape.Subst.one rawX) blocks.underBinder blocks := by
  have WI := EqSpecializationFrame.inst W.agree.left hA HX.hasType.2
    (HX.subst henv.orderedStrong W.agree.left hΔ)
  have W₀ := EqSpecializationFrame.of_conversion hΔ W.agree.left (.refl W.actual.wf)
  have JS := J.source_identity.under_binder W₀ hA
  have hΛ := (J.actual W).2.1.wf
  have hAup : env.HasType univs Λ (blocks.actual A) (.sort u) := by
    simpa only [EqInsertionPath.actual_sort] using J.weak hA
  have hΛA : OnCtx (blocks.actual A :: Λ) (env.IsType univs) := ⟨hΛ, u, hAup⟩
  have EXup := (J.erase_actual W HX.hasType.2).trans EX
  refine ⟨WI, ?_, J.source_identity, hΛ,
    Ctx.InstN.zero.substEq hΛA (J.weak HX.hasType.2), ?_, ?_, ?_⟩
  · simpa only [VExpr.id_lift, ProofShape.Subst.id_lift, VExpr.subst_id] using JS
  · intro i T hl hn
    simpa only [EXup] using erasedSubstAgreement_one hΛA (J.weak HX.hasType.2) hl hn
  · intro e
    simpa only [VExpr.inst_eq] using (blocks.actual_inst e actualX).symm
  · intro e
    simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN, EX] using
      (blocks.erased_inst e (proofErase Γ actualX)).symm

/-- Consume the actual nested supplied binder, rebuild the surviving inner
history at its computed annotations, attach the actual waiting arguments to
its outermost lambda, and rejoin the older ancestry. The entire post-beta
wrapper is identified on every body. Positive inner depth is required here;
with no surviving wrapper, whole-spine argument restoration is needed instead. -/
theorem EqInterleavedSupplyHistory.consume_rejoin
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΔ : OnCtx Δ (env.IsType univs))
    (W : EqSpecializationFrame Γ₀ Γ₀' Δ σ₀ σ₀' ρ τ)
    (J : EqFrameInsertionChain Γ₀ Γ₀' ρ τ Λ₀ Λ₀' κ ω incoming)
    (O : EqInterleavedSupplyHistory D Δ baseΓ baseΛ baseσ baseBlocks baseTarget baseMap
      Γ₀ Λ₀ σ₀ incoming oldTarget oldMap oldPlug oldChosen oldDepth)
    (hA : env.HasType univs Γ₀ A (.sort u))
    (HX : env.IsDefEq univs Γ₀ x actualX A)
    (EX : incoming.erased (proofErase Γ₀ actualX) = rawX)
    (H : EqInterleavedSupplyHistory D Δ (A :: Γ₀) (incoming.actual A :: Λ₀)
      (σ₀.cons (x.subst σ₀)) incoming.underBinder historyTarget historyMap
      Γ Λ σ blocks Ψ υ plug chosen depth)
    (hd : 0 < depth) (waiting : List ProofShape) :
    ∃ (Γ' Λ' : List VExpr) (σ' : VExpr.Subst) (outblocks : EqInsertionPath)
      (returned : ProofShape → ProofShape) (joinedTarget : List ProofShape) (joinedMap : ProofShape.Subst),
      EqSupplyInsertionSquare Γ Γ' Δ σ σ' ((VExpr.Subst.one actualX).liftN chosen)
        ((ProofShape.Subst.one (proofErase Γ₀ actualX)).liftN chosen) Λ Λ'
        ((VExpr.Subst.one (incoming.actual actualX)).liftN depth)
        ((ProofShape.Subst.one rawX).liftN depth) blocks outblocks ∧
      EqInterleavedSupplyHistory D Δ Γ₀ Λ₀ σ₀ incoming (proofEraseCtx Λ₀) ProofShape.Subst.id
        Γ' Λ' σ' outblocks (proofEraseCtx Λ') ProofShape.Subst.id returned chosen depth ∧
      EqInterleavedSupplyHistory D Δ baseΓ baseΛ baseσ baseBlocks baseTarget baseMap
        Γ' Λ' σ' outblocks joinedTarget joinedMap (fun e => oldPlug (returned e))
        (oldChosen+chosen) (oldDepth+depth) ∧
      ∀ e : ProofShape, ProofShape.mkApps ((plug e).inst rawX) waiting =
        returned (e.subst ((ProofShape.Subst.one rawX).liftN depth)) := by
  obtain ⟨Ξ, χ, HR⟩ := H.rebase_endpoint (proofEraseCtx Λ₀) (ProofShape.Subst.one rawX)
  have Q := EqSupplyInsertionSquare.of_supplied_argument hΔ W J hA HX EX
  obtain ⟨Γ', Λ', σ', outblocks, plug', Qnew, EΞ, HRout, EW⟩ := HR.realize_returning heq hs hΔ Q rfl
  obtain ⟨returned, Hreturned, Ereturned⟩ := HRout.append_outer_arguments hd waiting
  obtain ⟨joinedTarget, joinedMap, Hjoined⟩ := O.append_rebased Hreturned
  refine ⟨Γ', Λ', σ', outblocks, returned, joinedTarget, joinedMap,
    (by simpa only [HR.shape.2] using Qnew), Hreturned, Hjoined, ?_⟩
  intro e
  simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN, HR.shape.2] using
    (congrArg (fun f => ProofShape.mkApps f waiting) (EW e)).trans (Ereturned (e.subst χ)).symm


/-- Resume an actual nested supplied application while preserving the older
ancestry in the resulting minimum. The selected body path derives the whole
suffix minimum; the rebuilt outgoing wrappers derive its inner minimum. The
same realized context carries the chosen prefix, actual type, exact component
vector and joined history. This handles a positive surviving inner prefix;
global descent/return closure and the depth-zero restoration case remain open. -/
theorem EqPrefixSpecializationAt.returning_supply_selected_return
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hbody : ErasedScopedPrimitiveCertificateDescent BodyStep BodyStep)
    (hΔ : OnCtx Δ (env.IsType univs))
    (W : EqSpecializationFrame Γ₀ Γ₀' Δ σ₀ σ₀' ρ τ)
    (J : EqFrameInsertionChain Γ₀ Γ₀' ρ τ Λ₀ Λ₀' κ ω incoming)
    (O : EqInterleavedSupplyHistory D Δ baseΓ baseΛ baseσ baseBlocks baseTarget baseMap
      Γ₀ Λ₀ σ₀ incoming oldTarget oldMap oldPlug oldChosen oldDepth)
    (hA : env.HasType univs Γ₀ A (.sort u))
    (HX : env.IsDefEq univs Γ₀ x actualX A)
    (EX : incoming.erased (proofErase Γ₀ actualX) = rawX)
    (HH : EqInterleavedSupplyHistory D Δ (A :: Γ₀) (incoming.actual A :: Λ₀)
      (σ₀.cons (x.subst σ₀)) incoming.underBinder historyTarget historyMap
      Γ Λ σ blocks Ψ υ plug chosen depth)
    (hd : 0 < depth)
    (H : EqPrefixSpecializationAt Γ Δ v w v' w' original pre σ pending)
    (hf : env.HasType univs Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre) F)
    (hn : ¬ IsProof Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre))
    (HC : env.IsDefEqU univs Γ (.const ``Eq.rec [v',w']) (.const ``Eq.rec [v'',w'']))
    (HA : List.Forall₂ (ScopedCompute BodyStep (proofEraseCtx Λ))
      ((pre.map (proofErase Γ)).map blocks.erased) rawBody)
    (hextra : rawExtra = [] ∨ pending = [])
    (RP : ScopedComputeCount (PiInertStage D n) cb (proofEraseCtx Λ) source
      (ProofShape.mkApps (.const ``Eq.rec [v'',w'']) (rawBody ++ rawExtra)))
    (HTnext : TypedSource (proofEraseCtx Λ₀)
      (ProofShape.mkApps ((plug (ProofShape.mkApps (.const ``Eq.rec [v'',w''])
        (rawBody ++ rawExtra))).inst rawX) waiting))
    (RT : ScopedComputeCount (PiInertStage D m) cs (proofEraseCtx Λ₀)
      (ProofShape.mkApps ((plug (ProofShape.mkApps (.const ``Eq.rec [v'',w''])
        (rawBody ++ rawExtra))).inst rawX) waiting) endpoint)
    (HK : PiInertRunFrames D Ω out (proofEraseCtx Λ₀) K endpoint ck frames)
    (hc : cb+(cs+ck) = cost)
    (HM : ∀ later j tail k, ScopedComputeCount (PiInertStage D later) j (proofEraseCtx Λ) source tail →
      PiInertApplicationContinuation D (proofEraseCtx Λ₀) (ProofShape.Subst.one rawX) waiting K
        (plug tail) k → cost ≤ j+k) :
    ∃ (Γ' Λ' : List VExpr) (σ' : VExpr.Subst) (outblocks : EqInsertionPath)
      (returned : ProofShape → ProofShape) (joinedTarget : List ProofShape) (joinedMap : ProofShape.Subst)
      (final : List VExpr) (smaller : Nat),
      EqPrefixSpecializationAt Γ' Δ v w v'' w'' original final σ' pending ∧
      env.HasType univs Γ' (VExpr.mkApps (.const ``Eq.rec [v'',w'']) final)
        (F.subst ((VExpr.Subst.one actualX).liftN chosen)) ∧
      ¬ IsProof Γ' (VExpr.mkApps (.const ``Eq.rec [v'',w'']) final) ∧
      EqFrameInsertionChain Γ' Γ' VExpr.Subst.id ProofShape.Subst.id
        Λ' Λ' VExpr.Subst.id ProofShape.Subst.id outblocks ∧
      EqInterleavedSupplyHistory D Δ Γ₀ Λ₀ σ₀ incoming (proofEraseCtx Λ₀) ProofShape.Subst.id
        Γ' Λ' σ' outblocks (proofEraseCtx Λ') ProofShape.Subst.id returned chosen depth ∧
      EqInterleavedSupplyHistory D Δ baseΓ baseΛ baseσ baseBlocks baseTarget baseMap
        Γ' Λ' σ' outblocks joinedTarget joinedMap (fun e => oldPlug (returned e))
        (oldChosen+chosen) (oldDepth+depth) ∧
      (∀ e : ProofShape, ProofShape.mkApps ((plug e).inst rawX) waiting =
        returned (e.subst ((ProofShape.Subst.one rawX).liftN depth))) ∧
      ((final.map (proofErase Γ')).map outblocks.erased) =
        rawBody.map (·.subst ((ProofShape.Subst.one rawX).liftN depth)) ∧
      PiInertFrameMinimum D Ω out (proofEraseCtx Λ')
        (ProofShape.mkApps (.const ``Eq.rec [v'',w''])
          (((final.map (proofErase Γ')).map outblocks.erased) ++
            rawExtra.map (·.subst ((ProofShape.Subst.one rawX).liftN depth)))) smaller (frames+depth) ∧
      EqChainContinuationMinimum D Δ v w original Ω out smaller ∧ smaller ≤ cs+ck ∧
      (smaller < cost ∨ smaller = cost ∧ frames+depth < frames+depth+1) := by
  obtain ⟨Γ', Λ', σ', outblocks, returned, joinedTarget, joinedMap, Q, HR, Hjoined, EW⟩ :=
    EqInterleavedSupplyHistory.consume_rejoin heq hs hΔ W J O hA HX EX HH hd waiting
  have HMnext : PiInertFrameMinimum D Ω out (proofEraseCtx Λ₀)
      (ProofShape.mkApps ((plug (ProofShape.mkApps (.const ``Eq.rec [v'',w''])
        (rawBody ++ rawExtra))).inst rawX) waiting) (cs+ck) frames := by
    refine ⟨K, m, cs, ck, endpoint, HTnext, RT, HK, rfl, ?_⟩
    intro later j tail k RJ HL
    have HB := HM n cb _ (j+k) RP ⟨later, j, tail, k, rfl, ?_, HL⟩
    · omega
    · simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using RJ
  rw [EW] at HMnext
  obtain ⟨smaller, hsmall, HB⟩ := HR.focus_nonempty heq hs hd
    (e := (ProofShape.mkApps (.const ``Eq.rec [v'',w'']) (rawBody ++ rawExtra)).subst
      ((ProofShape.Subst.one rawX).liftN depth)) (pending := [])
    (by simpa only [ProofShape.subst_id, ProofShape.mkApps] using HMnext)
  have HB : PiInertFrameMinimum D Ω out (proofEraseCtx Λ')
      (ProofShape.mkApps (.const ``Eq.rec [v'',w''])
        (rawBody.map (·.subst ((ProofShape.Subst.one rawX).liftN depth)) ++
          rawExtra.map (·.subst ((ProofShape.Subst.one rawX).liftN depth)))) smaller (frames+depth) := by
    simpa only [ProofShape.subst_id, ProofShape.subst_mkApps, ProofShape.subst, List.map_append] using HB
  have hextra' : rawExtra.map (·.subst ((ProofShape.Subst.one rawX).liftN depth)) = [] ∨ pending = [] := by
    rcases hextra with rfl | hp
    · exact .inl rfl
    · exact .inr hp
  obtain ⟨final, HP, ht, hnout, Efinal, Hchain⟩ := Q.component_return hbody hΔ H hf hn HC HA hextra' HB.forget
  exact ⟨Γ', Λ', σ', outblocks, returned, joinedTarget, joinedMap, final, smaller,
    HP, ht, hnout, Q.target, HR, Hjoined, EW, Efinal,
    (by simpa only [Efinal] using HB), Hchain, hsmall, by omega⟩

end Lean4Lean.VEnv.Strengthening
