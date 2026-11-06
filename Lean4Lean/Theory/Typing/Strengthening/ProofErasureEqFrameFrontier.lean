import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqFrameProgress

/-! # Exhaust direct completed frames before selecting a boundary

Primitive-count descent handles non-level roots. Between them, following the
actual application tail removes a frame, even when the count is unchanged.
The remaining boundary retains its exact run and identifies a retained binder,
non-proof consumption, or a nonempty supply at an underfilled Eq prefix.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params]

/-- Add the selected finite run's frame count to any existing typed minimum.
This does not minimize over frame counts or restrict the competitor predicate. -/
theorem PiInertTypedContinuationMinimum.with_frames
    (H : PiInertTypedContinuationMinimum D Ω out Δ source cost) :
    ∃ frames, PiInertFrameMinimum D Ω out Δ source cost frames := by
  obtain ⟨K, n, cb, ck, endpoint, HT, R, HK, hc, HM⟩ := H
  obtain ⟨frames, HF⟩ := HK.frame_count
  exact ⟨frames, K, n, cb, ck, endpoint, HT, R, HF, hc, HM⟩

/-- Following an actual direct application keeps its entire selected suffix
and tail frame count. Every competitor can be prefixed by the original path
at the old application predicate. No source-completion hypothesis is needed. -/
theorem pi_inert_application_tail_minimum
    (RP : ScopedComputeCount (PiInertStage D n) cb Δ source e)
    (HTnext : TypedSource Θ (ProofShape.mkApps (e.subst τ) pending))
    (RT : ScopedComputeCount (PiInertStage D m) cs Θ (ProofShape.mkApps (e.subst τ) pending) endpoint)
    (HK : PiInertRunFrames D Ω out Θ K endpoint ck frames)
    (hc : cb+(cs+ck) = cost)
    (HM : ∀ later j tail k, ScopedComputeCount (PiInertStage D later) j Δ source tail →
      PiInertApplicationContinuation D Θ τ pending K tail k → cost ≤ j+k) :
    PiInertFrameMinimum D Ω out Θ (ProofShape.mkApps (e.subst τ) pending) (cs+ck) frames := by
  refine ⟨K, m, cs, ck, endpoint, HTnext, RT, HK, rfl, ?_⟩
  intro later j tail k RJ HL
  have HB := HM n cb e (j+k) RP ⟨later, j, tail, k, rfl, RJ, HL⟩
  omega

/-- Exact selected frames at which direct preservation does not yet close the
argument. Retained binders require wrapper execution; non-proof consumption
requires image agreement; new arguments at an underfilled prefix require
supply ancestry. These are recorded cases, not claims of impossibility. -/
inductive PiInertEqFrameBoundary (D : Definitions) (slots : Nat)
    (Ω : List ProofShape) (out : ProofShape) :
    List ProofShape → (ProofShape → Nat → Prop) → ProofShape → Nat → Nat → Prop where
  | retained : TypedSource (A :: Δ) body → DomainSort Δ A u →
      ScopedComputeCount (PiInertStage D n) cd Δ A A' →
      ContextSubstitution (A :: Δ) (A' :: Δ) ProofShape.Subst.id →
      PiInertRunFrames D Ω out Δ K (ProofShape.mkApps (.lam A' body) args) ck frames →
      PiInertEqFrameBoundary D slots Ω out (A :: Δ)
        (fun body k => K (ProofShape.mkApps (.lam A' body) args) k) body ck (frames+1)
  | nonproof : TypedSource (A :: Δ) e →
      ContextSubstitution (A :: Δ) Δ (ProofShape.Subst.one x) → ¬ DomainSort Δ A .zero →
      TypedSource Δ (ProofShape.mkApps (e.subst (ProofShape.Subst.one x)) pending) →
      ScopedComputeCount (PiInertStage D n) cs Δ
        (ProofShape.mkApps (e.subst (ProofShape.Subst.one x)) pending) endpoint →
      PiInertRunFrames D Ω out Δ K endpoint ck frames →
      PiInertEqFrameBoundary D slots Ω out (A :: Δ)
        (PiInertApplicationContinuation D Δ (ProofShape.Subst.one x) pending K) e (cs+ck) (frames+1)
  | underfilled : TypedSource Δ (ProofShape.mkApps (.const ``Eq.rec ls) args) →
      PiInertEndpointMap Δ Θ τ → args.length < slots → pending ≠ [] →
      TypedSource Θ (ProofShape.mkApps ((ProofShape.mkApps (.const ``Eq.rec ls) args).subst τ) pending) →
      ScopedComputeCount (PiInertStage D n) cs Θ
        (ProofShape.mkApps ((ProofShape.mkApps (.const ``Eq.rec ls) args).subst τ) pending) endpoint →
      PiInertRunFrames D Ω out Θ K endpoint ck frames →
      PiInertEqFrameBoundary D slots Ω out Δ
        (PiInertApplicationContinuation D Θ τ pending K)
        (ProofShape.mkApps (.const ``Eq.rec ls) args) (cs+ck) (frames+1)

/-- Each boundary retains an actual typed run, with its original frame count. -/
theorem PiInertEqFrameBoundary.run
    (H : PiInertEqFrameBoundary D slots Ω out Δ K e ck frames) :
    PiInertRunFrames D Ω out Δ K e ck frames := by
  cases H with
  | retained HT SD RD WI HK => exact .retained HT SD RD WI HK
  | nonproof HT WI _ HTnext RT HK => exact .application HT (.inst WI) HTnext RT HK
  | underfilled HT W _ _ HTnext RT HK => exact .application HT W HTnext RT HK

/-- An Eq endpoint cannot be terminal at an exposed carrier. Its exact first
frame either gives a proof-preserving direct application with available supply,
or is one of the three recorded boundary cases. Empty pending vectors require
no new argument agreement, including at underfilled prefixes. -/
theorem PiInertRunFrames.eq_application_or_boundary
    (heq : env.HasCanonicalEq)
    (H : PiInertRunFrames D Ω out Δ K (ProofShape.mkApps (.const ``Eq.rec ls) args) ck frames)
    (HE : CarrierExposure out) :
    (∃ Θ τ pending n cs endpoint ck' K' remaining,
      ProofEndpointContext D Δ Θ τ ∧ (slots ≤ args.length ∨ pending = []) ∧
      TypedSource Θ (ProofShape.mkApps ((ProofShape.mkApps (.const ``Eq.rec ls) args).subst τ) pending) ∧
      ScopedComputeCount (PiInertStage D n) cs Θ
        (ProofShape.mkApps ((ProofShape.mkApps (.const ``Eq.rec ls) args).subst τ) pending) endpoint ∧
      PiInertRunFrames D Ω out Θ K' endpoint ck' remaining ∧
      ck = cs+ck' ∧ frames = remaining+1 ∧ K = PiInertApplicationContinuation D Θ τ pending K') ∨
    PiInertEqFrameBoundary D slots Ω out Δ K (ProofShape.mkApps (.const ``Eq.rec ls) args) ck frames := by
  classical
  cases H with
  | terminal => exact ((((RetainedConstHead.const (ls := ls)).mkApps args).eq_not_exposed heq) HE).elim
  | retained HT SD RD WI HK => exact .inr (.retained HT SD RD WI HK)
  | @application _ _ Θ _ pending n cs endpoint K' ck' remaining HT W HTnext RT HK =>
    by_cases hsupply : slots ≤ args.length ∨ pending = []
    · cases W with
      | identity WI =>
        exact .inl ⟨_, _, _, _, _, _, _, _, _, .identity, hsupply, HTnext, RT, HK, rfl, rfl, rfl⟩
      | @inst A _ x WI =>
        by_cases SD : DomainSort Θ A .zero
        · exact .inl ⟨_, _, _, _, _, _, _, _, _, .inst SD WI, hsupply, HTnext, RT, HK, rfl, rfl, rfl⟩
        · exact .inr (.nonproof HT WI SD HTnext RT HK)
    · exact .inr (.underfilled HT W (by omega) (fun h => hsupply (.inr h)) HTnext RT HK)

/-- A completed Eq endpoint whose selected run has reached an exact boundary.
Its own unrestricted minimum costs at most the original budget; the completed
source, run and remaining frame count are retained. Eliminating these boundary
cases is still needed for a sufficient strengthening obligation. -/
def EqEmbeddingFrameBoundaryMinimum (D : Definitions) (Γ : List VExpr) (v w : VLevel)
    (original : List VExpr) (Ω : List ProofShape) (out : ProofShape) (budget : Nat) : Prop :=
  ∃ Δ ls args K ck frames,
    EqTargetPrefixEmbedding Γ v w original Δ (ProofShape.mkApps (.const ``Eq.rec ls) args) ∧
    PiInertEqFrameBoundary D original.length Ω out Δ K (ProofShape.mkApps (.const ``Eq.rec ls) args) ck frames ∧
    ck ≤ budget ∧ ∀ later j endpoint k,
      ScopedComputeCount (PiInertStage D later) j Δ (ProofShape.mkApps (.const ``Eq.rec ls) args) endpoint →
      K endpoint k → ck ≤ j+k

/-- Increasing the outer bound keeps the same selected boundary and minimum. -/
theorem EqEmbeddingFrameBoundaryMinimum.mono
    (H : EqEmbeddingFrameBoundaryMinimum D Γ v w original Ω out budget)
    (h : budget ≤ larger) : EqEmbeddingFrameBoundaryMinimum D Γ v w original Ω out larger := by
  obtain ⟨Δ, ls, args, K, ck, frames, HP, HB, hc, HM⟩ := H
  exact ⟨Δ, ls, args, K, ck, frames, HP, HB, Nat.le_trans hc h, HM⟩

/-- The boundary carries a genuine typed minimum at its completed endpoint,
with zero preceding computation and the exact selected remaining run. -/
theorem EqEmbeddingFrameBoundaryMinimum.minimum
    (H : EqEmbeddingFrameBoundaryMinimum D Γ v w original Ω out budget) :
    ∃ Δ ls args ck frames, ck ≤ budget ∧
      EqTargetPrefixEmbedding Γ v w original Δ (ProofShape.mkApps (.const ``Eq.rec ls) args) ∧
      PiInertFrameMinimum D Ω out Δ (ProofShape.mkApps (.const ``Eq.rec ls) args) ck frames := by
  obtain ⟨Δ, ls, args, K, ck, frames, HP, HB, hc, HM⟩ := H
  exact ⟨Δ, ls, args, ck, frames, hc, HP, K, 0, 0, ck, _, HB.run.forget.typed,
    .beta .refl, HB.run, by omega, HM⟩

/-- Exhaust all completed non-level cuts and direct application frames.
The primary measure is the unrestricted primitive minimum. An equal-cost
direct move uses the actual tail with one fewer frame; positive-cost moves
may reset the frame count. No refocused run is used for the secondary descent.
The result retains an actual boundary instead of stopping at the first
component-only path. These boundaries still require ancestry or wrapper work. -/
theorem EqTargetPrefixEmbedding.frame_boundary
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hRec : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ (eqRecBeforeMajor v w α a M minor b) T)
    (HP : EqTargetPrefixEmbedding Γ v w [α,a,M,minor,b] Δ (ProofShape.mkApps (.const ``Eq.rec ls) args))
    (HM : PiInertFrameMinimum D Ω out Δ (ProofShape.mkApps (.const ``Eq.rec ls) args) cost frames)
    (HE : CarrierExposure out) (HO : ControlTyping Ω out (.sort outU)) :
    env.IsDefEq univs Γ a b α ∨ EqEmbeddingFrameBoundaryMinimum D Γ v w [α,a,M,minor,b] Ω out cost := by
  induction cost using Nat.strongRecOn generalizing Δ ls args frames with
  | ind cost ihCost =>
    induction frames using Nat.strongRecOn generalizing Δ ls args with
    | ind frames ihFrames =>
      obtain ⟨K, n, cb, ck, endpoint, HT, R, HK, hc, hmin⟩ := HM
      rcases HP.counted_spine_or_cut heq hs hΓ HT R with
        ⟨ls', args', rfl, _, _, HPend⟩ | Hcut
      · have HTend := HK.forget.typed
        have HMend : ∀ later j endpoint k,
            ScopedComputeCount (PiInertStage D later) j Δ (ProofShape.mkApps (.const ``Eq.rec ls') args') endpoint →
            K endpoint k → ck ≤ j+k := by
          intro later j tail k RJ HL
          have RR := (R.mono (pi_inert_stage_mono (Nat.le_max_left n later))).trans
            (RJ.mono (pi_inert_stage_mono (Nat.le_max_right n later)))
          have HB := hmin (max n later) _ tail k RR HL
          omega
        rcases HK.eq_application_or_boundary (slots := [α,a,M,minor,b].length) heq HE with
          ⟨Θ, τ, pending, m, cs, tail, ck', K', remaining, HC, Hsupply,
            HTnext, RT, HR, rfl, rfl, rfl⟩ | HB
        · have HPscope := HPend.proof_endpoint heq hs hΓ HTend HC
          simp only [ProofShape.subst_mkApps, ProofShape.subst] at HPscope
          have HPnext : EqTargetPrefixEmbedding Γ v w [α,a,M,minor,b] Θ
              (ProofShape.mkApps (.const ``Eq.rec ls') (args'.map (·.subst τ) ++ pending)) := by
            rcases Hsupply with hlen | rfl
            · exact HPscope.append_saturated (by simpa only [List.length_map] using hlen) pending
            · simpa only [List.append_nil] using HPscope
          have HMnext := pi_inert_application_tail_minimum R HTnext RT HR hc hmin
          simp only [ProofShape.subst_mkApps, ProofShape.subst, ← ProofShape.mkApps_append] at HMnext
          by_cases hsmall : cs+ck' < cost
          · rcases ihCost (cs+ck') hsmall HPnext HMnext with Hlower | Hboundary
            · exact .inl Hlower
            · exact .inr (Hboundary.mono (Nat.le_of_lt hsmall))
          · have hequal : cs+ck' = cost := by omega
            rw [hequal] at HMnext
            exact ihFrames remaining (by omega) HPnext HMnext
        · exact .inr ⟨Δ, ls', args', K, ck, frames, HPend, HB, by omega, HMend⟩
      · rcases Hcut.eq_or_smaller heq hs hreg hoff hRec hΓ ht HT HK.forget HE HO
          (cost := cost) (by omega) hmin with Hlower | ⟨Ξ, ls', args', smaller, hsmall, HM', HP'⟩
        · exact .inl Hlower
        · obtain ⟨remaining, HF⟩ := HM'.with_frames
          rcases ihCost smaller hsmall HP' HF with Hlower | Hboundary
          · exact .inl Hlower
          · exact .inr (Hboundary.mono (Nat.le_of_lt hsmall))

/-- The direct-frame boundary is reached from any ordinary completed typed
minimum. Its selected run supplies the secondary count, so callers need no
extra frame-minimality or termination premise. A sufficient smaller obligation
would still need to resolve the recorded boundary cases. -/
theorem EqTargetPrefixCompletion.frame_boundary
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hRec : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ (eqRecBeforeMajor v w α a M minor b) T)
    (HP : EqTargetPrefixCompletion Γ v w [α,a,M,minor,b] Δ (ProofShape.mkApps (.const ``Eq.rec ls) args))
    (HM : PiInertTypedContinuationMinimum D Ω out Δ (ProofShape.mkApps (.const ``Eq.rec ls) args) cost)
    (HE : CarrierExposure out) (HO : ControlTyping Ω out (.sort outU)) :
    env.IsDefEq univs Γ a b α ∨ EqEmbeddingFrameBoundaryMinimum D Γ v w [α,a,M,minor,b] Ω out cost := by
  obtain ⟨frames, HF⟩ := HM.with_frames
  exact HP.embedding.frame_boundary heq hs hreg hoff hRec hΓ ht HF HE HO

/-- The original lifted Eq probe starts bounded completion directly. Its five
lower arguments use identity specialization and the actual unused insertion;
the erased proof major lies beyond the bounded prefix and needs no inhabitant. -/
theorem EqTargetPrefixCompletion.probe
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.LiftN count offset Γ Γ')
    (ht : env.HasType univs Γ (eqRecBeforeMajor v w α a M minor b) T)
    (hn : ¬ IsProof Γ (eqRecBeforeMajor v w α a M minor b))
    (Eargs : args = (([α,a,M,minor,b].map (proofErase Γ)).map (·.liftN count offset)) ++ [.proof]) :
    EqTargetPrefixCompletion Γ v w [α,a,M,minor,b] (proofEraseCtx Γ')
      (ProofShape.mkApps (.const ``Eq.rec [v,w]) args) := by
  have HP : EqHeadCompletion Γ v w [α,a,M,minor,b] (proofEraseCtx Γ')
      (ProofShape.mkApps (.const ``Eq.rec [v,w])
        (([α,a,M,minor,b].map (proofErase Γ)).map (·.liftN count offset))) := by
    refine ⟨Γ, Γ', count, offset, v, w, [α,a,M,minor,b], T,
      hΓ, hΓ', W, rfl, ht, hn, EqPrefixSpecialization.of_typed hΓ ht, ?_⟩
    rw [proofErase_const_spine hΓ ht hn, ProofShape.liftN_mkApps]
    rfl
  have H := (EqTargetPrefixCompletion.of_completion (.base HP)).append_saturated
    (by simp only [List.length_map, Nat.le_refl]) [.proof]
  simpa only [Eargs] using H

/-- A sort-typed lifted Eq probe reaching an exposed carrier either reads the
lower equation or reaches an exact completed frame boundary. The original
path is minimized over all finite stages; direct eligible frames are exhausted
by the two-measure induction. The boundary is derived from the original probe,
without assuming completion at a later selected root or invoking the older
nested-eta frontier. Resolving its three cases and full strengthening coverage
remain separate obligations. -/
theorem pi_inert_eq_exposure_eq_or_frame_boundary
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
    env.IsDefEq univs Γ a b α ∨
      ∃ stage cost,
        ScopedComputeCount (PiInertStage D stage) cost (proofEraseCtx Γ')
          (ProofShape.mkApps (.const ``Eq.rec [v,w]) args) out ∧
        (∀ later j, ScopedComputeCount (PiInertStage D later) j (proofEraseCtx Γ')
          (ProofShape.mkApps (.const ``Eq.rec [v,w]) args) out → cost ≤ j) ∧
        EqEmbeddingFrameBoundaryMinimum D Γ v w [α,a,M,minor,b] (proofEraseCtx Γ') out cost := by
  have HP := EqTargetPrefixCompletion.probe hΓ hΓ' W ht hn Eargs
  have HTsource : TypedSource (proofEraseCtx Γ') (ProofShape.mkApps (.const ``Eq.rec [v,w]) args) := by
    obtain ⟨Ξ, e, hΞ, EΞ, he, Ee⟩ := HT
    exact ⟨Ξ, e, _, hΞ, EΞ, he, Ee⟩
  have HO := HT.compute
    (ErasedScopedPrimitiveCertificateDescent.descent (pi_inert_stage_certificate_descent heq hs n)) R
  obtain ⟨initial, RC₀⟩ := R.count
  obtain ⟨stage, cost, RC, hmin⟩ := RC₀.minimal_across_stages
  have HM : PiInertTypedContinuationMinimum D (proofEraseCtx Γ') out (proofEraseCtx Γ')
      (ProofShape.mkApps (.const ``Eq.rec [v,w]) args) cost := by
    refine ⟨(fun e k => e = out ∧ k = 0), stage, cost, 0, out, HTsource, RC,
      .terminal (HTsource.pi_inert_compute heq hs RC.forget), by omega, ?_⟩
    rintro later j endpoint k RJ ⟨rfl, rfl⟩
    simpa only [Nat.add_zero] using hmin later j RJ
  rcases HP.frame_boundary heq hs hreg hoff hRec hΓ ht HM HE HO with Hlower | HB
  · exact .inl Hlower
  · exact .inr ⟨stage, cost, RC, hmin, HB⟩

end Lean4Lean.VEnv.Strengthening
