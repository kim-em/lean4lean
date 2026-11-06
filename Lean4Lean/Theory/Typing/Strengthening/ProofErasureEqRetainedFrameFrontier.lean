import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqFrameFrontier
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqRetainedFrameProgress
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqRetainedRetraction

/-! # Exhaust retained prefixes before selecting a supply boundary

The next actual scope map is followed through all retained lambdas. Reading
those lambda paths rebuilds fewer frames than were removed. Remaining cases
are an actual non-proof scope map or a new supply at an underfilled direct
Eq application. At a direct map, the bounded prefix must actually use the
consumed binder; unused top binders and retained wrappers alone do not stop
the induction. At retained depth the consumed binder must occur in the
annotation shell around the bounded prefix. Wrapper argument vectors do not
need to be independent.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params]

/-- An actual endpoint map is proof-preserving or consumes its displayed
base domain without a Prop witness. The latter keeps the literal one map. -/
theorem PiInertEndpointMap.proof_or_nonproof
    (W : PiInertEndpointMap Δ Θ τ) :
    ProofEndpointContext D Δ Θ τ ∨
      ∃ A x, Δ = A :: Θ ∧ τ = ProofShape.Subst.one x ∧ ¬ DomainSort Θ A .zero := by
  classical
  cases W with
  | identity => exact .inl .identity
  | @inst A _ x WI =>
    by_cases SD : DomainSort Θ A .zero
    · exact .inl (.inst SD WI)
    · exact .inr ⟨A, x, rfl, rfl, SD⟩

/-- A completed endpoint whose next actual application still needs argument
agreement. Its counted retained prefix, exact scope map, suffix and tail remain
recorded, as does equivalence on every competing endpoint. The actual map
consumes a non-proof domain (used in the bounded Eq arguments when there are
no retained wrappers, and used in its annotation shell otherwise),
or the prefix is empty and its underfilled Eq spine receives nonempty new
supply. Retained wrappers are not a separate case. -/
def EqEmbeddingSupplyBoundaryMinimum (D : Definitions) (Γ : List VExpr) (v w : VLevel)
    (original : List VExpr) (Ω : List ProofShape) (out : ProofShape) (budget : Nat) : Prop :=
  ∃ Δ ls args K ck frames Θ Ξ τ pending plug depth n cs endpoint ck' K' remaining,
    EqTargetPrefixEmbedding Γ v w original Δ (ProofShape.mkApps (.const ``Eq.rec ls) args) ∧
    PiInertRunFrames D Ω out Δ K (ProofShape.mkApps (.const ``Eq.rec ls) args) ck frames ∧
    PiInertRetainedPrefixCount D Δ Θ plug depth ∧ PiInertEndpointMap Θ Ξ τ ∧
    TypedSource Θ (plug (ProofShape.mkApps (.const ``Eq.rec ls) args)) ∧
    TypedSource Ξ (ProofShape.mkApps ((plug (ProofShape.mkApps (.const ``Eq.rec ls) args)).subst τ) pending) ∧
    ScopedComputeCount (PiInertStage D n) cs Ξ
      (ProofShape.mkApps ((plug (ProofShape.mkApps (.const ``Eq.rec ls) args)).subst τ) pending) endpoint ∧
    PiInertRunFrames D Ω out Ξ K' endpoint ck' remaining ∧
    ck = cs+ck' ∧ frames = remaining+depth+1 ∧ ck ≤ budget ∧
    (∀ body k, K body k ↔ PiInertApplicationContinuation D Ξ τ pending K' (plug body) k) ∧
    (∀ later j endpoint k,
      ScopedComputeCount (PiInertStage D later) j Δ (ProofShape.mkApps (.const ``Eq.rec ls) args) endpoint →
      K endpoint k → ck ≤ j+k) ∧
    ((∃ A x, Θ = A :: Ξ ∧ τ = ProofShape.Subst.one x ∧ ¬ DomainSort Ξ A .zero ∧
        (depth = 0 → ¬ UnusedEqPrefix original.length args) ∧
        (0 < depth → ∃ shell, PiInertRetainedShellCount D Δ Θ plug shell depth ∧
          ¬ UnusedRetainedEqPrefix shell original.length ls args)) ∨
      (depth = 0 ∧ args.length < original.length ∧ pending ≠ []))

/-- Increasing the budget keeps the identical endpoint and supply boundary. -/
theorem EqEmbeddingSupplyBoundaryMinimum.mono
    (H : EqEmbeddingSupplyBoundaryMinimum D Γ v w original Ω out budget)
    (h : budget ≤ larger) : EqEmbeddingSupplyBoundaryMinimum D Γ v w original Ω out larger := by
  obtain ⟨Δ, ls, args, K, ck, frames, Θ, Ξ, τ, pending, plug, depth, n, cs, endpoint, ck', K', remaining,
    HP, HK, HR, W, HTplug, HTnext, RT, HK', hc, hf, hb, EK, HM, HB⟩ := H
  exact ⟨Δ, ls, args, K, ck, frames, Θ, Ξ, τ, pending, plug, depth, n, cs, endpoint, ck', K', remaining,
    HP, HK, HR, W, HTplug, HTnext, RT, HK', hc, hf, Nat.le_trans hb h, EK, HM, HB⟩

/-- Exhaust non-level cuts and every completion-preserving next application,
including arbitrary retained prefixes. Refocusing reads actual lambda paths
and rebuilds exactly the prefix length in frames, leaving the removed
application as a strict secondary decrease. Only the actual supply-agreement
cases remain; no global sufficiency for strengthening is claimed. -/
theorem EqTargetPrefixEmbedding.supply_boundary
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hRec : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ (eqRecBeforeMajor v w α a M minor b) T)
    (HP : EqTargetPrefixEmbedding Γ v w [α,a,M,minor,b] Δ (ProofShape.mkApps (.const ``Eq.rec ls) args))
    (HM : PiInertFrameMinimum D Ω out Δ (ProofShape.mkApps (.const ``Eq.rec ls) args) cost frames)
    (HE : CarrierExposure out) (HO : ControlTyping Ω out (.sort outU)) :
    env.IsDefEq univs Γ a b α ∨ EqEmbeddingSupplyBoundaryMinimum D Γ v w [α,a,M,minor,b] Ω out cost := by
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
        obtain ⟨Θ, Ξ, τ, pending, plug, depth, m, cs, tail, ck', K', remaining,
          HR, W, HTplug, HTnext, RT, HK', hcount, hframes, EK⟩ :=
          HK.next_counted_application HE (((RetainedConstHead.const (ls := ls')).mkApps args').eq_not_exposed heq)
        have HMwhole : PiInertFrameMinimum D Ω out Ξ
            (ProofShape.mkApps ((plug (ProofShape.mkApps (.const ``Eq.rec ls') args')).subst τ) pending) ck remaining := by
          refine ⟨K', m, cs, ck', tail, HTnext, RT, HK', hcount.symm, ?_⟩
          intro later j last k RJ HL
          have HB := HMend 0 0 _ (j+k) (ScopedComputeCount.beta BetaRed.refl)
            ((EK _ (j+k)).2 ⟨later, j, last, k, rfl, RJ, HL⟩)
          omega
        by_cases hd : depth = 0
        · subst depth
          cases HR with
          | refl =>
            by_cases hsup : [α,a,M,minor,b].length ≤ args'.length ∨ pending = []
            · rcases HPend.direct_endpoint_or_used heq hs hΓ HTend W with HPscope | HN
              · have HPnext : EqTargetPrefixEmbedding Γ v w [α,a,M,minor,b] Ξ
                    (ProofShape.mkApps (.const ``Eq.rec ls') (args'.map (·.subst τ) ++ pending)) := by
                  rcases hsup with hlen | rfl
                  · exact HPscope.append_saturated (by simpa only [List.length_map] using hlen) pending
                  · simpa only [List.append_nil] using HPscope
                simp only [id_eq, ProofShape.subst_mkApps, ProofShape.subst, ← ProofShape.mkApps_append] at HMwhole
                by_cases hsmall : ck < cost
                · rcases ihCost ck hsmall HPnext HMwhole with Hlower | HB
                  · exact .inl Hlower
                  · exact .inr (HB.mono (Nat.le_of_lt hsmall))
                · have hequal : ck = cost := by omega
                  rw [hequal] at HMwhole
                  exact ihFrames remaining (by omega) HPnext HMwhole
              · obtain ⟨A, x, EΔ, Eτ, Hnonprop, Hused⟩ := HN
                exact .inr ⟨Δ, ls', args', K, ck, frames, Δ, Ξ, τ, pending, id, 0, m, cs, tail, ck', K', remaining,
                  HPend, HK, .refl, W, HTplug, HTnext, RT, HK', hcount, hframes, by omega, EK, HMend,
                  .inl ⟨A, x, EΔ, Eτ, Hnonprop, (fun _ => Hused), by omega⟩⟩
            · exact .inr ⟨Δ, ls', args', K, ck, frames, Δ, Ξ, τ, pending, id, 0, m, cs, tail, ck', K', remaining,
                HPend, HK, .refl, W, HTplug, HTnext, RT, HK', hcount, hframes, by omega, EK, HMend,
                .inr ⟨rfl, by omega, fun h => hsup (.inr h)⟩⟩
        · rcases W.proof_or_nonproof (D := D) with HC | HN
          · obtain ⟨Λ, σ, smaller, HCinner, hsmall, HMinner⟩ := HR.focus_nonempty heq hs (by omega) HC HMwhole
            have HPinner := HPend.proof_endpoint heq hs hΓ HTend HCinner
            simp only [ProofShape.subst_mkApps, ProofShape.subst] at HPinner HMinner
            by_cases hstrict : smaller < cost
            · rcases ihCost smaller hstrict HPinner HMinner with Hlower | HB
              · exact .inl Hlower
              · exact .inr (HB.mono (Nat.le_of_lt hstrict))
            · have hequal : smaller = cost := by omega
              rw [hequal] at HMinner
              exact ihFrames (remaining+depth) (by omega) HPinner HMinner
          · obtain ⟨A, x, EΘ, Eτ, Hnonprop⟩ := HN
            obtain ⟨shell, HS⟩ := HR.with_shell
            by_cases HU : UnusedRetainedEqPrefix shell [α,a,M,minor,b].length ls' args'
            · subst Θ τ
              obtain ⟨u, SD⟩ := TypedSource.top_domain HTplug
              obtain ⟨Λ, smaller, hsmall, HMinner, HPinner⟩ :=
                HPend.consume_unused_retained heq hs hΓ HS (by omega) SD HU HMwhole
              by_cases hstrict : smaller < cost
              · rcases ihCost smaller hstrict HPinner HMinner with Hlower | HB
                · exact .inl Hlower
                · exact .inr (HB.mono (Nat.le_of_lt hstrict))
              · have hequal : smaller = cost := by omega
                rw [hequal] at HMinner
                exact ihFrames (remaining+depth) (by omega) HPinner HMinner
            · exact .inr ⟨Δ, ls', args', K, ck, frames, Θ, Ξ, τ, pending, plug, depth, m, cs, tail, ck', K', remaining,
                HPend, HK, HR, W, HTplug, HTnext, RT, HK', hcount, hframes, by omega, EK, HMend,
                .inl ⟨A, x, EΘ, Eτ, Hnonprop, (fun h => (hd h).elim), fun _ => ⟨shell, HS, HU⟩⟩⟩
      · rcases Hcut.eq_or_smaller heq hs hreg hoff hRec hΓ ht HT HK.forget HE HO
          (cost := cost) (by omega) hmin with Hlower | ⟨Ξ, ls', args', smaller, hsmall, HM', HP'⟩
        · exact .inl Hlower
        · obtain ⟨remaining, HF⟩ := HM'.with_frames
          rcases ihCost smaller hsmall HP' HF with Hlower | HB
          · exact .inl Hlower
          · exact .inr (HB.mono (Nat.le_of_lt hsmall))

/-- Ordinary completion and an existing typed minimum need no extra frame
count premise to reach the supply boundary. -/
theorem EqTargetPrefixCompletion.supply_boundary
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hRec : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ (eqRecBeforeMajor v w α a M minor b) T)
    (HP : EqTargetPrefixCompletion Γ v w [α,a,M,minor,b] Δ (ProofShape.mkApps (.const ``Eq.rec ls) args))
    (HM : PiInertTypedContinuationMinimum D Ω out Δ (ProofShape.mkApps (.const ``Eq.rec ls) args) cost)
    (HE : CarrierExposure out) (HO : ControlTyping Ω out (.sort outU)) :
    env.IsDefEq univs Γ a b α ∨ EqEmbeddingSupplyBoundaryMinimum D Γ v w [α,a,M,minor,b] Ω out cost := by
  obtain ⟨frames, HF⟩ := HM.with_frames
  exact HP.embedding.supply_boundary heq hs hreg hoff hRec hΓ ht HF HE HO

/-- The original lifted Eq probe reaches an actual supply boundary after
exhausting completion-preserving applications through every finite retained
prefix. The original all-stage minimum is retained. No retained-wrapper case
is left on its own: the residue identifies a non-proof endpoint map (with
actual bounded-prefix use in the direct case and annotation-shell use
otherwise) or a nonempty new supply at an
underfilled direct prefix. Their argument agreement
and full strengthening coverage remain unproved. -/
theorem pi_inert_eq_exposure_eq_or_supply_boundary
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
        EqEmbeddingSupplyBoundaryMinimum D Γ v w [α,a,M,minor,b] (proofEraseCtx Γ') out cost := by
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
  rcases HP.supply_boundary heq hs hreg hoff hRec hΓ ht HM HE HO with Hlower | HB
  · exact .inl Hlower
  · exact .inr ⟨stage, cost, RC, hmin, HB⟩

end Lean4Lean.VEnv.Strengthening
