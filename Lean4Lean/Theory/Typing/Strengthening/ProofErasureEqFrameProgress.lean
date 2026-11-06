import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqEmbeddedMinimum

/-! # Preserve an actual application suffix instead of refocusing it

Once the target prefix is full, additional pending arguments need no target
images. Retain the whole actual next path and its shorter continuation. A
frame count then decreases when the preceding component count is zero.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params]

/-- Pending arguments beyond the original target length do not change its
completed prefix. They need no target images or standalone typing witnesses. -/
theorem EqTargetPrefixCompletion.append_saturated
    (H : EqTargetPrefixCompletion Δ v w original Ξ (ProofShape.mkApps (.const ``Eq.rec ls) args))
    (hlen : original.length ≤ args.length) (pending : List ProofShape) :
    EqTargetPrefixCompletion Δ v w original Ξ
      (ProofShape.mkApps (.const ``Eq.rec ls) (args ++ pending)) :=
  ⟨ls, args ++ pending, rfl, by simpa only [List.take_append_of_le_length hlen] using H.prefix⟩

/-- The constructed reverse embedding is unchanged when pending arguments
are appended beyond the target prefix. -/
theorem EqTargetPrefixEmbedding.append_saturated
    (H : EqTargetPrefixEmbedding Δ v w original Ξ (ProofShape.mkApps (.const ``Eq.rec ls) args))
    (hlen : original.length ≤ args.length) (pending : List ProofShape) :
    EqTargetPrefixEmbedding Δ v w original Ξ
      (ProofShape.mkApps (.const ``Eq.rec ls) (args ++ pending)) := by
  obtain ⟨Θ, κ, WK, HP⟩ := H
  simp only [ProofShape.subst_mkApps, ProofShape.subst] at HP
  refine ⟨Θ, κ, WK, ?_⟩
  simpa only [ProofShape.subst_mkApps, ProofShape.subst, List.map_append] using
    HP.append_saturated (by simpa only [List.length_map] using hlen) (pending.map (·.subst κ))

/-- The actual continuation run with its number of application and retained
frames. Computation and annotation certificates remain exactly those of the
selected run; this count imposes no restriction on competitor predicates. -/
inductive PiInertRunFrames (D : Definitions) (Ω : List ProofShape) (out : ProofShape) :
    List ProofShape → (ProofShape → Nat → Prop) → ProofShape → Nat → Nat → Prop where
  | terminal : TypedSource Ω out →
      PiInertRunFrames D Ω out Ω (fun e k => e = out ∧ k = 0) out 0 0
  | application : TypedSource Δ e → PiInertEndpointMap Δ Θ τ →
      TypedSource Θ (ProofShape.mkApps (e.subst τ) args) →
      ScopedComputeCount (PiInertStage D n) cs Θ (ProofShape.mkApps (e.subst τ) args) e' →
      PiInertRunFrames D Ω out Θ K e' ck frames →
      PiInertRunFrames D Ω out Δ (PiInertApplicationContinuation D Θ τ args K)
        e (cs+ck) (frames+1)
  | retained : TypedSource (A :: Δ) body → DomainSort Δ A u →
      ScopedComputeCount (PiInertStage D n) cd Δ A A' →
      ContextSubstitution (A :: Δ) (A' :: Δ) ProofShape.Subst.id →
      PiInertRunFrames D Ω out Δ K (ProofShape.mkApps (.lam A' body) args) ck frames →
      PiInertRunFrames D Ω out (A :: Δ)
        (fun body k => K (ProofShape.mkApps (.lam A' body) args) k) body ck (frames+1)

/-- Forgetting the frame count preserves the actual typed run and predicate. -/
theorem PiInertRunFrames.forget (H : PiInertRunFrames D Ω out Δ K e ck frames) :
    PiInertTypedContinuationRun D Ω out Δ K e ck := by
  induction H with
  | terminal HT => exact .terminal HT
  | application HT W HTnext R _ ih => exact .application HT W HTnext R ih
  | retained HT SD RD WI _ ih => exact .retained HT SD RD WI ih

/-- Every actual finite run has such a frame count. -/
theorem PiInertTypedContinuationRun.frame_count
    (H : PiInertTypedContinuationRun D Ω out Δ K e ck) :
    ∃ frames, PiInertRunFrames D Ω out Δ K e ck frames := by
  induction H with
  | terminal HT => exact ⟨0, .terminal HT⟩
  | application HT W HTnext R _ ih =>
    obtain ⟨frames, HF⟩ := ih
    exact ⟨frames+1, .application HT W HTnext R HF⟩
  | retained HT SD RD WI _ ih =>
    obtain ⟨frames, HF⟩ := ih
    exact ⟨frames+1, .retained HT SD RD WI HF⟩

/-- Traversing the actual retained prefix and first application removes at
least one selected frame. The exact suffix, interpretation and competitor
equivalence are retained. This decrease is before any hole refocusing; generic
refocusing can add frames and is not covered by this measure. -/
theorem PiInertRunFrames.next_application
    (H : PiInertRunFrames D Ω out Δ K e ck frames)
    (HE : CarrierExposure out) (hn : ¬ CarrierExposure e) :
    ∃ Θ Ξ τ args plug n cs e' ck' K' remaining,
      PiInertRetainedPrefix D Δ Θ plug ∧ PiInertEndpointMap Θ Ξ τ ∧
      TypedSource Θ (plug e) ∧ TypedSource Ξ (ProofShape.mkApps ((plug e).subst τ) args) ∧
      ScopedComputeCount (PiInertStage D n) cs Ξ (ProofShape.mkApps ((plug e).subst τ) args) e' ∧
      PiInertRunFrames D Ω out Ξ K' e' ck' remaining ∧ cs+ck' = ck ∧ remaining < frames ∧
      ∀ endpoint k, K endpoint k ↔ PiInertApplicationContinuation D Ξ τ args K' (plug endpoint) k := by
  induction H with
  | terminal => exact (hn HE).elim
  | application HT W HTnext R HK _ =>
    exact ⟨_, _, _, _, id, _, _, _, _, _, _, .refl, W, HT, HTnext, R, HK,
      rfl, by omega, fun _ _ => Iff.rfl⟩
  | retained HT SD RD WI HK ih =>
    obtain ⟨Θ, Ξ, τ, args, plug, n, cs, e', ck', K', remaining,
      HP, W, HTplug, HTnext, R, HR, hc, hsmall, EK⟩ :=
      ih (fun H => H.not_lambda_spine _ _ _ rfl)
    exact ⟨Θ, Ξ, τ, args, _, n, cs, e', ck', K', remaining,
      .retained SD RD WI HP, W, HTplug, HTnext, R, HR, hc, by omega,
      fun _ _ => EK _ _⟩

/-- The existing unrestricted primitive-count minimum, additionally recording
the actual chosen suffix's frame count. No secondary minimality is assumed. -/
def PiInertFrameMinimum (D : Definitions) (Ω : List ProofShape) (out : ProofShape)
    (Δ : List ProofShape) (source : ProofShape) (cost frames : Nat) : Prop :=
  ∃ K n cb ck endpoint, TypedSource Δ source ∧
    ScopedComputeCount (PiInertStage D n) cb Δ source endpoint ∧
    PiInertRunFrames D Ω out Δ K endpoint ck frames ∧ cb+ck = cost ∧
    ∀ later j endpoint' k, ScopedComputeCount (PiInertStage D later) j Δ source endpoint' →
      K endpoint' k → cost ≤ j+k

/-- The frame-refined minimum retains the original minimum verbatim. -/
theorem PiInertFrameMinimum.forget
    (H : PiInertFrameMinimum D Ω out Δ source cost frames) :
    PiInertTypedContinuationMinimum D Ω out Δ source cost := by
  obtain ⟨K, n, cb, ck, endpoint, HT, R, HK, hc, HM⟩ := H
  exact ⟨K, n, cb, ck, endpoint, HT, R, HK.forget, hc, HM⟩

/-- Refocusing the same whole path behind an empty identity application can
increase the chosen frame count while leaving source, context and primitive
cost fixed. Thus generic reification does not supply a decreasing frame
measure; the direct suffix construction below is essential. -/
theorem PiInertFrameMinimum.idle_refocus
    (H : PiInertFrameMinimum D Ω out Δ source cost frames) :
    PiInertFrameMinimum D Ω out Δ source cost (frames+1) := by
  obtain ⟨K, n, cb, ck, endpoint, HT, R, HK, hc, HM⟩ := H
  have W : PiInertEndpointMap Δ Δ ProofShape.Subst.id := .identity ContextRenaming.identity.interpretation
  have HF := PiInertRunFrames.application (args := []) HT W
    (by simpa only [ProofShape.subst_id, ProofShape.mkApps] using HT)
    (by simpa only [ProofShape.subst_id, ProofShape.mkApps] using R) HK
  refine ⟨PiInertApplicationContinuation D Δ ProofShape.Subst.id [] K,
    0, 0, cost, source, HT, .beta .refl, ?_, by omega, ?_⟩
  · simpa only [hc] using HF
  · intro later j tail k RJ HL
    have HH := pi_inert_identity_application_prefix_closed later j source tail k RJ HL
    obtain ⟨m, ct, last, cl, he, RT, HL'⟩ := HH
    have Hbound := HM m ct last cl
      (by simpa only [ProofShape.subst_id, ProofShape.mkApps] using RT) HL'
    omega

/-- Preserve the actual whole application suffix when its completed target
prefix is full. The next minimum uses the selected tail run, with one fewer
frame. Its primitive cost strictly decreases if the preceding path has
positive cost, and otherwise its frame count strictly decreases. Proof-valued
endpoint agreement comes from the constructed embedding. -/
theorem EqTargetPrefixEmbedding.direct_application_progress
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (HP : EqTargetPrefixEmbedding Γ v w original Δ (ProofShape.mkApps (.const ``Eq.rec ls) args))
    (hlen : original.length ≤ args.length)
    (HT : TypedSource Δ (ProofShape.mkApps (.const ``Eq.rec ls) args))
    (HC : ProofEndpointContext D Δ Θ τ)
    (W : PiInertEndpointMap Δ Θ τ)
    (HTsource : TypedSource Δ source)
    (RP : ScopedComputeCount (PiInertStage D n) cb Δ source (ProofShape.mkApps (.const ``Eq.rec ls) args))
    (HTnext : TypedSource Θ
      (ProofShape.mkApps ((ProofShape.mkApps (.const ``Eq.rec ls) args).subst τ) pending))
    (RT : ScopedComputeCount (PiInertStage D m) cs Θ
      (ProofShape.mkApps ((ProofShape.mkApps (.const ``Eq.rec ls) args).subst τ) pending) endpoint)
    (HK : PiInertRunFrames D Ω out Θ K endpoint ck frames)
    (hc : cb+(cs+ck) = cost)
    (HM : ∀ later j tail k, ScopedComputeCount (PiInertStage D later) j Δ source tail →
      PiInertApplicationContinuation D Θ τ pending K tail k → cost ≤ j+k) :
    PiInertFrameMinimum D Ω out Δ source cost (frames+1) ∧
      EqTargetPrefixEmbedding Γ v w original Θ
        (ProofShape.mkApps (.const ``Eq.rec ls) (args.map (·.subst τ) ++ pending)) ∧
      PiInertFrameMinimum D Ω out Θ
        (ProofShape.mkApps (.const ``Eq.rec ls) (args.map (·.subst τ) ++ pending)) (cs+ck) frames ∧
      (cs+ck < cost ∨ cs+ck = cost ∧ frames < frames+1) := by
  have HP' := HP.proof_endpoint heq hs hΓ HT HC
  simp only [ProofShape.subst_mkApps, ProofShape.subst] at HP'
  have HP'' := HP'.append_saturated (by simpa only [List.length_map] using hlen) pending
  refine ⟨⟨PiInertApplicationContinuation D Θ τ pending K, n, cb, cs+ck,
    ProofShape.mkApps (.const ``Eq.rec ls) args, HTsource, RP,
    .application HT W HTnext RT HK, hc, HM⟩, HP'', ?_, by omega⟩
  refine ⟨K, m, cs, ck, endpoint, ?_, ?_, HK, rfl, ?_⟩
  · simpa only [ProofShape.subst_mkApps, ProofShape.subst, ProofShape.mkApps_append] using HTnext
  · simpa only [ProofShape.subst_mkApps, ProofShape.subst, ProofShape.mkApps_append] using RT
  · intro later j tail k RJ HL
    have HB := HM n cb _ (j+k) RP ⟨later, j, tail, k, rfl,
      (by simpa only [ProofShape.subst_mkApps, ProofShape.subst, ProofShape.mkApps_append] using RJ), HL⟩
    omega

end Lean4Lean.VEnv.Strengthening
