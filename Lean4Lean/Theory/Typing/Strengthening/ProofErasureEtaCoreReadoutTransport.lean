import Lean4Lean.Theory.Typing.Strengthening.ProofErasureAmbientSortedReadout
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureIdentityRecoveryCover

/-! # Retaining eta readout evidence through actual function computation

Readout is attached to a particular assigned function, not inferred from a
native certificate at its outer syntax. Core computation preserves this evidence
in both directions. Backward transport joins independently exposed lambdas and
retains their domain paths, without comparison transitivity or stage increases.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params] {D : Definitions}

/-- Retained comparison evidence for a particular assigned function and domain.
The two fields are exactly the local obligations consumed by full-core eta
consumer readout. Their synthesis from an arbitrary typing remains missing. -/
structure EtaCoreReadout (D : Definitions)
    (Step : List ProofShape → ProofShape → ProofShape → Prop)
    (Δ : List ProofShape) (u : VLevel) (A f : ProofShape) : Prop where
  domains : ∀ {C E}, EtaCoreDomains D A f C E → ComputedJointCompare Step Δ true C E
  origins : ∀ {C g mode}, EtaCoreOrigin D A f C g →
    ComputedJointCompare Step Δ mode (sortedEta u C g) g

/-- Later function computation restricts the histories requested by a retained
certificate. The original assigned domain, context and comparison core stay fixed. -/
theorem EtaCoreReadout.after (H : EtaCoreReadout D Step Δ u A f)
    (R : Compute (ErasedLevelCore D) f g) : EtaCoreReadout D Step Δ u A g := by
  constructor
  · intro C E HG
    rcases HG with ⟨RA, b, RF⟩ | ⟨RA, b, RF⟩
    · exact H.domains (.inl ⟨RA, b, R.trans RF⟩)
    · exact H.domains (.inr ⟨RA, b, R.trans RF⟩)
  · intro C g mode HG
    exact H.origins ⟨HG.1, R.trans HG.2⟩

/-- Evidence for a chosen core reduct transports back to its actual typed
source. Source confluence joins every other function history to that reduct;
lambda inversion retains the precise annotation computation needed by readout.
No native recovery, semantic comparison completeness or comparison transitivity
is used. The target comparison core need only contain ordinary level-core roots. -/
theorem EtaCoreReadout.before
    (hcore : ∀ {Δ a b}, ErasedLevelCore D a b → Step Δ a b)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hΓ : OnCtx Γ (env.IsType univs)) (hf : env.HasType univs Γ f T)
    (R : Compute (ErasedLevelCore D) (proofErase Γ f) g)
    (H : EtaCoreReadout D Step (proofEraseCtx Γ) u A g) :
    EtaCoreReadout D Step (proofEraseCtx Γ) u A (proofErase Γ f) := by
  have expose {X C body} (RA : Compute (ErasedLevelCore D) A X)
      (RF : Compute (ErasedLevelCore D) (proofErase Γ f) (.lam C body)) :
      ComputedJointCompare Step (proofEraseCtx Γ) true X C := by
    obtain ⟨shared, RF', RG⟩ := hc hΓ hf RF R
    obtain ⟨C', body', rfl, RC, _⟩ := RF'.level_core_lam_inv
    exact .compute .refl (RC.scoped (fun H => .base (hcore H)))
      (H.domains (.inl ⟨RA, body', RG⟩))
  constructor
  · intro C E HG
    rcases HG with ⟨RA, body, RF⟩ | ⟨RA, body, RF⟩
    · exact expose RA RF
    · exact (expose RA RF).symm
  · intro C q mode HG
    obtain ⟨shared, RQ, RG⟩ := hc hΓ hf HG.2 R
    have RL : Compute (ErasedLevelCore D) (sortedEta u C q) (sortedEta u C shared) :=
      .lam .refl (.app (RQ.liftN (fun H => erased_level_core_liftN H)) .refl)
    exact .compute (RL.scoped (fun H => .base (hcore H)))
      (RQ.scoped (fun H => .base (hcore H))) (H.origins ⟨HG.1, RG⟩)

/-- A particular eta-readout certificate is invariant along actual typed core
computation. This is local evidence transport, not a global coverage assertion. -/
theorem eta_core_readout_compute_iff
    (hcore : ∀ {Δ a b}, ErasedLevelCore D a b → Step Δ a b)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hΓ : OnCtx Γ (env.IsType univs)) (hf : env.HasType univs Γ f T)
    (R : Compute (ErasedLevelCore D) (proofErase Γ f) g) :
    EtaCoreReadout D Step (proofEraseCtx Γ) u A (proofErase Γ f) ↔
      EtaCoreReadout D Step (proofEraseCtx Γ) u A g :=
  ⟨fun H => H.after R, fun H => H.before (fun H => hcore H) hc hΓ hf R⟩

/-- The argument's conversion evidence, not just the wrapper's exact native
Pi, is sufficient and necessary to retain eta readout across identity beta.
Both directions preserve the comparison relation and hence any fixed stage. -/
theorem eta_core_readout_identity_iff
    (hcore : ∀ {Δ a b}, ErasedLevelCore D a b → Step Δ a b)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hΓ : OnCtx Γ (env.IsType univs)) (hf : env.HasType univs Γ f T) :
    EtaCoreReadout D Step (proofEraseCtx Γ) u A
        (proofErase Γ (.app (.lam T (.bvar 0)) f)) ↔
      EtaCoreReadout D Step (proofEraseCtx Γ) u A (proofErase Γ f) := by
  obtain ⟨hy, _, RB, _⟩ := proofErase_identity_recovery_cover (Step := Step) hΓ hf
  exact eta_core_readout_compute_iff (fun H => hcore H) hc hΓ hy (.beta RB)

/-- Retained function evidence supplies both obligations of arbitrary typed
consumer readout after independent full-core paths. The source typing need not
be used to reconstruct any inferred domain certificate. -/
theorem EtaCoreReadout.consumer
    (hs : D.Sound env univs) (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hcore : ∀ {Δ a b}, ErasedLevelCore D a b → Step Δ a b)
    (hrename : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextRenaming Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (hf : env.HasType univs Γ f (.forallE A B))
    (ht : env.HasType univs (.forallE A B :: Γ) t T)
    (H : EtaCoreReadout D Step (proofEraseCtx Γ) u (proofErase Γ A) (proofErase Γ f))
    (RL : Compute (ErasedLevelCore D) (proofErase Γ (t.inst (.lam A (.app f.lift (.bvar 0))))) left)
    (RR : Compute (ErasedLevelCore D) (proofErase Γ (t.inst f)) right) :
    ComputedJointCompare Step (proofEraseCtx Γ) mode left right :=
  proofErase_sorted_eta_consumer_core_sorted_check hs hc (fun H => hcore H)
    (fun H W => hrename H W) hΓ hA hf ht (fun HG => H.domains HG) (fun HG => H.origins HG) RL RR

end Lean4Lean.VEnv.Strengthening
