import Lean4Lean.Theory.Typing.Strengthening.ProofErasureWrappedCutHistory
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureNativeBetaPrimitiveResidual

/-! # Developments that create, evolve and remove historical cut frames

Source guards create paired frames by native transfer. Afterwards the argument
may evolve and lose that guard: ordinary annotation witnesses suffice. The
selected pivot follows every step by forward computation, including creation
and contraction of any number of nested constant, identity and eta frames.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params] {D : PureObservation.Definitions}

/-- A marked development includes leaf component rounds, contraction,
native constant/identity/eta creation, beta-wrapper removal, annotation
computation, eta-argument computation and recursive evolution inside frames.
Once source and pivot coincide, any whole-term continuation is synchronized. Structure frames,
arbitrary computation of beta-wrapper control functions and unrestricted
eta-body root steps while the mark remains active are not yet constructors. -/
inductive WrappedCutStep (D : PureObservation.Definitions) (Γ : List VExpr)
    (A b x : VExpr) (u : VLevel) (B : VExpr) : WrappedCut → WrappedCut → Prop where
  | cut : CutComponentRound D (proofEraseCtx Γ) s t →
      CutPivotHistory D Γ A b x u B t d' →
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ (d.inst x)) (proofErase Γ (d'.inst x)) →
      WrappedCutStep D Γ A b x u B (.cut s d) (.cut t d')
  | cut_contract : WrappedCutStep D Γ A b x u B (.cut s d) (.done (s.2.1.inst s.2.2))
  | done_compute : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) e e' →
      WrappedCutStep D Γ A b x u B (.done e) (.done e')
  | constant_expand : WrappedCutStep D Γ A b x u B s (.constant s)
  | identity_expand : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D)
      (proofEraseCtx Γ) s.source C → WrappedCutStep D Γ A b x u B s (.identity C s)
  | constant_contract : WrappedCutStep D Γ A b x u B (.constant s) s
  | identity_contract : WrappedCutStep D Γ A b x u B (.identity C s) s
  | constant_inner : WrappedCutStep D Γ A b x u B s t →
      WrappedCutStep D Γ A b x u B (.constant s) (.constant t)
  | identity_inner : WrappedCutStep D Γ A b x u B s t →
      WrappedCutStep D Γ A b x u B (.identity C s) (.identity C t)
  | identity_annotation : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D)
      (proofEraseCtx Γ) C C' → WrappedCutStep D Γ A b x u B (.identity C s) (.identity C' s)
  | eta_expand : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D)
      (proofEraseCtx Γ) s.source (.forallE C E) → DomainSort (proofEraseCtx Γ) C v →
      WrappedCutStep D Γ A b x u B s (.eta C (etaArgument v) s)
  | eta_inner : WrappedCutStep D Γ A b x u B s t →
      WrappedCutStep D Γ A b x u B (.eta C argument s) (.eta C argument t)
  | eta_annotation : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D)
      (proofEraseCtx Γ) C C' → WrappedCutStep D Γ A b x u B (.eta C argument s) (.eta C' argument s)
  | eta_argument : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D)
      (C :: proofEraseCtx Γ) argument argument' →
      WrappedCutStep D Γ A b x u B (.eta C argument s) (.eta C argument' s)
  | synchronized_compute : s.source = s.pivot Γ x →
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) s.source out →
      WrappedCutStep D Γ A b x u B s (.done out)

/-- Every component round has a compatible selected-body successor. Thus the
cut constructor's pivot path is proved for arbitrary rounds, rather than an
assumed preservation obligation imposed on future computations. -/
theorem CutPivotHistory.wrapper_round
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (H : CutPivotHistory D Γ A b x u B s d)
    (HR : ¬ IsProof Γ x → ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D)
      (proofEraseCtx Γ) (proofErase Γ x) (proofErase Γ A))
    (R : CutComponentRound D (proofEraseCtx Γ) s t) :
    ∃ d', WrappedCutStep D Γ A b x u B (.cut s d) (.cut t d') := by
  obtain ⟨d', H', RP⟩ := H.advance heq hs hΓ HR R
  exact ⟨d', .cut R H' RP⟩

/-- A wrapper step preserves its history and has forward simulations on both
sides. Native guards are transferred only when frames are created; no guard is
renewed when a frame argument or its stored annotation computes. -/
theorem WrappedCutStep.simulate
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hn : ¬ IsProof Γ (.app (.lam A b) x))
    (HR : ¬ IsProof Γ x → ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D)
      (proofEraseCtx Γ) (proofErase Γ x) (proofErase Γ A))
    (R : WrappedCutStep D Γ A b x u B s t) (H : WrappedCut.Valid D Γ A b x u B s) :
    WrappedCut.Valid D Γ A b x u B t ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) s.source t.source ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) (s.pivot Γ x) (t.pivot Γ x) := by
  induction R with
  | cut RC H' RP => exact ⟨.cut H', RC.compute, RP⟩
  | @cut_contract c d =>
    cases H with
    | cut H =>
      obtain ⟨T, HT⟩ := H.source_witness hΓ hn
      have RB : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
          c.redex (c.2.1.inst c.2.2) := .beta .beta
      have hnp : c.redex ≠ ProofShape.proof := ProofShape.noConfusion
      exact ⟨.done (HT.compute_term heq hs hΓ RB) (HT.not_proof_after heq hs hΓ hnp RB),
        RB, (H.native heq hs hΓ hn HR).2⟩
  | done_compute R =>
    cases H with
    | done HT hnp =>
      exact ⟨.done (HT.compute_term heq hs hΓ R) (HT.not_proof_after heq hs hΓ hnp R), R, R⟩
  | @constant_expand s =>
    exact ⟨.constant H, .base ⟨0, .inr (.intro H.source_ne_proof)⟩,
      .base ⟨0, .inr (.intro (H.pivot_ne_proof hΓ hn))⟩⟩
  | identity_expand RN =>
    obtain ⟨T, HT⟩ := H.source_witness hΓ hn
    have HP := (H.native heq hs hΓ hn HR) _ RN
    exact ⟨.identity H (HT.of_native heq hs hΓ RN),
      .base (erased_static_structure_eta_expansion_union_identity (.intro RN)),
      .base (erased_static_structure_eta_expansion_union_identity (.intro HP))⟩
  | constant_contract =>
    cases H with
    | constant H => exact ⟨H, .beta (constantExpansion_beta _), .beta (constantExpansion_beta _)⟩
  | identity_contract =>
    cases H with
    | identity H _ => exact ⟨H, .beta (raw_identity_beta _ _), .beta (raw_identity_beta _ _)⟩
  | constant_inner _ ih =>
    cases H with
    | constant H =>
      obtain ⟨H', RS, RP⟩ := ih H
      exact ⟨.constant H', static_structure_constant_compute heq hs hΓ RS,
        static_structure_constant_compute heq hs hΓ RP⟩
  | identity_inner _ ih =>
    cases H with
    | identity H HT =>
      obtain ⟨H', RS, RP⟩ := ih H
      exact ⟨.identity H' (HT.compute_term heq hs hΓ RS), .app .refl RS, .app .refl RP⟩
  | identity_annotation RA =>
    cases H with
    | identity H HT =>
      exact ⟨.identity H (HT.compute_type heq hs hΓ RA),
        .app (.lam RA .refl) .refl, .app (.lam RA .refl) .refl⟩
  | eta_expand RN SD =>
    obtain ⟨_, HT⟩ := H.source_witness hΓ hn
    have HP := (H.native heq hs hΓ hn HR) _ RN
    obtain ⟨_, HE⟩ := (EtaFrameWitness.of_native heq hs hΓ HT RN SD).source_witness hΓ H.source_ne_proof
    exact ⟨.eta H SD HE,
      .base (erased_static_structure_eta_expansion_union_eta (.intro RN SD)),
      .base (erased_static_structure_eta_expansion_union_eta (.intro HP SD))⟩
  | eta_inner _ ih =>
    cases H with
    | eta H SD HT =>
      obtain ⟨H', RS, RP⟩ := ih H
      exact ⟨.eta H' SD (HT.compute_term heq hs hΓ (static_structure_eta_frame_compute heq hs SD RS)),
        static_structure_eta_frame_compute heq hs SD RS,
        static_structure_eta_frame_compute heq hs SD RP⟩
  | eta_annotation RA =>
    cases H with
    | eta H SD HT =>
      exact ⟨.eta H (SD.scoped_compute (erased_static_structure_eta_expansion_union_descent heq hs) RA)
        (HT.compute_term heq hs hΓ (.lam RA .refl)), .lam RA .refl, .lam RA .refl⟩
  | eta_argument RA =>
    cases H with
    | eta H SD HT =>
      exact ⟨.eta H SD (HT.compute_term heq hs hΓ (.lam .refl (.app .refl RA))),
        .lam .refl (.app .refl RA), .lam .refl (.app .refl RA)⟩
  | synchronized_compute E R =>
    obtain ⟨_, HT⟩ := H.source_witness hΓ hn
    exact ⟨.done (HT.compute_term heq hs hΓ R)
      (HT.not_proof_after heq hs hΓ H.source_ne_proof R), R, E ▸ R⟩

/-- The simulations compose for arbitrarily many nested wrapper changes.
This is an invariant of the entire development, not just its final local peak. -/
theorem wrapped_cut_steps_simulate
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hn : ¬ IsProof Γ (.app (.lam A b) x))
    (HR : ¬ IsProof Γ x → ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D)
      (proofEraseCtx Γ) (proofErase Γ x) (proofErase Γ A))
    (R : ReflTransGen (WrappedCutStep D Γ A b x u B) s t)
    (H : WrappedCut.Valid D Γ A b x u B s) :
    WrappedCut.Valid D Γ A b x u B t ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) s.source t.source ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) (s.pivot Γ x) (t.pivot Γ x) := by
  induction R with
  | rfl => exact ⟨H, .refl, .refl⟩
  | tail _ R ih =>
    obtain ⟨H₁, RS₁, RP₁⟩ := ih
    obtain ⟨H₂, RS₂, RP₂⟩ := R.simulate heq hs hΓ hn HR H₁
    exact ⟨H₂, RS₁.trans RS₂, RP₁.trans RP₂⟩

/-- A finite wrapper development joins contraction of the original native
cut. Frames may be created, evolved recursively and removed repeatedly. -/
theorem native_cut_wrapper_development
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) (hb : env.HasType univs (A :: Γ) b B)
    (hx : env.HasType univs Γ x A)
    (hn : ¬ IsProof Γ (.app (.lam A b) x))
    (HR : ¬ IsProof Γ x → ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D)
      (proofEraseCtx Γ) (proofErase Γ x) (proofErase Γ A))
    (R : ReflTransGen (WrappedCutStep D Γ A b x u B)
      (.cut (proofErase Γ A, proofErase (A :: Γ) b, proofErase Γ x) b) t) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ (b.inst x)) t.readout ∧ ProofShape.BetaRed t.source t.readout := by
  obtain ⟨H, _, RP⟩ := wrapped_cut_steps_simulate heq hs hΓ hn HR R
    (.cut (CutPivotHistory.refl hA hb hx))
  exact ⟨RP.trans (H.compute_readout heq hs hΓ hn HR), t.beta_readout⟩

end Lean4Lean.VEnv.Strengthening
