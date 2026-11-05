import Lean4Lean.Theory.Typing.Strengthening.ProofErasureNativePivotPrimitiveSquare
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCutHistoryLocalSquare

/-! # Historical cut squares under arbitrary pending application spines

A marked historical beta cut can occur in function position at any depth.
Its uniform pivot supplies guards at every surrounding application. Component
histories and pending argument computations are followed by any single step,
including a primitive at a surrounding root or a step inside a pending argument.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params] {D : PureObservation.Definitions}

omit [Params] in
private theorem cut_spine_not_primitive (s : CutComponents) (args : List ProofShape) :
    ¬ PrimitiveHead (ProofShape.mkApps s.redex args) := by
  induction args using List.snoc_induction with
  | nil => exact id
  | snoc args a ih => simpa only [ProofShape.mkApps_snoc, PrimitiveHead] using ih

omit [Params] in
private theorem cut_spine_not_sort (s : CutComponents) (args : List ProofShape) (u) :
    ProofShape.mkApps s.redex args ≠ .sort u := by
  cases args using List.snoc_induction with
  | nil => exact ProofShape.noConfusion
  | snoc args a => rw [ProofShape.mkApps_snoc]; exact ProofShape.noConfusion

omit [Params] in
private theorem cut_spine_not_lam (s : CutComponents) (args : List ProofShape) (A b) :
    ProofShape.mkApps s.redex args ≠ .lam A b := by
  cases args using List.snoc_induction with
  | nil => exact ProofShape.noConfusion
  | snoc args a => rw [ProofShape.mkApps_snoc]; exact ProofShape.noConfusion

omit [Params] in
private theorem beta_spine (R : ProofShape.BetaRed f g) (args : List ProofShape) :
    ProofShape.BetaRed (ProofShape.mkApps f args) (ProofShape.mkApps g args) := by
  induction args using List.snoc_induction with
  | nil => exact R
  | snoc args a ih => simpa only [ProofShape.mkApps_snoc] using ProofShape.BetaRed.app ih (.refl (e := a))

/-- Every primitive at any surrounding application of the historical cut
joins the original contractum in that spine. All pending arguments are raw;
none is required to carry native recovery. -/
theorem CutComponentHistory.spine_primitive_square
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (H : CutComponentHistory D Γ A b x u B s)
    (hn : ¬ IsProof Γ (.app (.lam A b) x))
    (HR : ¬ IsProof Γ x → ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D)
      (proofEraseCtx Γ) (proofErase Γ x) (proofErase Γ A))
    (RP : ErasedStaticStructureEtaExpansionUnion D (proofEraseCtx Γ)
      (ProofShape.mkApps s.redex args) expanded) :
    ∃ shared, ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (ProofShape.mkApps (proofErase Γ (b.inst x)) args) shared ∧ ProofShape.BetaRed expanded shared := by
  obtain ⟨pivot, _, HP⟩ := H.spine_pivot_uniform heq hs hΓ hn HR
  obtain ⟨RL, RR, HN⟩ := HP args
  exact native_pivot_primitive_square heq hs (cut_spine_not_primitive s args)
    (cut_spine_not_sort s args) RL RR HN (beta_spine (ProofShape.BetaRed.beta
      (A := s.1) (b := s.2.1) (a := s.2.2)) args) RP

omit [Params] in
private theorem step_app_cases
    (R : ScopedStep Step Δ (.app f a) out) :
    Step Δ (.app f a) out ∨
      (∃ A b, f = .lam A b ∧ out = b.inst a) ∨
      (∃ g, out = .app g a ∧ ScopedStep Step Δ f g) ∨
      (∃ a', out = .app f a' ∧ ScopedStep Step Δ a a') := by
  cases R with
  | primitive RP => exact .inl RP
  | beta => exact .inr (.inl ⟨_, _, rfl, rfl⟩)
  | appL RF => exact .inr (.inr (.inl ⟨_, rfl, RF⟩))
  | appR RA => exact .inr (.inr (.inr ⟨_, rfl, RA⟩))

/-- An arbitrary single-occurrence competitor of a historical cut inside an
application spine joins the original contractum in that spine. This handles
primitive roots at every enclosing application and steps within any argument. -/
theorem CutComponentHistory.spine_step_square
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (H : CutComponentHistory D Γ A b x u B s)
    (hn : ¬ IsProof Γ (.app (.lam A b) x))
    (HR : ¬ IsProof Γ x → ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D)
      (proofEraseCtx Γ) (proofErase Γ x) (proofErase Γ A))
    (R : ScopedStep (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (ProofShape.mkApps s.redex args) out) :
    ∃ shared, ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (ProofShape.mkApps (proofErase Γ (b.inst x)) args) shared ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) out shared := by
  induction args using List.snoc_induction generalizing out with
  | nil => exact H.step_square heq hs hΓ hn HR R
  | snoc args a ih =>
    rw [ProofShape.mkApps_snoc] at R ⊢
    rcases step_app_cases R with RP | ⟨C, d, EF, _⟩ | ⟨g, rfl, RF⟩ | ⟨a', rfl, RA⟩
    · rw [← ProofShape.mkApps_snoc] at RP ⊢
      obtain ⟨shared, RL, RR⟩ := H.spine_primitive_square heq hs hΓ hn HR RP
      exact ⟨shared, RL, .beta RR⟩
    · exact (cut_spine_not_lam s args C d EF).elim
    · obtain ⟨shared, RL, RR⟩ := ih RF
      exact ⟨_, .app RL .refl, .app RR .refl⟩
    · have RC := (H.contract heq hs hΓ HR).1.mkApps
        (List.Forall₂.rfl (fun _ _ => ScopedCompute.refl) (l := args))
      exact ⟨_, .app RC RA.compute,
        .app (.beta (beta_spine (ProofShape.BetaRed.beta
          (A := s.1) (b := s.2.1) (a := s.2.2)) args)) .refl⟩

/-- Finite component histories and independent computations of every pending
argument may precede the competing step. This is a contextual one-step square;
unrestricted continuation after root expansion still needs a history invariant
that survives the resulting change of shape. -/
theorem native_cut_spine_development_step_square
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) (hb : env.HasType univs (A :: Γ) b B)
    (hx : env.HasType univs Γ x A)
    (hn : ¬ IsProof Γ (.app (.lam A b) x))
    (HR : ¬ IsProof Γ x → ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D)
      (proofEraseCtx Γ) (proofErase Γ x) (proofErase Γ A))
    (RC : ReflTransGen (CutComponentRound D (proofEraseCtx Γ))
      (proofErase Γ A, proofErase (A :: Γ) b, proofErase Γ x) s)
    (RA : List.Forall₂ (ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)) args₀ args)
    (R : ScopedStep (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (ProofShape.mkApps s.redex args) out) :
    ∃ shared, ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (ProofShape.mkApps (proofErase Γ (b.inst x)) args₀) shared ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) out shared := by
  obtain ⟨shared, RL, RR⟩ := ((CutComponentHistory.refl hA hb hx).rounds heq hs hΓ RC).spine_step_square
    heq hs hΓ hn HR R
  exact ⟨shared, (ScopedCompute.refl.mkApps RA).trans RL, RR⟩

end Lean4Lean.VEnv.Strengthening
