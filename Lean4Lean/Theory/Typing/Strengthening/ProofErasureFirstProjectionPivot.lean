import Lean4Lean.Theory.Typing.Strengthening.ProofErasureNativeTransferBinders
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureWrappedCutSquare

/-! # Historical cut pivots beneath the first structure projection

The first field's native type recipe has no preceding field projections, so
exact native-output transfer survives this projection without a type-joining
premise. A projection whose major still has a lambda-headed cut cannot contract
at its root. Its expansion competitors can therefore use the historical pivot.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private empty_compute_beta from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedComparison
variable [Params] {D : PureObservation.Definitions}

/-- The first projection's recipe depends on its selected parameters, but
not on its major. Thus every native output transfers exactly, with no ordinary
typing or native argument certificate required for the target major. -/
theorem NativeOutputTransfer.proj_zero (H : NativeOutputTransfer Step Δ source pivot) (s : Name) :
    NativeOutputTransfer Step Δ (.proj s 0 source) (.proj s 0 pivot) := by
  intro out RN
  generalize E : ProofShape.proj s 0 source = e at RN
  induction RN with
  | proj hi HT hj hl RM =>
    cases E
    have R := ScopedTypeRecovery.proj hi HT hj hl (H _ RM)
    simpa only [projectionType, projectionArgs, List.range_zero, List.map_nil, List.append_nil] using R
  | convert _ RC ih => exact (ih H E).convert RC
  | bvar | sort | const | app | lam | forallE => cases E

omit [Params] in
private theorem constant_spine_not_proj (c ls args s j m) :
    ProofShape.mkApps (.const c ls) args ≠ .proj s j m := by
  cases args using List.snoc_induction with
  | nil => exact ProofShape.noConfusion
  | snoc args a => rw [ProofShape.mkApps_snoc]; exact ProofShape.noConfusion

omit [Params] in
private theorem constant_spine_head (c ls args) : PrimitiveHead (ProofShape.mkApps (.const c ls) args) := by
  induction args using List.snoc_induction with
  | nil => trivial
  | snoc args a ih => simpa only [ProofShape.mkApps_snoc, PrimitiveHead] using ih

omit [Params] in
private theorem match_not_proj (H : ProofShape.Matches p e ls captures) : ∀ s j m, e ≠ .proj s j m := by
  cases H <;> exact fun _ _ _ => ProofShape.noConfusion

/-- A projection above a nonopaque major has no contracting root primitive.
All four expansion kinds remain possible, including structure eta. -/
theorem static_structure_projection_primitive
    (hhead : ¬ PrimitiveHead major)
    (RP : ErasedStaticStructureEtaExpansionUnion D Δ (.proj s j major) expanded) :
    ConstantExpansion (.proj s j major) expanded ∨
      NativeIdentityExpansion (ErasedStaticStructureEtaExpansionUnion D) Δ (.proj s j major) expanded ∨
      NativeEtaExpansion (ErasedStaticStructureEtaExpansionUnion D) Δ (.proj s j major) expanded ∨
      NativeMaskedStructureExpansion (ErasedStaticStructureEtaExpansionUnion D) Δ (.proj s j major) expanded := by
  obtain ⟨stage, RP⟩ := RP
  induction stage with
  | zero =>
    rcases RP with ((RP | RP) | RP) | RP
    · rcases RP with RP | RP
      · cases RP with
        | projIota => exact (hhead (constant_spine_head ..)).elim
      · cases RP with
        | select _ _ HM | apply _ _ HM => exact (match_not_proj HM _ _ _ rfl).elim
    · cases RP with
      | intro _ _ _ HM => exact (match_not_proj HM _ _ _ rfl).elim
    · cases RP
    · exact .inl RP
  | succ stage ih =>
    rcases RP with RP | RP | RP | RP | RP | RP
    · exact ih RP
    · obtain ⟨_, RP⟩ := RP
      generalize E : ProofShape.proj s j major = src at RP
      cases RP with
      | intro => exact (constant_spine_not_proj _ _ _ _ _ _ E.symm).elim
    · cases RP
    · exact .inr (.inl (RP.mono (fun H => ⟨stage, H⟩)))
    · exact .inr (.inr (.inl (RP.mono (fun H => ⟨stage, H⟩))))
    · exact .inr (.inr (.inr (RP.mono (fun H => ⟨stage, H⟩))))

/-- The native-pivot square depends only on the classification of a root as
an expansion. This also applies to projected cuts, whose outer syntax has a
projection head even though their major prevents projection contraction. -/
theorem native_pivot_expansion_square
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (Rbefore : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) Δ original pivot)
    (Rafter : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) Δ pivot target)
    (HN : NativeOutputTransfer (ErasedStaticStructureEtaExpansionUnion D) Δ source pivot)
    (Rβ : ProofShape.BetaRed source target)
    (RP : ConstantExpansion source expanded ∨
      NativeIdentityExpansion (ErasedStaticStructureEtaExpansionUnion D) Δ source expanded ∨
      NativeEtaExpansion (ErasedStaticStructureEtaExpansionUnion D) Δ source expanded ∨
      NativeMaskedStructureExpansion (ErasedStaticStructureEtaExpansionUnion D) Δ source expanded) :
    ∃ shared, ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) Δ original shared ∧
      ProofShape.BetaRed expanded shared := by
  rcases RP with RC | RI | RE | RS
  · cases RC
    exact ⟨_, Rbefore.trans Rafter, (constantExpansion_beta _).trans Rβ⟩
  · cases RI
    exact ⟨_, Rbefore.trans Rafter, (raw_identity_beta _ _).trans Rβ⟩
  · cases RE with
    | intro RN SD =>
      have RL := static_structure_compute_under_domain heq hs SD Rafter
      exact ⟨_, Rbefore.trans ((ScopedCompute.base
          (erased_static_structure_eta_expansion_union_eta (.intro (HN _ RN) SD))).trans
            (.lam .refl (.app RL .refl))),
        .lam .refl (.app Rβ.liftN .refl)⟩
  · cases RS with
    | intro hi hx ha hp RN =>
      refine ⟨_, Rbefore.trans ((ScopedCompute.base
        (erased_static_structure_eta_expansion_union_structure (.intro hi hx ha hp (HN _ RN)))).trans
          (nativeStructureOutput_compute (List.Forall₂.rfl (fun _ _ => ScopedCompute.refl)) Rafter)), ?_⟩
      apply empty_compute_beta
      exact (nativeStructureOutput_compute (List.Forall₂.rfl (fun _ _ => ScopedCompute.refl))
        (ScopedCompute.beta (Step := fun _ _ _ => False) (Δ := Δ) Rβ)).core_forget

/-- Every primitive above a first-field projection of a wrapped historical cut
joins the projected pivot. No fresh native evidence is required after the
major's history has advanced. Dependent later fields are not covered here. -/
theorem WrappedCut.Valid.first_projection_primitive_square {cut : WrappedCut}
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (H : WrappedCut.Valid D Γ A b x u B cut)
    (hn : ¬ IsProof Γ (.app (.lam A b) x))
    (HR : ¬ IsProof Γ x → ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D)
      (proofEraseCtx Γ) (proofErase Γ x) (proofErase Γ A))
    (Rbefore : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      original (.proj s 0 (cut.pivot Γ x)))
    (RP : ErasedStaticStructureEtaExpansionUnion D (proofEraseCtx Γ) (.proj s 0 cut.source) expanded) :
    ∃ shared, ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      original shared ∧ ProofShape.BetaRed expanded shared := by
  rcases cut.source_root_cases Γ x with E | ⟨hhead, _⟩
  · rw [E] at RP
    exact ⟨expanded, Rbefore.trans (.base RP), .refl⟩
  · exact native_pivot_expansion_square heq hs Rbefore
      (.proj (H.compute_readout heq hs hΓ hn HR))
      ((H.native heq hs hΓ hn HR).proj_zero s) (.proj cut.beta_readout)
      (static_structure_projection_primitive hhead RP)

/-- A whole wrapped-cut development may occur below the first projection,
then a primitive may act at the projection root and beta may continue arbitrarily.
This extends the application-spine square to a projection context. It does not
assert coverage of arbitrary later dependent fields or all full-union paths. -/
theorem native_cut_first_projection_development_square
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) (hb : env.HasType univs (A :: Γ) b B)
    (hx : env.HasType univs Γ x A)
    (hn : ¬ IsProof Γ (.app (.lam A b) x))
    (HR : ¬ IsProof Γ x → ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D)
      (proofEraseCtx Γ) (proofErase Γ x) (proofErase Γ A))
    (R : ReflTransGen (WrappedCutStep D Γ A b x u B)
      (.cut (proofErase Γ A, proofErase (A :: Γ) b, proofErase Γ x) b) t)
    (RP : ErasedStaticStructureEtaExpansionUnion D (proofEraseCtx Γ) (.proj s 0 t.source) expanded)
    (RB : ProofShape.BetaRed expanded out) :
    ∃ shared, ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (.proj s 0 (proofErase Γ (b.inst x))) shared ∧ ProofShape.BetaRed out shared := by
  obtain ⟨H, _, Rbefore⟩ := wrapped_cut_steps_simulate heq hs hΓ hn HR R
    (.cut (CutPivotHistory.refl hA hb hx))
  obtain ⟨shared, RL, RR⟩ := H.first_projection_primitive_square heq hs hΓ hn HR (.proj Rbefore) RP
  obtain ⟨shared', RO, RL'⟩ := RB.raw_confluent RR
  exact ⟨shared', RL.trans (.beta RL'), RO⟩

end Lean4Lean.VEnv.Strengthening
