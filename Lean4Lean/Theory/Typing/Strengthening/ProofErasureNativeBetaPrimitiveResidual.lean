import Lean4Lean.Theory.Typing.Strengthening.ProofErasureNativeHeadBeta

/-! # Every primitive commutes with a certified root beta cut

A literal beta redex cannot be an opaque computational head. Its primitive
expansions are constant, identity, function eta or structure eta. Exact recovery
through the original certified cut supplies each residual guard, while beta
computes the old expansion to the same result. This does not certify arbitrary
later beta cuts after the argument has computed.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private beta_eq from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
variable [Params] {D : PureObservation.Definitions}

/-- Native identity guards over the union have a finite stage, independently
of the computation that produced their selected type. -/
theorem erased_static_structure_eta_expansion_union_identity
    (R : NativeIdentityExpansion (ErasedStaticStructureEtaExpansionUnion D) Δ a b) :
    ErasedStaticStructureEtaExpansionUnion D Δ a b := by
  cases R with
  | intro RN =>
    obtain ⟨stage, RN⟩ := RN.finite_stage (Stages := ErasedStaticStructureEtaExpansionStage D)
      (fun {n m} hle {Δ a b} H => erased_static_structure_eta_expansion_stage_mono hle H)
    exact ⟨stage+1, .inr (.inr (.inr (.inl (.intro RN))))⟩

/-- The fixed unused wrapper commutes with every certified head beta path.
Only preservation of proof status is needed for this primitive's residual. -/
theorem NativeHeadBeta.constant_residual
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (H : NativeHeadBeta D Γ e e')
    (RE : ConstantExpansion (proofErase Γ e) expanded) :
    ∃ shared, ConstantExpansion (proofErase Γ e') shared ∧ ProofShape.BetaRed expanded shared := by
  cases RE with
  | intro hn =>
    have HE := beta_eq hΓ ht H.beta_path
    have hn' : ¬ IsProof Γ e' := fun hp => hn (proofErase_eq_proof.2 ((isProof_congr hΓ HE).2 hp))
    exact ⟨_, .intro (fun E => hn' (proofErase_eq_proof.1 E)),
      .app (.lam .refl (proofErase_beta_forward hΓ ht H.beta_path).liftN) .refl⟩

/-- A literal raw beta redex admits only the four expansion primitives at its
root. Singleton, Eq, iota and universe roots are syntactically impossible. -/
theorem static_structure_beta_redex_primitive
    (RP : ErasedStaticStructureEtaExpansionUnion D Δ (.app (.lam A b) x) expanded) :
    ConstantExpansion (.app (.lam A b) x) expanded ∨
      NativeIdentityExpansion (ErasedStaticStructureEtaExpansionUnion D) Δ (.app (.lam A b) x) expanded ∨
      NativeEtaExpansion (ErasedStaticStructureEtaExpansionUnion D) Δ (.app (.lam A b) x) expanded ∨
      NativeMaskedStructureExpansion (ErasedStaticStructureEtaExpansionUnion D) Δ
        (.app (.lam A b) x) expanded := by
  obtain ⟨stage, RP⟩ := RP
  induction stage with
  | zero =>
    rcases RP with (RP | RP) | RP
    · exact (erased_iota_primitive_head RP).elim
    · cases RP
    · exact .inl RP
  | succ stage ih =>
    rcases RP with RP | RP | RP | RP | RP | RP
    · exact ih RP
    · exact RP.2.head.elim
    · exact RP.head.elim
    · exact .inr (.inl (RP.mono (fun H => ⟨stage, H⟩)))
    · exact .inr (.inr (.inl (RP.mono (fun H => ⟨stage, H⟩))))
    · exact .inr (.inr (.inr (RP.mono (fun H => ⟨stage, H⟩))))

/-- Every primitive-root competitor of a retained certified beta cut has an
exact commuting residual: a primitive from the contractum, and beta from the
expanded branch. The retained argument is required to recover only the original
written domain. No type-fork joining or native coverage premise occurs. -/
theorem native_root_beta_primitive_residual
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) (hb : env.HasType univs (A :: Γ) b B)
    (hx : env.HasType univs Γ x A)
    (hn : ¬ IsProof Γ (.app (.lam A b) x))
    (HR : ¬ IsProof Γ x → ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D)
      (proofEraseCtx Γ) (proofErase Γ x) (proofErase Γ A))
    (RP : ErasedStaticStructureEtaExpansionUnion D (proofEraseCtx Γ)
      (proofErase Γ (.app (.lam A b) x)) expanded) :
    ∃ shared, ErasedStaticStructureEtaExpansionUnion D (proofEraseCtx Γ)
        (proofErase Γ (b.inst x)) shared ∧ ProofShape.BetaRed expanded shared := by
  have ht := HasType.app (HasType.lam hA hb) hx
  have H : NativeHeadBeta D Γ (.app (.lam A b) x) (b.inst x) := .beta hA hb hx HR
  have hnf := not_isProof_fn hΓ (HasType.lam hA hb) hx hn
  have EE : proofErase Γ (.app (.lam A b) x) =
      .app (.lam (proofErase Γ A) (proofErase (A :: Γ) b)) (proofErase Γ x) := by
    rw [show proofErase Γ (.app (.lam A b) x) = .app _ _ from if_neg hn,
      show proofErase Γ (.lam A b) = .lam _ _ from if_neg hnf]
  have HH := static_structure_beta_redex_primitive (EE ▸ RP)
  rw [← EE] at HH
  rcases HH with RC | RI | RE | RS
  · obtain ⟨shared, RC, Rβ⟩ := H.constant_residual hΓ ht RC
    exact ⟨shared, ⟨0, .inr RC⟩, Rβ⟩
  · obtain ⟨shared, RI, Rβ⟩ := H.identity_residual heq hs hΓ ht RI
    exact ⟨shared, erased_static_structure_eta_expansion_union_identity RI, Rβ⟩
  · obtain ⟨shared, RE, Rβ⟩ := H.eta_residual heq hs hΓ ht RE
    exact ⟨shared, erased_static_structure_eta_expansion_union_eta RE, Rβ⟩
  · obtain ⟨shared, RS, Rβ⟩ := H.structure_residual heq hs hΓ ht RS
    exact ⟨shared, erased_static_structure_eta_expansion_union_structure RS, Rβ⟩

end Lean4Lean.VEnv.Strengthening
