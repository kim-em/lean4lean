import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypeContextStructureEta

/-! # Joining equality observations in type contexts

The observation of a data equation is a pair of types. Transitivity therefore
uses forks at typed types only. This does not supply binder congruence or prove
completeness for ordinary equality; those remain separate missing arguments.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params] {D : PureObservation.Definitions}

/-- Every typed type context gives a computational join after substituting the
two values. This is a relation, not an assumed completeness theorem. Endpoint
typings and context well-formedness are supplied by its individual uses. -/
def TypeContextJoin (D : PureObservation.Definitions) (Γ : List VExpr) (A a b : VExpr) : Prop :=
  ∀ {C v}, env.HasType univs (A :: Γ) C (.sort v) →
    ∃ shared, ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ (C.inst a)) shared ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ (C.inst b)) shared

/-- A value has the same observation as itself. -/
theorem TypeContextJoin.refl : TypeContextJoin D Γ A a a :=
  fun _ => ⟨_, .refl, .refl⟩

/-- Common reducts give symmetric observations. -/
theorem TypeContextJoin.symm (H : TypeContextJoin D Γ A a b) : TypeContextJoin D Γ A b a := by
  intro C v hC
  obtain ⟨s, L, R⟩ := H hC
  exact ⟨s, R, L⟩

/-- Type-only fork joining composes contextual observations of arbitrary data.
The fork's root is the typed observation of the middle value, so no confluence
hypothesis at data terms is used. Type-only fork joining is still open. -/
theorem TypeContextJoin.trans
    (HF : ∀ {Γ T u left right}, OnCtx Γ (env.IsType univs) →
      env.HasType univs Γ T (.sort u) →
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ T) left →
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ T) right →
      ∃ shared, ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) left shared ∧
        ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) right shared)
    (hΓ : OnCtx Γ (env.IsType univs)) (hb : env.HasType univs Γ b A)
    (Hab : TypeContextJoin D Γ A a b) (Hbc : TypeContextJoin D Γ A b c) :
    TypeContextJoin D Γ A a c := by
  intro C v hC
  obtain ⟨s, La, Lb⟩ := Hab hC
  obtain ⟨t, Rb, Rc⟩ := Hbc hC
  obtain ⟨r, L, R⟩ := HF hΓ (hC.instN henv.ordered Ctx.InstN.zero hb) Lb Rb
  exact ⟨r, La.trans L, Rc.trans R⟩

/-- Computing the actual argument through a typed context requires primitive
renaming only, including for the full structure/function-eta union. The output
may be raw and need not have a supplied native certificate. -/
theorem proofErase_static_structure_compute_inst_argument
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓA : OnCtx (A :: Γ) (env.IsType univs))
    (hC : env.HasType univs (A :: Γ) C T) (ha : env.HasType univs Γ a A)
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ a) out) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (C.inst a)) ((proofErase (A :: Γ) C).inst out) := by
  have W := (Ctx.InstN.zero (Γ₀ := Γ) (e₀ := a) (A₀ := A)).substEq hΓA ha
  have hrename : ∀ {Δ Δ' a b σ}, ErasedStaticStructureEtaExpansionUnion D Δ a b →
      ContextRenaming Δ Δ' σ → ErasedStaticStructureEtaExpansionUnion D Δ' (a.subst σ) (b.subst σ) := by
    intro Δ Δ' a b σ ⟨n, H⟩ W
    exact ⟨n, erased_static_structure_eta_expansion_stage_rename heq hs n H W⟩
  have H := proofErase_compute_subst_images_of_renaming hrename hΓA.1 W hC
    (erasedSubstAgreement_one hΓA ha) (τ := ProofShape.Subst.one out) (fun i => by
      cases i with
      | zero => exact R
      | succ i => exact .refl)
  rw [proofErase_instN hΓA ha Ctx.InstN.zero hC]
  simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using H

/-- An existing data join lifts through every typed type context without any
instantiation-joining or confluence assumption. Only the two source values
need ordinary typings; the common reduct may be raw. -/
theorem TypeContextJoin.of_compute_join
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓA : OnCtx (A :: Γ) (env.IsType univs))
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b A)
    (Ra : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ a) shared)
    (Rb : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ b) shared) : TypeContextJoin D Γ A a b := by
  intro C v hC
  exact ⟨_, proofErase_static_structure_compute_inst_argument heq hs hΓA hC ha Ra,
    proofErase_static_structure_compute_inst_argument heq hs hΓA hC hb Rb⟩

/-- Equal erasures, in particular proofs of a common proposition, have equal
contextual observations. No open joining premise is needed. -/
theorem TypeContextJoin.of_erasure_eq
    (hΓA : OnCtx (A :: Γ) (env.IsType univs))
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b A)
    (E : proofErase Γ a = proofErase Γ b) : TypeContextJoin D Γ A a b := by
  intro C v hC
  have EC : proofErase Γ (C.inst a) = proofErase Γ (C.inst b) := by
    rw [proofErase_instN hΓA ha Ctx.InstN.zero hC,
      proofErase_instN hΓA hb Ctx.InstN.zero hC, E]
  exact ⟨_, .refl, EC ▸ ScopedCompute.refl⟩

end Lean4Lean.VEnv.Strengthening
