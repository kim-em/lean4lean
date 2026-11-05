import Lean4Lean.Theory.Typing.Strengthening.ProofErasureNativeHeaderApplication
import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePendingUnitNative

/-! # Repeated function-head expansions preserve native header ancestry

Constant, native identity and native function eta expansions may alternate with
unbounded finite nesting. Their actual guards use the full computation union.
This development relation records root expansions only: arbitrary compatible
computation inside the generated controls is not asserted to preserve ancestry.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean Params ProofShape
variable [Params] {D : PureObservation.Definitions}

/-- Native identity stores the original header path to its selected annotation. -/
theorem NativeHeaderHistory.native_identity
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hf : env.HasType univs Γ f T)
    (H : NativeHeaderHistory D Γ header (proofErase Γ f))
    (RE : NativeIdentityExpansion (ErasedStaticStructureEtaExpansionUnion D)
      (proofEraseCtx Γ) (proofErase Γ f) target) : NativeHeaderHistory D Γ header target := by
  cases RE with
  | intro RG =>
    have hn : ¬ IsProof Γ f := fun hp => RG.ne_proof (proofErase_eq_proof.2 hp)
    obtain ⟨A, hfA, EA⟩ := proofErase_scoped_typeRecovery_replay
      (erased_static_structure_eta_expansion_union_descent heq hs) hΓ hf RG
    rw [← EA]
    intro out RN
    exact NativeHeaderHistory.identity heq hs hΓ hfA hn (EA ▸ H RG) RN

/-- Actual full-union guards license a finite sequence of root control
expansions. There is no congruence or beta case hidden in this relation. -/
inductive FunctionHeadExpansion (D : PureObservation.Definitions) (Δ : List ProofShape) :
    ProofShape → ProofShape → Prop where
  | refl : FunctionHeadExpansion D Δ e e
  | constant : e ≠ .proof → FunctionHeadExpansion D Δ e (constantExpansion e)
  | identity : NativeIdentityExpansion (ErasedStaticStructureEtaExpansionUnion D) Δ e out →
      FunctionHeadExpansion D Δ e out
  | eta : NativeEtaExpansion (ErasedStaticStructureEtaExpansionUnion D) Δ e out →
      FunctionHeadExpansion D Δ e out
  | trans : FunctionHeadExpansion D Δ a b → FunctionHeadExpansion D Δ b c →
      FunctionHeadExpansion D Δ a c

/-- Every recorded expansion sequence is an actual full-union computation. -/
theorem FunctionHeadExpansion.compute (R : FunctionHeadExpansion D Δ a b) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) Δ a b := by
  induction R with
  | refl => exact .refl
  | constant hn => exact .base ⟨0, .inr (.intro hn)⟩
  | identity R =>
    cases R with
    | intro RN =>
      obtain ⟨n, RN⟩ := RN.finite_stage (Stages := ErasedStaticStructureEtaExpansionStage D)
        (fun {n m} hle {Δ a b} H => erased_static_structure_eta_expansion_stage_mono hle H)
      exact .base ⟨n+1, .inr (.inr (.inr (.inl (.intro RN))))⟩
  | eta R => exact .base (erased_static_structure_eta_expansion_union_eta R)
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- Repeated root expansions preserve the original typed Pi header even when
later native guards choose different annotations and different type histories. -/
theorem FunctionHeadExpansion.header
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) (hB : env.HasType univs (A :: Γ) B (.sort v))
    (R : FunctionHeadExpansion D (proofEraseCtx Γ) source out)
    (hf : env.HasType univs Γ f (.forallE A B)) (Ef : proofErase Γ f = source)
    (H : NativeHeaderHistory D Γ (proofErase Γ (.forallE A B)) source) :
    NativeHeaderHistory D Γ (proofErase Γ (.forallE A B)) out := by
  induction R generalizing f with
  | refl => exact H
  | constant hn =>
    cases Ef
    exact H.constant heq hs hΓ hf (fun hp => hn (proofErase_eq_proof.2 hp))
  | identity R => cases Ef; exact H.native_identity heq hs hΓ hf R
  | eta R => cases Ef; exact H.eta heq hs hΓ hA hB hf R
  | trans R₁ _ ih₁ ih₂ =>
    obtain ⟨g, Hfg, Eg⟩ := proofErase_scoped_compute_realize
      (erased_static_structure_eta_expansion_union_descent heq hs) hΓ hf rfl Ef R₁.compute
    exact ih₂ Hfg.hasType.2 Eg (ih₁ hf Ef H)

/-- An actual registered fieldless constructor can undergo arbitrarily many
root control expansions before its independently computed unit parameter is
supplied. Every native output and every later type continuation returns to the
canonical unit-family type. No computed family-header certificate is required. -/
theorem expanded_unit_constructor_application_native_return
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hz : info.numFields = 0)
    (hD : ∀ levels rhs, ¬ D.unfolds info.ctorName levels rhs)
    (hS : env.HasType univs [] (.const family []) (.sort (.succ u)))
    (hTag : env.projections r (PositiveHeaderRegistration.info 0 [.const family []] r c))
    (hDr : ∀ levels rhs, ¬ D.unfolds r levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hF : env.HasType univs Γ (.const r []) (.forallE (.const family []) (.sort v)))
    (hl : Lookup Γ i (.const family [])) (hn : ¬ IsProof Γ (.const c []))
    (RH : FunctionHeadExpansion D (proofEraseCtx Γ) (.const c []) head)
    (RX : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (.bvar i)) a)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (.app head a) T)
    (RT : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) T out) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      out (.app (.const r []) (.const info.ctorName [])) := by
  have hC : env.HasType univs Γ (.const c [])
      (.forallE (.const family []) (.app (.const r []) (.bvar 0))) :=
    .const (henv.ordered.projectionConstructor hTag) (by simp) rfl
  have EC : proofErase Γ (.const c []) = .const c [] := if_neg hn
  have hA : env.HasType univs Γ (.const family []) (.sort (.succ u)) := hS.weak0 henv.ordered
  have hB : env.HasType univs (.const family [] :: Γ) (.app (.const r []) (.bvar 0)) (.sort v) :=
    .app (hF.weak henv.ordered) (HasType.bvar .zero)
  have H : NativeHeaderHistory D Γ
      (proofErase Γ (.forallE (.const family []) (.app (.const r []) (.bvar 0)))) head :=
    RH.header heq hs hΓ hA hB hC EC
    (fun RN => registered_unit_constructor_function_history hΓ hTag RN)
  exact pending_unit_application_native_return heq hs hi hp hx hz hD hS
    (henv.projectionRigid hTag) hDr hΓ hF hl (fun _ _ RN => H RN) RX RN RT

end Lean4Lean.VEnv.Strengthening
