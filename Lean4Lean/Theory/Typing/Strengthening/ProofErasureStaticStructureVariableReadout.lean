import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStaticStructureSortReadout

/-! # Reading an opaque type variable through guarded expansion

A sort demand can mark a free variable instead of a literal universe. With
literal payloads excluded, the existing typed observation transport retains
that variable through all control frames. Its readout is pure beta reduction.
-/
namespace Lean4Lean.VEnv.Strengthening.ProofShape.VariableTypeObservation
open _root_.Lean4Lean
open PureObservation (Ob)

/-- Interpret a sort demand as return to one fixed opaque type variable. -/
def Realizes (i : Nat) (e : ProofShape) : Ob → Prop
  | .pi => False
  | .sort => BetaRed e (.bvar i)
  | .app keys o => ∀ a, (∀ key ∈ keys, Realizes i a key) → Realizes i (.app e a) o
termination_by o => sizeOf o

/-- Beta predecessors preserve a demand for the same fixed variable. -/
theorem Realizes.beta_back (R : BetaRed e e') (H : Realizes i e' o) : Realizes i e o := by
  cases o with
  | sort =>
    simp only [Realizes] at H ⊢
    exact R.trans H
  | pi => simp only [Realizes] at H
  | app keys o =>
    simp only [Realizes] at H ⊢
    exact fun a ha => Realizes.beta_back (.app R .refl) (H a ha)
termination_by sizeOf o

/-- Without literal payloads, finite observations are parametric in the
meaning of their free demands. Temporary binders are discharged by substitution. -/
theorem realizes
    (H : SortOriginObservation.Obs (fun _ => False) n S e o)
    (hσ : ∀ j key, S j key → Realizes i (σ j) key) : Realizes i (e.subst σ) o := by
  induction H generalizing σ with
  | var h => exact hσ _ _ h
  | payload h => exact h.elim
  | app _ _ ihf iha =>
    have HF := ihf hσ
    simp only [Realizes] at HF
    exact HF _ (fun key hk => iha key hk hσ)
  | @lam n keys S b o A _ ih =>
    simp only [Realizes]
    intro a ha
    have HB := ih (σ := σ.cons a) (fun j key hj => by
      cases j with
      | zero => exact ha key hj
      | succ j => exact hσ j key hj)
    have E : (b.subst σ.lift).inst a = b.subst (σ.cons a) := by
      simp only [inst_eq_subst, Subst.liftN, subst_subst]
      congr 1
      funext j
      cases j with
      | zero => rfl
      | succ j => simp only [Subst.comp, Subst.lift, Subst.one, Subst.cons, lift_subst_cons, subst_id]
    exact Realizes.beta_back (E ▸ (BetaRed.beta (A := A.subst σ))) HB

end Lean4Lean.VEnv.Strengthening.ProofShape.VariableTypeObservation

namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params] {D : PureObservation.Definitions}

/-- A computation from an opaque variable assigned a universe beta-reduces
back to exactly that variable. Structure eta is excluded by its sort type,
and function demands cannot replace the marked sort demand. No normalization
or confluence theorem is assumed for arbitrary terms. -/
theorem proofErase_static_structure_union_type_variable_readout
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ (.bvar i) (.sort u))
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) (.bvar i) out) :
    ProofShape.BetaRed out (.bvar i) := by
  let S : SortControlObservation.Sets := fun j t o => j = i ∧ t = .sort u ∧ o = .sort
  have E : proofErase Γ (.bvar i) = .bvar i := if_neg (not_isProof_of_sort hΓ ht)
  have HC : ControlTyping (proofEraseCtx Γ) (.bvar i) (.sort u) := ⟨Γ, _, hΓ, rfl, ht, E⟩
  have H : SortControlObservation.Obs (fun _ => False) 0 (proofEraseCtx Γ) S
      (.bvar i) (.sort u) .sort := .var HC .payload ⟨rfl, rfl, rfl⟩
  have HS : S.Typed (proofEraseCtx Γ) := by
    rintro j t o ⟨rfl, rfl, rfl⟩
    exact HC
  have HO := proofErase_scoped_compute_sortObservation
    (erased_static_structure_eta_expansion_union_descent heq hs)
    (erased_static_structure_union_sortObservation heq hs (fun H _ _ => H.elim))
    R hΓ ht rfl E HS H
  have HF := HO.forget (T := fun j key => j = i ∧ key = .sort) (fun _ _ _ H => ⟨H.1, H.2.2⟩)
  have HR := VariableTypeObservation.realizes (i := i) HF (σ := ProofShape.Subst.id) (fun j key hj => by
    obtain ⟨rfl, rfl⟩ := hj
    simpa only [VariableTypeObservation.Realizes, ProofShape.Subst.id] using
      (ProofShape.BetaRed.refl (e := .bvar j)))
  simpa only [ProofShape.subst_id, VariableTypeObservation.Realizes] using HR

end Lean4Lean.VEnv.Strengthening
