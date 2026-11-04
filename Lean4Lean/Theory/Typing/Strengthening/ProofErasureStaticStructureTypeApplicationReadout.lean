import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStaticStructureVariableReadout
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCommonNativeBinder

/-! # Returning a neutral type constructor applied to a type variable

Two finite sort demands distinguish the argument from the result. Both are
typed at universes, so structure eta cannot consume either marked node. The
function demand propagates through eta and beta while retaining the argument.
-/
namespace Lean4Lean.VEnv.Strengthening.ProofShape.TypeApplicationObservation
open _root_.Lean4Lean
open PureObservation (Ob)

/-- The two atomic demands name separate argument and result targets. -/
def Realizes (argument result e : ProofShape) : Ob → Prop
  | .pi => BetaRed e argument
  | .sort => BetaRed e result
  | .app keys o => ∀ a, (∀ key ∈ keys, Realizes argument result a key) →
      Realizes argument result (.app e a) o
termination_by o => sizeOf o

/-- Beta predecessors preserve either atomic target and every function demand. -/
theorem Realizes.beta_back (R : BetaRed e e') (H : Realizes argument result e' o) :
    Realizes argument result e o := by
  cases o with
  | pi | sort =>
    simp only [Realizes] at H ⊢
    exact R.trans H
  | app keys o =>
    simp only [Realizes] at H ⊢
    exact fun a ha => Realizes.beta_back (.app R .refl) (H a ha)
termination_by sizeOf o

/-- Empty literal-payload observations admit two independent meanings for
their atomic keys. Free-variable demands determine the resulting beta target. -/
theorem realizes
    (H : SortOriginObservation.Obs (fun _ => False) n S e o)
    (hσ : ∀ j key, S j key → Realizes argument result (σ j) key) :
    Realizes argument result (e.subst σ) o := by
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

end Lean4Lean.VEnv.Strengthening.ProofShape.TypeApplicationObservation

namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params] {D : PureObservation.Definitions}

/-- A neutral type constructor applied to an opaque type variable returns
from every full structure/function-eta computation by pure beta. This includes
type variables ranging over Prop; it does not assert return for data indices
or arbitrary type arguments. -/
theorem static_structure_neutral_type_application_readout
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ (.bvar f) (.forallE (.sort u) (.sort v)))
    (hx : env.HasType univs Γ (.bvar i) (.sort u))
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (.app (.bvar f) (.bvar i)) out) :
    ProofShape.BetaRed out (.app (.bvar f) (.bvar i)) := by
  have ht : env.HasType univs Γ (.app (.bvar f) (.bvar i)) (.sort v) := hf.app hx
  have EF : proofErase Γ (.bvar f) = .bvar f := if_neg (not_isProof_function_to_sort hΓ hf)
  have EX : proofErase Γ (.bvar i) = .bvar i := if_neg (not_isProof_of_sort hΓ hx)
  have EE : proofErase Γ (.app (.bvar f) (.bvar i)) = .app (.bvar f) (.bvar i) := by
    rw [show proofErase Γ (.app (.bvar f) (.bvar i)) = .app _ _ from
      if_neg (not_isProof_of_sort hΓ ht), EF, EX]
  have HF : ControlTyping (proofEraseCtx Γ) (.bvar f) (.arrow (.sort u) (.sort v)) :=
    ⟨Γ, _, hΓ, rfl, hf, EF⟩
  have HX : ControlTyping (proofEraseCtx Γ) (.bvar i) (.sort u) := ⟨Γ, _, hΓ, rfl, hx, EX⟩
  have HT : ControlTyping (proofEraseCtx Γ) (.app (.bvar f) (.bvar i)) (.sort v) :=
    ⟨Γ, _, hΓ, rfl, ht, EE⟩
  let S : SortControlObservation.Sets := fun j t o =>
    (j = f ∧ t = .arrow (.sort u) (.sort v) ∧ o = .app [.pi] .sort) ∨
    (j = i ∧ t = .sort u ∧ o = .pi)
  have HS : S.Typed (proofEraseCtx Γ) := by
    intro j t o H
    rcases H with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact HF
    · exact HX
  have H : SortControlObservation.Obs (fun _ => False) 0 (proofEraseCtx Γ) S
      (.app (.bvar f) (.bvar i)) (.sort v) .sort := by
    apply SortControlObservation.Obs.app HT (keys := [.pi])
    · exact .var HF (.fn (by intro key hk; obtain rfl := List.mem_singleton.1 hk; exact .neutral)
        .payload) (.inl ⟨rfl, rfl, rfl⟩)
    · intro key hk
      obtain rfl := List.mem_singleton.1 hk
      exact .var HX .neutral (.inr ⟨rfl, rfl, rfl⟩)
  have HO := proofErase_scoped_compute_sortObservation
    (erased_static_structure_eta_expansion_union_descent heq hs)
    (erased_static_structure_union_sortObservation heq hs (fun H _ _ => H.elim))
    R hΓ ht rfl EE HS H
  have HN := HO.forget
    (T := fun j key => (j = f ∧ key = .app [.pi] .sort) ∨ (j = i ∧ key = .pi))
    (fun _ _ _ H => H.elim (fun H => .inl ⟨H.1, H.2.2⟩) (fun H => .inr ⟨H.1, H.2.2⟩))
  have HR := TypeApplicationObservation.realizes (argument := .bvar i)
    (result := .app (.bvar f) (.bvar i)) HN (σ := ProofShape.Subst.id) (fun j key hj => by
      rcases hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · simp only [TypeApplicationObservation.Realizes, ProofShape.Subst.id]
        intro a ha
        have HA := ha .pi (by simp)
        simp only [TypeApplicationObservation.Realizes] at HA
        exact .app .refl HA
      · simp only [TypeApplicationObservation.Realizes, ProofShape.Subst.id]
        exact .refl)
  simpa only [ProofShape.subst_id, TypeApplicationObservation.Realizes] using HR

/-- Common native evidence for a retained value assigned F A restores that
exact type when F is a universe-to-universe variable and A is a type variable.
The value itself is unrestricted. This supplies the existing exact native
substitution and beta laws with their required image certificate. -/
theorem CommonNativeArgument.exact_type_application
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ (.bvar f) (.forallE (.sort u) (.sort v)))
    (hx : env.HasType univs Γ (.bvar i) (.sort u))
    (H : CommonNativeArgument D Γ p (.app (.bvar f) (.bvar i)))
    (hn : ¬ IsProof Γ p) :
    ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ p) (proofErase Γ (.app (.bvar f) (.bvar i))) := by
  obtain ⟨shared, RN, RC⟩ := H hn
  have ht : env.HasType univs Γ (.app (.bvar f) (.bvar i)) (.sort v) := hf.app hx
  have E : proofErase Γ (.app (.bvar f) (.bvar i)) = .app (.bvar f) (.bvar i) := by
    rw [show proofErase Γ (.app (.bvar f) (.bvar i)) = .app _ _ from
      if_neg (not_isProof_of_sort hΓ ht)]
    rw [show proofErase Γ (.bvar f) = .bvar f from if_neg (not_isProof_function_to_sort hΓ hf),
      show proofErase Γ (.bvar i) = .bvar i from if_neg (not_isProof_of_sort hΓ hx)]
  rw [E] at RC ⊢
  exact RN.convert (.beta (static_structure_neutral_type_application_readout heq hs hΓ hf hx RC))

end Lean4Lean.VEnv.Strengthening
