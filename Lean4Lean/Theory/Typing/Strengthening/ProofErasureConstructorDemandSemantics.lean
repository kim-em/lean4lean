import Lean4Lean.Theory.Typing.Strengthening.ProofErasureConstructorDemandStages

/-! # Computational realizability of joint constructor demands

Free demands may be realized by full computations instead of literal beta
leaves. This permits native-certified functions that return the unit value
to supply higher-order inputs to a constructor program.
-/
namespace Lean4Lean.VEnv.Strengthening.ConstructorDemand
open _root_.Lean4Lean Params ProofShape
variable [Params] {unit record : AtomicControl.Atom} {uc ctor family : Name}

/-- A demanded value reaches its canonical unit/record instance. Function demands
consume realized arguments. Higher type keys constrain only the observer. -/
def Computes (Step : List ProofShape → ProofShape → ProofShape → Prop) (Δ : List ProofShape) (uc ctor family : Name) (e : ProofShape) : Key → Prop
  | .unit => ScopedCompute Step Δ e (.const uc [])
  | .record => ScopedCompute Step Δ e (.app (.const ctor []) (.const uc []))
  | .fn _ keys result => ∀ a, (∀ key ∈ keys, Computes Step Δ uc ctor family a key) → Computes Step Δ uc ctor family (.app e a) result
  | .type .record => ScopedCompute Step Δ e (.app (.const family []) (.const uc []))
  | .type _ => True
termination_by key => sizeOf key

/-- Beta predecessors retain computational demands. No general confluence or
substitution closure of Step is assumed. -/
theorem Computes.beta_back (R : BetaRed e e') (H : Computes Step Δ uc ctor family e' key) :
    Computes Step Δ uc ctor family e key := by
  cases key with
  | unit | record =>
    simp only [Computes] at H ⊢
    exact (ScopedCompute.beta R).trans H
  | fn A keys result =>
    simp only [Computes] at H ⊢
    exact fun a ha => Computes.beta_back (.app R .refl) (H a ha)
  | type key =>
    cases key with
    | unit | type | fn => simp only [Computes]
    | record =>
      simp only [Computes] at H ⊢
      exact (ScopedCompute.beta R).trans H
termination_by sizeOf key

/-- Any raw substitution realizing the free demands computes the observed
program at its result key. The output context is fixed; source typing witnesses
are used by preservation, not to assume native completeness for the images. -/
theorem Obs.computes (H : Obs unit record uc ctor family Ω S e key)
    (hσ : ∀ j key, S j key → Computes Step Δ uc ctor family (σ j) key) :
    Computes Step Δ uc ctor family (e.subst σ) key := by
  induction H generalizing σ with
  | var _ _ hi => exact hσ _ _ hi
  | unit_ctor => simp only [ProofShape.subst, Computes]; exact .refl
  | record_ctor | family =>
    simp only [ProofShape.subst, Computes]
    intro a ha
    have HA := ha .unit (by simp)
    simp only [Computes] at HA
    exact .app .refl HA
  | unit_type | univ | family_type | pi => simp only [Computes]
  | app _ _ _ ihf iha =>
    have HF := ihf hσ
    simp only [Computes] at HF
    exact HF _ (fun key hk => iha key hk hσ)
  | @lam Δ A b domain keys result S _ _ _ _ _ _ ihb =>
    simp only [Computes]
    intro a ha
    have HB := ihb (σ := σ.cons a) (fun j key hj => by
      cases j with
      | zero => exact ha key hj
      | succ j => exact hσ j key hj)
    have E : (b.subst σ.lift).inst a = b.subst (σ.cons a) := by
      simp only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN, ProofShape.subst_subst]
      congr 1
      funext j
      cases j with
      | zero => rfl
      | succ j => simp only [ProofShape.Subst.comp, ProofShape.Subst.lift, ProofShape.Subst.one,
          ProofShape.Subst.cons, ProofShape.lift_subst_cons, ProofShape.subst_id]
    exact Computes.beta_back (E ▸ (BetaRed.beta (A := A.subst σ))) HB


end Lean4Lean.VEnv.Strengthening.ConstructorDemand
