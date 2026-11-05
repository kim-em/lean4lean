import Lean4Lean.Theory.Typing.Strengthening.ProofErasureAtomicUnitTransport

/-! # Computational readout of unit function demands

Pointwise function demands can use structural computation of unit results.
This interpretation is applied in the caller's actual fresh-argument context;
it does not assert return of a function's own annotation.
-/
namespace Lean4Lean.VEnv.Strengthening.AtomicUnitObservation
open _root_.Lean4Lean Params ProofShape
open AtomicControl (Atom ControlType)
open PureObservation (Ob)
variable [Params] [Atom]

/-- An atomic observation computes to the unit constructor; function demands
consume computationally realized inputs. -/
def Computes (Step : List ProofShape → ProofShape → ProofShape → Prop)
    (Δ : List ProofShape) (c : Name) (e : ProofShape) (t : ControlType) : Ob → Prop
  | .pi => ScopedCompute Step Δ e (.const c [])
  | .sort => False
  | .app keys o => match t with
    | .arrow A B => ∀ a, (∀ key ∈ keys, Computes Step Δ c a A key) → Computes Step Δ c (.app e a) B o
    | _ => False
termination_by o => sizeOf o

omit [Params] [Atom] in
/-- Beta predecessors preserve computational unit demands. -/
theorem Computes.beta_back (R : ProofShape.BetaRed e e') (H : Computes Step Δ c e' t o) :
    Computes Step Δ c e t o := by
  cases o with
  | sort => simp only [Computes] at H
  | pi =>
    simp only [Computes] at H ⊢
    exact (ScopedCompute.beta R).trans H
  | app keys o =>
    cases t with
    | atom | sort => simp only [Computes] at H
    | arrow A B =>
      simp only [Computes] at H ⊢
      exact fun a ha => Computes.beta_back (.app R .refl) (H a ha)
termination_by sizeOf o

/-- Typed unit observations have a computational interpretation under every
raw substitution supplying their free demands. The output world is fixed; the supplied realizations carry the actual
computation paths. -/
theorem Obs.computes (H : Obs c Ω S e t o)
    (hσ : ∀ i t key, S i t key → Computes Step Δ c (σ i) t key) :
    Computes Step Δ c (e.subst σ) t o := by
  induction H generalizing σ with
  | var _ _ h => exact hσ _ _ _ h
  | terminal => simp only [Computes]; exact .refl
  | app _ _ _ ihf iha =>
    have HF := ihf hσ
    simp only [Computes] at HF
    exact HF _ (fun key hk => iha key hk hσ)
  | @lam Δ D b A B keys S o _ _ _ ih =>
    simp only [Computes]
    intro a ha
    have HB := ih (σ := σ.cons a) (fun i t key hi => by
      cases i with
      | zero => obtain ⟨rfl, hk⟩ := hi; exact ha key hk
      | succ i => exact hσ i t key hi)
    have E : (b.subst σ.lift).inst a = b.subst (σ.cons a) := by
      simp only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN, ProofShape.subst_subst]
      congr 1
      funext i
      cases i with
      | zero => rfl
      | succ i => simp only [ProofShape.Subst.comp, ProofShape.Subst.lift, ProofShape.Subst.one, ProofShape.Subst.cons, ProofShape.lift_subst_cons, ProofShape.subst_id]
    exact Computes.beta_back (E ▸ (ProofShape.BetaRed.beta (A := D.subst σ))) HB

end Lean4Lean.VEnv.Strengthening.AtomicUnitObservation
