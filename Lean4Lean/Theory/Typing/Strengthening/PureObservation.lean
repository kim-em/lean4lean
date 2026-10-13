import Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta

/-! # Finite observations for beta and function eta

These observations ignore lambda annotations and observe only Pi/sort heads and
finite application behavior. They are used for head exposure, not equality
reflection: ignoring annotations cannot justify arbitrary definitional equality.
The interpretation has no declaration computation or projection clauses yet.
-/
namespace Lean4Lean.VEnv.Strengthening.PureObservation
open _root_.Lean4Lean _root_.Lean4Lean.VExpr

/-- A finite demand on a function, or a non-function type head. -/
inductive Ob where
  | pi
  | sort
  | app (keys : List Ob) (result : Ob)

/-- A stronger observation satisfies a weaker one. Function arguments vary
contravariantly, including their own finite demands. -/
inductive Ob.Le : Ob → Ob → Prop where
  | refl : Ob.Le o o
  | app (f : Ob → Ob) : (∀ k ∈ K, f k ∈ K') → (∀ k ∈ K, Ob.Le (f k) k) →
      Ob.Le o o' → Ob.Le (.app K o) (.app K' o')

/-- Operational meaning of a finite observation. No typing is assumed. -/
def Realizes (e : VExpr) : Ob → Prop
  | .pi => ∃ A B, BetaRed e (.forallE A B)
  | .sort => ∃ u, BetaRed e (.sort u)
  | .app keys result => ∀ a, (∀ key ∈ keys, Realizes a key) → Realizes (.app e a) result
termination_by o => sizeOf o

/-- Beta predecessors realize every observation realized by their reduct. -/
theorem Realizes.beta_back (R : BetaRed e e') (H : Realizes e' o) : Realizes e o := by
  cases o with
  | pi => simp only [Realizes] at H ⊢; obtain ⟨A, B, H⟩ := H; exact ⟨A, B, R.trans H⟩
  | sort => simp only [Realizes] at H ⊢; obtain ⟨u, H⟩ := H; exact ⟨u, R.trans H⟩
  | app keys result =>
    simp only [Realizes] at H ⊢
    intro a ha
    exact Realizes.beta_back (.app R .refl) (H a ha)
termination_by sizeOf o

/-- Operational realization respects observation subsumption. -/
theorem Realizes.mono (h : Ob.Le o o') (H : Realizes e o) : Realizes e o' := by
  induction h generalizing e with
  | refl => exact H
  | app f hf _ _ ihk iho =>
    simp only [Realizes] at H ⊢
    intro a ha
    exact iho (H a (fun k hk => ihk k hk (ha (f k) (hf k hk))))

abbrev Sets := Nat → Ob → Prop

def Sets.cons (head : Ob → Prop) (tail : Sets) : Sets
  | 0 => head
  | i+1 => tail i

/-- Interpretation by finite demands. Subsumption saturates each observation set;
function annotations are ignored, and Pi bodies are not evaluated. -/
inductive Obs : Sets → VExpr → Ob → Prop where
  | var : S i o → Obs S (.bvar i) o
  | sort : Obs S (.sort u) .sort
  | pi : Obs S (.forallE A B) .pi
  | app : Obs S f (.app keys o) → (∀ key ∈ keys, Obs S a key) → Obs S (.app f a) o
  | lam : Obs (Sets.cons (fun key => key ∈ keys) S) b o → Obs S (.lam A b) (.app keys o)
  | sub : Obs S e o → Ob.Le o o' → Obs S e o'

/-- A syntactic substitution realizes a valuation when it supplies all demanded
observations of every variable. -/
def RealizesSets (σ : VExpr.Subst) (S : Sets) : Prop :=
  ∀ i o, S i o → Realizes (σ i) o

/-- Every observation has operational content after any realizing substitution.
The lambda case uses one beta step and extends the realizing valuation. -/
theorem Obs.realizes (H : Obs S e o) (hσ : RealizesSets σ S) : Realizes (e.subst σ) o := by
  induction H generalizing σ with
  | var h => exact hσ _ _ h
  | sort => simp only [Realizes]; exact ⟨_, .refl⟩
  | pi => simp only [Realizes]; exact ⟨_, _, .refl⟩
  | app _ _ ihf iha =>
    have hf := ihf hσ
    simp only [Realizes] at hf
    exact hf _ (fun key hk => iha key hk hσ)
  | @lam keys S b o A _ ih =>
    simp only [Realizes]
    intro a ha
    have hb := ih (σ := σ.cons a) (by
      intro i key hi
      cases i with
      | zero => exact ha key hi
      | succ i => exact hσ i key hi)
    have R : BetaRed (.app ((VExpr.lam A b).subst σ) a) (b.subst (σ.cons a)) := by
      simpa only [VExpr.subst, inst_lift_cons] using
        (BetaRed.beta (A := A.subst σ) (b := b.subst σ.lift) (a := a))
    exact Realizes.beta_back R hb
  | sub _ h ih => exact Realizes.mono h (ih hσ)

/-- A Pi observation at the empty valuation exposes an actual Pi by beta reduction. -/
theorem Obs.pi_exposure (H : Obs (fun _ _ => False) e .pi) :
    ∃ A B, BetaRed e (.forallE A B) := by
  have h := H.realizes (σ := .id) (fun _ _ h => h.elim)
  simpa only [subst_id, Realizes] using h

/-- A sort observation likewise exposes an actual sort by beta reduction. -/
theorem Obs.sort_exposure (H : Obs (fun _ _ => False) e .sort) :
    ∃ u, BetaRed e (.sort u) := by
  have h := H.realizes (σ := .id) (fun _ _ h => h.elim)
  simpa only [subst_id, Realizes] using h

end Lean4Lean.VEnv.Strengthening.PureObservation
