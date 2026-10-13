import Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta

/-! # Finite observations for beta and function eta

These observations ignore lambda annotations and observe only Pi/sort heads and
finite application behavior. They are used for head exposure, not equality
reflection: ignoring annotations cannot justify arbitrary definitional equality.
Closed declaration bodies may be unfolded finitely, including recursive bodies.
Projection computation is not part of this interpretation.
-/
namespace Lean4Lean.VEnv.Strengthening.PureObservation
open _root_.Lean4Lean _root_.Lean4Lean.VExpr

/-- A collection of constant equations with closed right-hand sides. No termination
or acyclicity is required, and several equations may share the same constant. -/
structure Definitions where
  unfolds : Name → List VLevel → VExpr → Prop
  closed : unfolds c ls rhs → rhs.Closed

/-- The original beta-only model is the instance with no declaration equations. -/
def Definitions.empty : Definitions := ⟨fun _ _ _ => False, False.elim⟩

/-- Finite compatible beta reduction and closed constant unfolding. -/
inductive Compute (D : Definitions) : VExpr → VExpr → Prop where
  | refl : Compute D e e
  | trans : Compute D a b → Compute D b c → Compute D a c
  | beta : Compute D (.app (.lam A b) a) (b.inst a)
  | delta : D.unfolds c ls rhs → Compute D (.const c ls) rhs
  | app : Compute D f f' → Compute D a a' → Compute D (.app f a) (.app f' a')
  | lam : Compute D A A' → Compute D b b' → Compute D (.lam A b) (.lam A' b')
  | forallE : Compute D A A' → Compute D B B' → Compute D (.forallE A B) (.forallE A' B')
  | proj : Compute D m m' → Compute D (.proj s i m) (.proj s i m')

variable {D : Definitions}

/-- Beta reduction is available for every collection of declaration equations. -/
theorem Compute.of_beta (R : BetaRed e out) : Compute D e out := by
  induction R with
  | refl => exact .refl
  | trans _ _ ih1 ih2 => exact .trans ih1 ih2
  | beta => exact .beta
  | app _ _ ih1 ih2 => exact .app ih1 ih2
  | lam _ _ ih1 ih2 => exact .lam ih1 ih2
  | forallE _ _ ih1 ih2 => exact .forallE ih1 ih2
  | proj _ ih => exact .proj ih

/-- With no equations the operational relation is precisely finite beta reduction. -/
theorem Compute.to_beta (R : Compute .empty e out) : BetaRed e out := by
  induction R with
  | refl => exact .refl
  | trans _ _ ih1 ih2 => exact .trans ih1 ih2
  | beta => exact .beta
  | delta h => exact h.elim
  | app _ _ ih1 ih2 => exact .app ih1 ih2
  | lam _ _ ih1 ih2 => exact .lam ih1 ih2
  | forallE _ _ ih1 ih2 => exact .forallE ih1 ih2
  | proj _ ih => exact .proj ih

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
def Realizes (D : Definitions) (e : VExpr) : Ob → Prop
  | .pi => ∃ A B, Compute D e (.forallE A B)
  | .sort => ∃ u, Compute D e (.sort u)
  | .app keys result => ∀ a, (∀ key ∈ keys, Realizes D a key) → Realizes D (.app e a) result
termination_by o => sizeOf o

/-- Computation predecessors realize every observation realized by their reduct. -/
theorem Realizes.compute_back (R : Compute D e e') (H : Realizes D e' o) : Realizes D e o := by
  cases o with
  | pi => simp only [Realizes] at H ⊢; obtain ⟨A, B, H⟩ := H; exact ⟨A, B, R.trans H⟩
  | sort => simp only [Realizes] at H ⊢; obtain ⟨u, H⟩ := H; exact ⟨u, R.trans H⟩
  | app keys result =>
    simp only [Realizes] at H ⊢
    intro a ha
    exact Realizes.compute_back (.app R .refl) (H a ha)
termination_by sizeOf o

/-- Operational realization respects observation subsumption. -/
theorem Realizes.mono (h : Ob.Le o o') (H : Realizes D e o) : Realizes D e o' := by
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
inductive Obs (D : Definitions) : Sets → VExpr → Ob → Prop where
  | var : S i o → Obs D S (.bvar i) o
  | sort : Obs D S (.sort u) .sort
  | pi : Obs D S (.forallE A B) .pi
  | app : Obs D S f (.app keys o) → (∀ key ∈ keys, Obs D S a key) → Obs D S (.app f a) o
  | lam : Obs D (Sets.cons (fun key => key ∈ keys) S) b o → Obs D S (.lam A b) (.app keys o)
  | delta : D.unfolds c ls rhs → Obs D (fun _ _ => False) rhs o → Obs D S (.const c ls) o
  | sub : Obs D S e o → Ob.Le o o' → Obs D S e o'

/-- A syntactic substitution realizes a valuation when it supplies all demanded
observations of every variable. -/
def RealizesSets (D : Definitions) (σ : VExpr.Subst) (S : Sets) : Prop :=
  ∀ i o, S i o → Realizes D (σ i) o

/-- Every observation has operational content after any realizing substitution.
The lambda case uses one beta step and extends the realizing valuation. -/
theorem Obs.realizes (H : Obs D S e o) (hσ : RealizesSets D σ S) : Realizes D (e.subst σ) o := by
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
    exact Realizes.compute_back (.of_beta R) hb
  | delta hd _ ih =>
    have hr := ih (σ := .id) (fun _ _ h => h.elim)
    rw [subst_id] at hr
    exact Realizes.compute_back (.delta hd) hr
  | sub _ h ih => exact Realizes.mono h (ih hσ)

/-- A Pi observation at the empty valuation exposes an actual Pi by beta and declaration reduction. -/
theorem Obs.pi_exposure (H : Obs D (fun _ _ => False) e .pi) :
    ∃ A B, Compute D e (.forallE A B) := by
  have h := H.realizes (σ := .id) (fun _ _ h => h.elim)
  simpa only [subst_id, Realizes] using h

/-- A sort observation likewise exposes an actual sort by beta and declaration reduction. -/
theorem Obs.sort_exposure (H : Obs D (fun _ _ => False) e .sort) :
    ∃ u, Compute D e (.sort u) := by
  have h := H.realizes (σ := .id) (fun _ _ h => h.elim)
  simpa only [subst_id, Realizes] using h

end Lean4Lean.VEnv.Strengthening.PureObservation
