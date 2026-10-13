import Lean4Lean.Theory.Typing.Strengthening.ProjectionComputation

/-! # Finite field observations with operational realization

This extends the beta/delta observation argument to registered constructors and
projections. Constructor observations demand a finite observation of a selected
argument; field observations realize actual projection computation. There are no
quotient classes or normalization assumptions. The beta-only model remains a
separate specialization while this larger operational interface is developed.
-/
namespace Lean4Lean.VEnv.Strengthening.FieldObservation
open _root_.Lean4Lean _root_.Lean4Lean.VExpr
open PureObservation (Definitions ProjectionCompute)

/-- A finite demand on a function, or a non-function type head. -/
inductive Ob where
  | pi
  | sort
  | app (keys : List Ob) (result : Ob)
  | field (family : Name) (index : Nat) (result : Ob)

/-- A stronger observation satisfies a weaker one. Function arguments vary
contravariantly, including their own finite demands. -/
inductive Ob.Le : Ob → Ob → Prop where
  | refl : Ob.Le o o
  | app (f : Ob → Ob) : (∀ k ∈ K, f k ∈ K') → (∀ k ∈ K, Ob.Le (f k) k) →
      Ob.Le o o' → Ob.Le (.app K o) (.app K' o')

  | field : Ob.Le o o' → Ob.Le (.field s i o) (.field s i o')

/-- A curried sequence of finite argument demands. -/
def Ob.wrap (keys : List (List Ob)) (result : Ob) : Ob :=
  keys.foldr Ob.app result

variable [Params]
variable {D : Definitions}

/-- Operational meaning of a finite observation. No typing is assumed. -/
def Realizes (D : Definitions) (e : VExpr) : Ob → Prop
  | .pi => ∃ A B, ProjectionCompute D e (.forallE A B)
  | .sort => ∃ u, ProjectionCompute D e (.sort u)
  | .field s i result => Realizes D (.proj s i e) result
  | .app keys result => ∀ a, (∀ key ∈ keys, Realizes D a key) → Realizes D (.app e a) result
termination_by o => sizeOf o

/-- Computation predecessors realize every observation realized by their reduct. -/
theorem Realizes.compute_back (R : ProjectionCompute D e e') (H : Realizes D e' o) : Realizes D e o := by
  cases o with
  | pi => simp only [Realizes] at H ⊢; obtain ⟨A, B, H⟩ := H; exact ⟨A, B, R.trans H⟩
  | sort => simp only [Realizes] at H ⊢; obtain ⟨u, H⟩ := H; exact ⟨u, R.trans H⟩
  | field s i result =>
    simp only [Realizes] at H ⊢
    exact Realizes.compute_back (.proj R) H
  | app keys result =>
    simp only [Realizes] at H ⊢
    intro a ha
    exact Realizes.compute_back (.app R (.base .refl)) (H a ha)
termination_by sizeOf o

/-- Operational realization respects observation subsumption. -/
theorem Realizes.mono (h : Ob.Le o o') (H : Realizes D e o) : Realizes D e o' := by
  induction h generalizing e with
  | refl => exact H
  | field _ ih => simp only [Realizes] at H ⊢; exact ih H
  | app f hf _ _ ihk iho =>
    simp only [Realizes] at H ⊢
    intro a ha
    exact iho (H a (fun k hk => ihk k hk (ha (f k) (hf k hk))))

/-- Realize a curried observation by realizing every demanded argument spine. -/
theorem Realizes.wrap_intro
    (H : ∀ args, List.Forall₂ (fun K a => ∀ key ∈ K, Realizes D a key) keys args →
      Realizes D (mkApps f args) result) : Realizes D f (Ob.wrap keys result) := by
  induction keys generalizing f with
  | nil => exact H [] .nil
  | cons K keys ih =>
    simp only [Ob.wrap, List.foldr_cons, Realizes]
    intro a ha
    apply ih
    intro args hargs
    exact H (a :: args) (.cons ha hargs)

omit [Params] in
/-- Select corresponding entries in a finite relation, retaining their relation. -/
theorem select_forall₂ {R : α → β → Prop} (H : List.Forall₂ R xs ys)
    {i : Nat} (hx : xs[i]? = some x) : ∃ y, ys[i]? = some y ∧ R x y := by
  induction H generalizing i with
  | nil => simp at hx
  | cons ha _ ih =>
    cases i with
    | zero => cases hx; exact ⟨_, rfl, ha⟩
    | succ i => exact ih hx

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
  | ctor : Params.env.projections s info → keys.length = info.nparams + info.numFields →
      keys[info.nparams + i]? = some K → o ∈ K →
      Obs D S (.const info.ctorName ls) (Ob.wrap keys (.field s i o))
  | proj : Obs D S m (.field s i o) → Obs D S (.proj s i m) o
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
  | sort => simp only [Realizes]; exact ⟨_, .base .refl⟩
  | pi => simp only [Realizes]; exact ⟨_, _, .base .refl⟩
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
    exact Realizes.compute_back (.base (.of_beta R)) hb
  | delta hd _ ih =>
    have hr := ih (σ := .id) (fun _ _ h => h.elim)
    rw [subst_id] at hr
    exact Realizes.compute_back (.base (.delta hd)) hr
  | ctor hi hl hg ho =>
    apply Realizes.wrap_intro
    intro args hargs
    obtain ⟨field, hf, hfield⟩ := select_forall₂ hargs hg
    simp only [Realizes]
    exact Realizes.compute_back (.projIota hi (hargs.length_eq.symm.trans hl) hf) (hfield _ ho)
  | proj _ ih => simpa only [Realizes, VExpr.subst] using ih hσ
  | sub _ h ih => exact Realizes.mono h (ih hσ)

/-- A Pi observation at the empty valuation exposes an actual Pi by beta and declaration reduction. -/
theorem Obs.pi_exposure (H : Obs D (fun _ _ => False) e .pi) :
    ∃ A B, ProjectionCompute D e (.forallE A B) := by
  have h := H.realizes (σ := .id) (fun _ _ h => h.elim)
  simpa only [subst_id, Realizes] using h

/-- A sort observation likewise exposes an actual sort by beta and declaration reduction. -/
theorem Obs.sort_exposure (H : Obs D (fun _ _ => False) e .sort) :
    ∃ u, ProjectionCompute D e (.sort u) := by
  have h := H.realizes (σ := .id) (fun _ _ h => h.elim)
  simpa only [subst_id, Realizes] using h

end Lean4Lean.VEnv.Strengthening.FieldObservation
