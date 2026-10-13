import Lean4Lean.Theory.Typing.Strengthening.PatternComputation

/-! # Constructor tuple observations for pattern computation

A constructor observation exposes one constructor spine and retains simultaneous
finite demands on all its arguments. Projection constructors use field observations
instead, so structure eta cannot create a constructor test.
-/
namespace Lean4Lean.VEnv.Strengthening.ConstructorObservation
open _root_.Lean4Lean _root_.Lean4Lean.VExpr
open PureObservation (Definitions PatternCompute CheckFromTyping)

/-- A finite demand on a function, or a non-function type head. -/
inductive Ob where
  | pi
  | sort
  | app (keys : List Ob) (result : Ob)
  | field (family : Name) (index : Nat) (result : Ob)
  | ctor (name : Name) (keys : List (List Ob))

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
  | .pi => ∃ A B, PatternCompute D e (.forallE A B)
  | .sort => ∃ u, PatternCompute D e (.sort u)
  | .ctor c keys => ∃ ls args, PatternCompute D e (mkApps (.const c ls) args) ∧
      ∃ hlen : keys.length = args.length,
        ∀ i (hi : i < keys.length) key, key ∈ keys[i] →
          Realizes D (args[i]'(hlen ▸ hi)) key
  | .field s i result => Realizes D (.proj s i e) result
  | .app keys result => ∀ a, (∀ key ∈ keys, Realizes D a key) → Realizes D (.app e a) result
termination_by o => sizeOf o
decreasing_by
  all_goals simp_wf
  · have hkey := List.sizeOf_lt_of_mem ‹key ∈ keys[i]›
    have hkeys := List.sizeOf_get keys ⟨i, hi⟩
    simp only [List.get_eq_getElem] at hkeys
    omega
  all_goals decreasing_tactic <;> omega

/-- Computation predecessors realize every observation realized by their reduct. -/
theorem Realizes.compute_back (R : PatternCompute D e e') (H : Realizes D e' o) : Realizes D e o := by
  cases o with
  | pi => simp only [Realizes] at H ⊢; obtain ⟨A, B, H⟩ := H; exact ⟨A, B, R.trans H⟩
  | sort => simp only [Realizes] at H ⊢; obtain ⟨u, H⟩ := H; exact ⟨u, R.trans H⟩
  | ctor c keys =>
    simp only [Realizes] at H ⊢
    obtain ⟨ls, args, hr, hl, ha⟩ := H
    exact ⟨ls, args, R.trans hr, hl, ha⟩
  | field s i result =>
    simp only [Realizes] at H ⊢
    exact Realizes.compute_back (.proj R) H
  | app keys result =>
    simp only [Realizes] at H ⊢
    intro a ha
    exact Realizes.compute_back (.app R (.refl)) (H a ha)
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

/-- Introduce a single exposed constructor tuple with all its finite demands. -/
theorem Realizes.ctor_intro (R : PatternCompute D e (mkApps (.const c ls) args))
    (ha : List.Forall₂ (fun K a => ∀ key ∈ K, Realizes D a key) keys args) :
    Realizes D e (.ctor c keys) := by
  simp only [Realizes]
  exact ⟨ls, args, R, ha.length_eq, fun i hi key hk =>
    ha.getElem_of i hi (ha.length_eq ▸ hi) key hk⟩

/-- Constructor demands come from one common exposure, with no joining premise. -/
theorem Realizes.ctor_inv (H : Realizes D e (.ctor c keys)) :
    ∃ ls args, PatternCompute D e (mkApps (.const c ls) args) ∧
      List.Forall₂ (fun K a => ∀ key ∈ K, Realizes D a key) keys args := by
  simp only [Realizes] at H
  obtain ⟨ls, args, hr, hl, ha⟩ := H
  exact ⟨ls, args, hr, List.forall₂_of_getElem hl (fun i hi _ => ha i hi)⟩

/-- Ordinary constructor tests are excluded for registered projection constructors. -/
def NotProjectionCtor (c : Name) : Prop :=
  ∀ s info, Params.env.projections s info → info.ctorName ≠ c

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

omit [Params] in
/-- Every capture of a constant spine is one of its numbered arguments. -/
theorem spine_path_surj {c : Name} : ∀ n (x : ((Pattern.const c).varN n).Path),
    ∃ (i : Nat) (hi : i < n), Pattern.varN_pathOf n i hi = x
  | 0, x => nomatch x
  | n+1, none => ⟨n, by omega, by simp [Pattern.varN_pathOf]; rfl⟩
  | n+1, some x => by
    obtain ⟨i, hi, rfl⟩ := spine_path_surj n x
    exact ⟨i, by omega, by simp [Pattern.varN_pathOf, show i ≠ n by omega]; rfl⟩

omit [Params] in
/-- Capture demands in the argument order of a constant spine. -/
def spineKeys {c : Name} {n : Nat} (K : ((Pattern.const c).varN n).Path → List Ob) :
    List (List Ob) := List.ofFn fun i : Fin n => K (Pattern.varN_pathOf n i i.isLt)

omit [Params] in
/-- Translate an indexed match into a relation between every capture and its
finite demand list. This lemma is shared by operational and syntactic observations. -/
theorem spineKeys_demands {c : Name} {n : Nat}
    {K : ((Pattern.const c).varN n).Path → List Ob} {captures : ((Pattern.const c).varN n).Path → VExpr}
    {args : List VExpr} {P : VExpr → Ob → Prop} (hlen : args.length = n)
    (hget : ∀ i (hi : i < n), captures (Pattern.varN_pathOf n i hi) = args[i]'(hlen ▸ hi)) :
    List.Forall₂ (fun keys a => ∀ key ∈ keys, P a key) (spineKeys K) args ↔
      ∀ p key, key ∈ K p → P (captures p) key := by
  have hkeys : (spineKeys K).length = n := by simp [spineKeys]
  constructor
  · intro H p key hk
    obtain ⟨i, hi, rfl⟩ := spine_path_surj n p
    have h := H.getElem_of i (by omega) (by omega)
    simp only [spineKeys, List.getElem_ofFn] at h
    rw [hget]
    exact h key hk
  · intro H
    apply List.forall₂_of_getElem (by omega)
    intro i hi hj key hk
    simp only [spineKeys, List.getElem_ofFn] at hk
    have h := H (Pattern.varN_pathOf n i (by omega)) key hk
    rwa [hget] at h

/-- A finite semantic certificate for an instantiated rule RHS. It quantifies
over all captures, so it is independent of the occurrence and its valuation. -/
def RHSRealizes {p : Pattern} (D : Definitions) (r : p.RHS) (levels : List VLevel)
    (K : p.Path → List Ob) (o : Ob) : Prop :=
  ∀ captures, (∀ p key, key ∈ K p → Realizes D (captures p) key) →
    Realizes D (r.apply levels captures) o

/-- A recursor consumes one shared constructor tuple and the finite demands on
its prefix arguments. The arbitrary pattern RHS is handled by its certificate. -/
theorem Realizes.recursor {recursor ctor : Name} {major fields : Nat}
    {r : (SimplePattern.iota recursor major ctor fields).toPattern.RHS ×
      (SimplePattern.iota recursor major ctor fields).toPattern.Check}
    {K : (SimplePattern.iota recursor major ctor fields).toPattern.Path → List Ob}
    (hp : Params.Pat _ r) (hc : CheckFromTyping Params.env Params.univs _ r levels)
    (hr : RHSRealizes D r.1 levels K o) :
    Realizes D (.const recursor levels)
      (Ob.wrap (spineKeys (fun p => K (.inl p)))
        (.app [.ctor ctor (spineKeys (fun p => K (.inr p)))] o)) := by
  apply Realizes.wrap_intro
  intro recArgs hrecArgs
  simp only [Realizes]
  intro majorExpr hmajor
  obtain ⟨ctorLevels, ctorArgs, hcompute, hctorArgs⟩ :=
    (hmajor (.ctor ctor (spineKeys (fun p => K (.inr p)))) (by simp)).ctor_inv
  have hrecLen : recArgs.length = major := by simpa [spineKeys] using hrecArgs.length_eq.symm
  have hctorLen : ctorArgs.length = fields := by simpa [spineKeys] using hctorArgs.length_eq.symm
  obtain ⟨recCaptures, hmrec, hgrec⟩ := Pattern.matches_varN_const major recArgs hrecLen
  obtain ⟨ctorCaptures, hmctor, hgctor⟩ := Pattern.matches_varN_const fields ctorArgs hctorLen
  have hrec := (spineKeys_demands hrecLen hgrec).1 hrecArgs
  have hctor := (spineKeys_demands hctorLen hgctor).1 hctorArgs
  have hRHS := hr (Sum.elim recCaptures ctorCaptures) (by
    intro p key hk
    cases p with
    | inl p => exact hrec p key hk
    | inr p => exact hctor p key hk)
  apply Realizes.compute_back (PatternCompute.app .refl hcompute)
  exact Realizes.compute_back (.pattern hp (.app hmrec hmctor) hc) hRHS

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
  | ctorTuple : NotProjectionCtor c →
      Obs D S (.const c ls) (Ob.wrap keys (.ctor c keys))
  | recursor {r : (SimplePattern.iota recursor major ctor fields).toPattern.RHS ×
        (SimplePattern.iota recursor major ctor fields).toPattern.Check}
      {K : (SimplePattern.iota recursor major ctor fields).toPattern.Path → List Ob} :
      Params.Pat _ r → CheckFromTyping Params.env Params.univs _ r levels →
      RHSRealizes D r.1 levels K o →
      Obs D S (.const recursor levels)
        (Ob.wrap (spineKeys (fun p => K (.inl p)))
          (.app [.ctor ctor (spineKeys (fun p => K (.inr p)))] o))
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
    exact Realizes.compute_back (.base (.base (.of_beta R))) hb
  | delta hd _ ih =>
    have hr := ih (σ := .id) (fun _ _ h => h.elim)
    rw [subst_id] at hr
    exact Realizes.compute_back (.base (.base (.delta hd))) hr
  | ctor hi hl hg ho =>
    apply Realizes.wrap_intro
    intro args hargs
    obtain ⟨field, hf, hfield⟩ := select_forall₂ hargs hg
    simp only [Realizes]
    exact Realizes.compute_back (.base (.projIota hi (hargs.length_eq.symm.trans hl) hf)) (hfield _ ho)
  | ctorTuple _ =>
    apply Realizes.wrap_intro
    intro args hargs
    exact Realizes.ctor_intro .refl hargs
  | recursor hp hc hr => exact Realizes.recursor hp hc hr
  | proj _ ih => simpa only [Realizes, VExpr.subst] using ih hσ
  | sub _ h ih => exact Realizes.mono h (ih hσ)

/-- A Pi observation at the empty valuation exposes an actual Pi by beta and declaration reduction. -/
theorem Obs.pi_exposure (H : Obs D (fun _ _ => False) e .pi) :
    ∃ A B, PatternCompute D e (.forallE A B) := by
  have h := H.realizes (σ := .id) (fun _ _ h => h.elim)
  simpa only [subst_id, Realizes] using h

/-- A sort observation likewise exposes an actual sort by beta and declaration reduction. -/
theorem Obs.sort_exposure (H : Obs D (fun _ _ => False) e .sort) :
    ∃ u, PatternCompute D e (.sort u) := by
  have h := H.realizes (σ := .id) (fun _ _ h => h.elim)
  simpa only [subst_id, Realizes] using h

end Lean4Lean.VEnv.Strengthening.ConstructorObservation
