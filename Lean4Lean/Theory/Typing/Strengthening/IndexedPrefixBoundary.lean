import Lean4Lean.Theory.Typing.Strengthening.FullHeadExposure

/-! # A boundary of the current raw indexed-prefix model

A registered recursor with no closed unfolding cannot expose a Pi from a spine
whose major is a free variable. Tuple observations require a constructor at that
major. This tests why indexed proof elimination needs an additional observation
rule rather than merely a proof of the current model's replay hypothesis.
-/
namespace Lean4Lean.VEnv.Strengthening.ConstructorObservation
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
open PureObservation (Definitions)

/-- Whether an observation ends in a Pi after its function demands are removed. -/
def Ob.piTail : Ob → Prop
  | .pi => True
  | .app _ o => o.piTail
  | _ => False

/-- Subsumption cannot create a Pi tail. -/
theorem Ob.Le.piTail (H : Ob.Le o o') : o'.piTail → o.piTail := by
  induction H with
  | refl => exact id
  | app _ _ _ _ _ ih => exact ih
  | field => exact False.elim

/-- Currying demands leaves the terminal head observation unchanged. -/
theorem Ob.piTail_wrap : (Ob.wrap keys o).piTail = o.piTail := by
  induction keys with
  | nil => rfl
  | cons _ _ ih => exact ih

/-- Strip equally many application demands from a subsumption proof. -/
theorem Ob.Le.wrap_parts (H : Ob.Le (Ob.wrap keys o) (Ob.wrap keys' o'))
    (hlen : keys.length = keys'.length) : Ob.Le o o' := by
  induction keys generalizing keys' with
  | nil => cases keys' with
    | nil => exact H
    | cons => cases hlen
  | cons K keys ih => cases keys' with
    | nil => cases hlen
    | cons L keys' => exact ih H.app_parts.2 (Nat.succ.inj hlen)

variable [Params] {D : Definitions}

/-- A registered recursor fixes the major offset of every pattern at its head. -/
theorem recursor_major_offset (hl : recursorData name = some data)
    {r : (SimplePattern.iota name major ctor fields).toPattern.RHS ×
      (SimplePattern.iota name major ctor fields).toPattern.Check}
    (hp : Pat _ r) : major = data.majorOffset := by
  rcases pat_recursor hp with ⟨data', _, hn, hm, hr, _⟩ | ⟨hq, hn, _⟩
  · subst name
    cases Option.some.inj (hl.symm.trans hr)
    exact hm.symm
  · subst name
    rw [recursorData_quot hq] at hl
    cases hl

/-- At its major application, a non-unfolding recursor cannot satisfy a Pi
observation while demanding nothing of the major. -/
theorem Obs.recursor_empty_major (hl : recursorData name = some data)
    (hn : ∀ rhs, ¬ D.unfolds name levels rhs)
    (H : Obs D S (.const name levels) o) :
    ∀ keys, keys.length = data.majorOffset →
      Ob.Le o (Ob.wrap keys (.app [] .pi)) → False := by
  generalize he : VExpr.const name levels = e at H
  induction H with
  | ctor hi hk hg ho =>
    cases he
    intro keys hlen hle
    have hh := hle.piTail (by rw [Ob.piTail_wrap]; trivial)
    simp only [Ob.piTail_wrap, Ob.piTail] at hh
  | ctorTuple ht =>
    cases he
    intro keys hlen hle
    have hh := hle.piTail (by rw [Ob.piTail_wrap]; trivial)
    simp only [Ob.piTail_wrap, Ob.piTail] at hh
  | recursor hp hc hr =>
    cases he
    intro keys hlen hle
    have hm := recursor_major_offset hl hp
    have hrest := hle.wrap_parts (by simp only [spineKeys, List.length_ofFn]; omega)
    have hcover := hrest.app_parts.1
    obtain ⟨_, hf, _⟩ := hcover _ (List.mem_cons_self)
    exact List.not_mem_nil hf
  | delta hd => cases he; exact (hn _ hd).elim
  | sub _ hs ih =>
    intro keys hlen hle
    exact ih he keys hlen (hs.trans hle)
  | var | sort | pi | app | lam | proj => cases he

/-- A free variable in the major position supplies no tuple observation at the
empty valuation, even if all preceding arguments carry arbitrary computation. -/
theorem Obs.recursor_variable_no_pi (hl : recursorData name = some data)
    (hn : ∀ rhs, ¬ D.unfolds name levels rhs) (ha : args.length = data.majorOffset) :
    ¬ Obs D (fun _ _ => False) (.app (mkApps (.const name levels) args) (.bvar i)) .pi := by
  intro H
  obtain ⟨keys, hf, ha'⟩ := H.app_inv
  have hnil : keys = [] := by
    cases keys with
    | nil => rfl
    | cons k keys =>
      obtain ⟨_, hfalse, _⟩ := (ha' k (by simp)).var_inv
      exact hfalse.elim
  subst keys
  obtain ⟨keys, hc, hk⟩ := hf.spine_inv
  exact hc.recursor_empty_major hl hn keys (hk.length_eq.trans ha) .refl

/-- The current mixed model cannot expose a Pi through a variable major at a
registered head that has no closed unfolding in its definition collection. -/
theorem recursor_variable_no_pi (hl : recursorData name = some data)
    (hn : ∀ rhs, ¬ D.unfolds name levels rhs) (ha : args.length = data.majorOffset)
    (hD : ConstructorRigid D) :
    ¬ EtaCompute D (.app (mkApps (.const name levels) args) (.bvar i)) (.forallE A B) := by
  intro H
  exact Obs.recursor_variable_no_pi hl hn ha (H.obs_back hD .pi)

omit [Params] in
/-- The actual constant-equation collection has no Eq.rec unfolding, because
canonical Eq.rec is the head of a stored iota pattern. -/
theorem eqRec_no_stored_unfold {env : VEnv} (henv : env.WF) (heq : env.HasCanonicalEq) :
    ¬ (Definitions.ofEnv env U henv).unfolds ``Eq.rec levels rhs := by
  rintro ⟨df, us, hd, _, _, he, _⟩
  have hshape : ∃ ls, df.lhs = .const ``Eq.rec ls := by
    cases hh : df.lhs <;> simp [hh, instL] at he
    obtain ⟨rfl, _⟩ := he
    exact ⟨_, rfl⟩
  obtain ⟨ls, hl⟩ := hshape
  obtain ⟨doms, hclosed, _, hp⟩ := heq.2.2.2
  exact henv.defeq_head_not_pat hd (by rw [hl]; rfl) hp rfl

omit [Params] in
/-- Canonical Eq computes a cast of a Pi along a free proof of reflexive type
equality. The raw model containing only stored definitions, ordinary guarded
iota, projections, and eta cannot simulate this K computation. Registration and
its major offset are explicit; no claim of a strengthening counterexample is made. -/
theorem canonical_cast_boundary {env : VEnv} (henv : env.WF) (heq : env.HasCanonicalEq)
    (hl : env.recursorRegistry ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hu : u.WF U) (hΓ : OnCtx Γ (env.IsType U))
    (hX : env.HasType U Γ X (.sort u))
    (hq : env.HasType U Γ (.bvar i) (eqApp (.succ u) (.sort u) X X))
    (hpi : env.HasType U Γ (.forallE A B) X) :
    env.IsDefEq U Γ (typeCast u X X (.bvar i) (.forallE A B)) (.forallE A B) X ∧
      ¬ @EtaCompute (henv.params U) (Definitions.ofEnv env U henv)
        (typeCast u X X (.bvar i) (.forallE A B)) (.forallE A B) := by
  letI := henv.params U
  refine ⟨IsDefEq.typeCast_refl henv heq hu hΓ hX hq hpi, ?_⟩
  exact recursor_variable_no_pi (D := Definitions.ofEnv env U henv) hl
    (fun _ => eqRec_no_stored_unfold henv heq)
    (args := [.sort u, X, castMotive u X, .forallE A B, X])
    (by simp [hoff]) ConstructorRigid.ofEnv

end Lean4Lean.VEnv.Strengthening.ConstructorObservation
