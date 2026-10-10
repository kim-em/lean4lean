import Lean4Lean.Theory.Typing.PatsIota

namespace Lean4Lean
namespace VEnv

open VExpr

/-!
# Non-overlap of the registered ι rules

The syntactic facts about `env.pats` that the confluence engine's `Params`
(`Theory/Typing/ChurchRosser.lean`) asks of its pattern relation: every registered pattern is
a `SimplePattern.iota` redex (`WF.pat_simple`), two registered redexes that intersect agree
(`WF.pat_uniq`), and a redex has no nested application subpattern (`WF.pat_app_l`,
`WF.pat_app_l_uniq`, `WF.pat_app_uniq`). Their engine is the population invariant
`VEnv.PatsIota`: every registered pattern is a `SimplePattern.iota` redex whose recursor head
is a registered `RecHeaded` constant of a spine arity fixed by the recursor name, whose
constructor is a registered `CtorHeaded` constant, and whose reduct is determined by the
pattern. The invariant comes from `VInductDecl.WF` and the stage lemmas of `addInduct`.

PR #43's `toParams`/`DefEqsAsPats`/`inductParams`/`crDefEq_of_induct` (the small-environment
`Params` instance, for environments without definitions or the quotient) are superseded by
`VEnv.WF.church_rosser` (`Theory/Typing/Confluence/WFParams.lean`), the instance for every
well-formed environment with canonical `Eq`; the lemmas below feed its pattern table
(`ConcretePattern`, `Theory/Typing/Confluence/Patterns.lean`).
-/

/-! ### Combinatorics of ι redexes -/

/-- The only application subpattern of an ι redex is its top-level one: the recursor
spine applied to the constructor spine. -/
theorem app_subpattern_iota' {r m c n a b}
    (hs : Subpattern (.app a b) ((SimplePattern.iota r m c n).toPattern)) :
    a = (Pattern.const r).varN m ∧ b = (Pattern.const c).varN n := by
  simp only [SimplePattern.toPattern] at hs
  cases hs with
  | refl => exact ⟨rfl, rfl⟩
  | appL h => exact absurd h Pattern.not_app_subpattern_varN_const
  | appR h => exact absurd h Pattern.not_app_subpattern_varN_const

/-- The only application subpattern of an ι redex is its top-level one, whose left
factor is the recursor spine. -/
theorem app_subpattern_iota {r m c n a b}
    (hs : Subpattern (.app a b) ((SimplePattern.iota r m c n).toPattern)) :
    a = (Pattern.const r).varN m :=
  (app_subpattern_iota' hs).1

/-- An application pattern does not intersect a constant. -/
theorem _root_.Lean4Lean.Pattern.inter_app_const {f a : Pattern} {c : Name} :
    (Pattern.app f a).inter (.const c) = none := by
  simp [Pattern.inter]

/-- An application pattern intersects a variable pattern only through its function
part. -/
theorem _root_.Lean4Lean.Pattern.inter_app_var {f a f' q : Pattern}
    (h : (Pattern.app f a).inter (.var f') = some q) :
    ∃ g, f.inter f' = some g ∧ q = .app g a := by
  cases hf : f.inter f' with
  | none => simp [Pattern.inter, hf] at h
  | some g => simp [Pattern.inter, hf] at h; exact ⟨g, rfl, h.symm⟩

/-- Two application patterns intersect componentwise. -/
theorem _root_.Lean4Lean.Pattern.inter_app_app {f a f' a' q : Pattern}
    (h : (Pattern.app f a).inter (.app f' a') = some q) :
    ∃ g b, f.inter f' = some g ∧ a.inter a' = some b ∧ q = .app g b := by
  cases hf : f.inter f' with
  | none => simp [Pattern.inter, hf] at h
  | some g =>
    cases ha : a.inter a' with
    | none => simp [Pattern.inter, hf, ha] at h
    | some b => simp [Pattern.inter, hf, ha] at h; exact ⟨g, b, rfl, rfl, h.symm⟩

/-! ### The discharged `Params` side conditions -/

/-- `Params.pat_simple` for `env.pats`: every registered pattern is a `SimplePattern`. -/
theorem WF.pat_simple {env : VEnv} (H : env.WF) {p rr} (hp : env.pats p rr) :
    ∃ sp : SimplePattern, p = sp.toPattern := by
  obtain ⟨recN, M, ctorN, N, _, hform, _⟩ := H.patsIota.shape hp
  exact ⟨.iota recN M ctorN N, hform⟩

/-- `Params.pat_uniq` for `env.pats`: if a subpattern `p₃` of a registered redex `p₁`
intersects a registered redex `p₂`, then `p₁ = p₂ = p₃` and the reducts agree. The
intersection forces the recursor spines to agree: at the top (`refl`) both spines
match and `functional` closes; inside the recursor spine (`appL`) the arity would drop
below `arity`; inside the constructor spine (`appR`) a recursor would be a
constructor (`rec_ne_ctor`). -/
theorem WF.pat_uniq {env : VEnv} (H : env.WF) {p₁ p₂ p₃ p₄ : Pattern}
    {r : p₁.RHS × p₁.Check} {r' : p₂.RHS × p₂.Check}
    (h1 : env.pats p₁ r) (h2 : env.pats p₂ r') (hs : Subpattern p₃ p₁)
    (hi : p₂.inter p₃ = some p₄) : p₁ = p₂ ∧ p₂ = p₃ ∧ HEq r r' := by
  have HI := H.patsIota
  obtain ⟨R₁, M₁, C₁, N₁, c₁, rfl, -, -⟩ := HI.shape h1
  obtain ⟨R₂, M₂, C₂, N₂, c₂, rfl, -, -⟩ := HI.shape h2
  simp only [SimplePattern.toPattern] at hs
  cases hs with
  | refl =>
    simp only [SimplePattern.toPattern] at hi
    obtain ⟨g, b, hg, hb, -⟩ := Pattern.inter_app_app hi
    obtain ⟨rfl, rfl, -⟩ := Pattern.varN_const_inter hg
    obtain ⟨rfl, rfl, -⟩ := Pattern.varN_const_inter hb
    exact ⟨rfl, rfl, heq_of_eq (HI.functional h1 h2)⟩
  | appL hs' =>
    obtain ⟨i, hi', rfl⟩ := Pattern.subpattern_varN_const hs'
    cases i with
    | zero => simp [SimplePattern.toPattern, Pattern.varN, Pattern.inter_app_const] at hi
    | succ i =>
      simp only [SimplePattern.toPattern, Pattern.varN] at hi
      obtain ⟨g, hg, -⟩ := Pattern.inter_app_var hi
      obtain ⟨rfl, rfl, -⟩ := Pattern.varN_const_inter hg
      have := HI.arity h1 h2
      omega
  | appR hs' =>
    obtain ⟨i, hi', rfl⟩ := Pattern.subpattern_varN_const hs'
    cases i with
    | zero => simp [SimplePattern.toPattern, Pattern.varN, Pattern.inter_app_const] at hi
    | succ i =>
      simp only [SimplePattern.toPattern, Pattern.varN] at hi
      obtain ⟨g, hg, -⟩ := Pattern.inter_app_var hi
      obtain ⟨rfl, -, -⟩ := Pattern.varN_const_inter hg
      exact absurd rfl (HI.rec_ne_ctor h2 h1)

/-- `Params.pat_app_l` for `env.pats`: the left factor of an ι redex's application
subpattern (the recursor spine) has no application subpattern of its own. -/
theorem WF.pat_app_l {env : VEnv} (H : env.WF) {p p₁ p₂ p₃ p₄ rr} (hp : env.pats p rr)
    (hs : Subpattern (.app p₁ p₂) p) : ¬ Subpattern (.app p₃ p₄) p₁ := by
  obtain ⟨recN, M, ctorN, N, _, rfl, _⟩ := H.patsIota.shape hp
  rw [app_subpattern_iota hs]
  exact Pattern.not_app_subpattern_varN_const

/-- `Params.pat_app_l_uniq` for `env.pats`: a variable-argument slot of one ι redex's
recursor spine never intersects another ι redex's recursor spine, since the recursor
name fixes the spine arity (`PatsIota.arity`). -/
theorem WF.pat_app_l_uniq {env : VEnv} (H : env.WF) {p r p' r' p₁ p₂ p₁' p₂' p₃}
    (hp : env.pats p r) (hp' : env.pats p' r')
    (hs : Subpattern (.app p₁ p₂) p) (hs' : Subpattern (.app p₁' p₂') p')
    (hv : Subpattern (.var p₃) p₁) : p₁'.inter p₃ = none := by
  have HI := H.patsIota
  obtain ⟨recN, M, ctorN, N, c, rfl, hc⟩ := HI.shape hp
  obtain ⟨recN', M', ctorN', N', c', rfl, hc'⟩ := HI.shape hp'
  have e1 : p₁ = (Pattern.const recN).varN M := app_subpattern_iota hs
  have e1' : p₁' = (Pattern.const recN').varN M' := app_subpattern_iota hs'
  subst e1 e1'
  obtain ⟨k, hk, hkk⟩ := Pattern.subpattern_varN_const hv
  cases k with
  | zero => simp [Pattern.varN] at hkk
  | succ i =>
    simp only [Pattern.varN] at hkk
    injection hkk with hkk; subst hkk
    cases hinter : ((Pattern.const recN').varN M').inter ((Pattern.const recN).varN i) with
    | none => rfl
    | some r₄ =>
      exfalso
      obtain ⟨hrr, hMi, _⟩ := Pattern.varN_const_inter hinter
      subst hrr
      have hMM : M = M' := HI.arity hp hp'
      omega

/-- `Params.pat_app_uniq` for `env.pats`: a subpattern of one ι redex's recursor spine
never intersects a subpattern of another ι redex's constructor spine, since a recursor
is never a constructor (`PatsIota.rec_ne_ctor`). -/
theorem WF.pat_app_uniq {env : VEnv} (H : env.WF) {p r p' r' p₁ p₂ p₁' p₂' p₃ p₃'}
    (hp : env.pats p r) (hp' : env.pats p' r')
    (hs : Subpattern (.app p₁ p₂) p) (hs' : Subpattern (.app p₁' p₂') p')
    (h3 : Subpattern p₃ p₁) (h3' : Subpattern p₃' p₂') : p₃.inter p₃' = none := by
  have HI := H.patsIota
  obtain ⟨R, M, C, N, c, rfl, -, -⟩ := HI.shape hp
  obtain ⟨R', M', C', N', c', rfl, -, -⟩ := HI.shape hp'
  obtain ⟨rfl, -⟩ := app_subpattern_iota' hs
  obtain ⟨-, rfl⟩ := app_subpattern_iota' hs'
  obtain ⟨i, -, rfl⟩ := Pattern.subpattern_varN_const h3
  obtain ⟨j, -, rfl⟩ := Pattern.subpattern_varN_const h3'
  cases hinter : ((Pattern.const R).varN i).inter ((Pattern.const C').varN j) with
  | none => rfl
  | some q =>
    obtain ⟨rfl, -, -⟩ := Pattern.varN_const_inter hinter
    exact absurd rfl (HI.rec_ne_ctor hp hp')

end VEnv
end Lean4Lean
