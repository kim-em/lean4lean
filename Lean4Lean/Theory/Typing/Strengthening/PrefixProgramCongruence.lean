import Lean4Lean.Theory.Typing.Strengthening.PrefixProgramJoins
import Lean4Lean.Theory.Typing.PrefixUnfolding.Substitution
import Lean4Lean.Theory.Inductive.RecursiveShapeCorrespondence

/-! # Direct congruence of generated prefix programs

At each fixed arity, generate a program at fresh variables and substitute the
supplied arguments into its entire RHS. The resulting syntax is exactly the
generated program, including its lambda domains. The fresh template needs no
occurrence check or typing. Consequently any weakening-stable congruence
relation on arguments relates the entire generated outputs directly.
-/
namespace Lean4Lean.VEnv.Strengthening.PureObservation
open _root_.Lean4Lean _root_.Lean4Lean.VExpr InductiveSignature
variable {env : VEnv} {data : RecursorData}

/-- Simultaneous substitution commutes with a generated singleton RHS, without
requiring an unfolding check at either argument list. -/
theorem singleton_program_instOuter
    (henv : env.WF) (hr : RecursorRegistered env data)
    (hlarge : data.largeTarget = true) (hz : data.sourceLevel levels ≈ .zero)
    (hg : data.singletonUnfolding env U levels args = some program)
    (supplied : List VExpr) :
    ∃ program', data.singletonUnfolding env U levels
      (args.map (·.instOuter supplied)) = some program' ∧
      program'.rhs = program.rhs.instOuter supplied := by
  obtain ⟨type, htype⟩ : ∃ type, data.recursorType = some type := by
    cases hh : data.recursorType with
    | some type => exact ⟨type, rfl⟩
    | none =>
      unfold RecursorData.singletonUnfolding at hg
      split at hg <;> simp [hh] at hg
  induction supplied generalizing args program with
  | nil => exact ⟨program, by simpa using hg, rfl⟩
  | cons a supplied ih =>
    have hs := RecursorData.singletonUnfolding_inst henv hr hlarge hz htype
      (hr.recursorType_closed henv htype) hg (arg := a) (k := supplied.length)
    obtain ⟨program', hg', he⟩ := ih hs
    refine ⟨program', ?_, ?_⟩
    · simpa only [instOuter_cons, List.map_map, Function.comp_def] using hg'
    · rw [he, RecursorData.PrefixUnfolding.rhs_instN _
        (ClosedSingleton.generated_template_closed henv hr hlarge hz hg), instOuter_cons]

/-- The primitive quotient generator has the same exact substitution law. -/
theorem quotient_program_instOuter
    (hg : QuotPrefixUnfolding.generate levels args = some program)
    (supplied : List VExpr) :
    ∃ program', QuotPrefixUnfolding.generate levels
      (args.map (·.instOuter supplied)) = some program' ∧
      program'.rhs = program.rhs.instOuter supplied := by
  induction supplied generalizing args program with
  | nil => exact ⟨program, by simpa using hg, rfl⟩
  | cons a supplied ih =>
    have hs := QuotPrefixUnfolding.generate_inst hg (arg := a) (k := supplied.length)
    obtain ⟨program', hg', he⟩ := ih hs
    refine ⟨program', ?_, ?_⟩
    · simpa only [instOuter_cons, List.map_map, Function.comp_def] using hg'
    · rw [he, RecursorData.PrefixUnfolding.rhs_instN _
        (ClosedQuot.generated_template_closed hg), instOuter_cons]

/-- A fixed-arity fresh-variable template specializes literally to both
singleton programs. No equation or check of that template is asserted. -/
theorem singleton_substitution_template
    (henv : env.WF) (hr : RecursorRegistered env data)
    (hlarge : data.largeTarget = true) (hz : data.sourceLevel levels ≈ .zero)
    (hg1 : data.singletonUnfolding env U levels args1 = some program1)
    (hg2 : data.singletonUnfolding env U levels args2 = some program2)
    (hlen : args1.length = args2.length) :
    ∃ template : VExpr, program1.rhs = template.instOuter args1 ∧
      program2.rhs = template.instOuter args2 := by
  obtain ⟨fresh, hf⟩ := RecursorData.singletonUnfolding_sameArity hg1
    (args' := vars args1.length 0) (by simp [vars])
  obtain ⟨p1, h1, e1⟩ := singleton_program_instOuter henv hr hlarge hz hf args1
  obtain ⟨p2, h2, e2⟩ := singleton_program_instOuter henv hr hlarge hz hf args2
  rw [vars_map_instOuter] at h1
  rw [hlen, vars_map_instOuter] at h2
  cases Option.some.inj (hg1.symm.trans h1)
  cases Option.some.inj (hg2.symm.trans h2)
  exact ⟨fresh.rhs, e1, e2⟩

/-- Quotient programs at the same arity share an exact substitution template. -/
theorem quotient_substitution_template
    (hg1 : QuotPrefixUnfolding.generate levels args1 = some program1)
    (hg2 : QuotPrefixUnfolding.generate levels args2 = some program2)
    (hlen : args1.length = args2.length) :
    ∃ template : VExpr, program1.rhs = template.instOuter args1 ∧
      program2.rhs = template.instOuter args2 := by
  obtain ⟨fresh, hf⟩ := QuotPrefixUnfolding.generate_sameArity hg1
    (args' := vars args1.length 0) (by simp [vars])
  obtain ⟨p1, h1, e1⟩ := quotient_program_instOuter hf args1
  obtain ⟨p2, h2, e2⟩ := quotient_program_instOuter hf args2
  rw [vars_map_instOuter] at h1
  rw [hlen, vars_map_instOuter] at h2
  cases Option.some.inj (hg1.symm.trans h1)
  cases Option.some.inj (hg2.symm.trans h2)
  exact ⟨fresh.rhs, e1, e2⟩

open Params
variable [Params] {R : List VExpr → VExpr → VExpr → Prop}

/-- A congruence relation on supplied singleton arguments relates the full
checked generated RHSs, including all remaining lambda domains. -/
theorem singleton_program_congr (I : CongrRel R)
    (H1 : PrefixUnfold Params.env univs recursorData Γ1 name levels args1 rhs1)
    (H2 : PrefixUnfold Params.env univs recursorData Γ2 name levels args2 rhs2)
    (HA : List.Forall₂ (R Γ) args1 args2) : R Γ rhs1 rhs2 := by
  cases H1 with
  | intro hlookup hr hname hlarge hw hz hg hc =>
    cases H2 with
    | intro hlookup' hr' hname' hlarge' hw' hz' hg' hc' =>
      cases Option.some.inj (hlookup.symm.trans hlookup')
      obtain ⟨template, e1, e2⟩ := singleton_substitution_template henv hr hlarge hz
        hg hg' (Lean4Lean.List.Forall₂.length_eq HA)
      rw [e1, e2, ← instantiateParams_eq_instOuter, ← instantiateParams_eq_instOuter]
      exact I.instantiateParams_args HA

/-- Full quotient RHSs are likewise congruent along related supplied arguments. -/
theorem quotient_program_congr (I : CongrRel R)
    (H1 : QuotPrefixUnfold Params.env univs Γ1 levels args1 rhs1)
    (H2 : QuotPrefixUnfold Params.env univs Γ2 levels args2 rhs2)
    (HA : List.Forall₂ (R Γ) args1 args2) : R Γ rhs1 rhs2 := by
  cases H1 with
  | intro hr hw hz hg hc =>
    cases H2 with
    | intro hr' hw' hz' hg' hc' =>
      obtain ⟨template, e1, e2⟩ := quotient_substitution_template hg hg'
        (Lean4Lean.List.Forall₂.length_eq HA)
      rw [e1, e2, ← instantiateParams_eq_instOuter, ← instantiateParams_eq_instOuter]
      exact I.instantiateParams_args HA

/-- Re-check a singleton prefix and relate its entire output directly. The
typed argument interface is used only for replay of the occurrence check. -/
theorem singleton_prefix_congr (I : CongrRel R) (J : ArgRel R)
    (hΓ : OnCtx Γ (Params.env.IsType univs))
    (H : PrefixUnfold Params.env univs recursorData Γ name levels args rhs)
    (HA : List.Forall₂ (R Γ) args args') :
    ∃ rhs', PrefixUnfold Params.env univs recursorData Γ name levels args' rhs' ∧
      R Γ rhs rhs' := by
  obtain ⟨rhs', H', _⟩ := H.congr_rel J hΓ HA
  exact ⟨rhs', H', singleton_program_congr I H H' HA⟩

/-- Re-check a quotient prefix with a direct relation on its entire output. -/
theorem quotient_prefix_congr (I : CongrRel R) (J : ArgRel R)
    (hΓ : OnCtx Γ (Params.env.IsType univs))
    (H : QuotPrefixUnfold Params.env univs Γ levels args rhs)
    (HA : List.Forall₂ (R Γ) args args') :
    ∃ rhs', QuotPrefixUnfold Params.env univs Γ levels args' rhs' ∧ R Γ rhs rhs' := by
  obtain ⟨rhs', H', _⟩ := H.congr_rel J hΓ HA
  exact ⟨rhs', H', quotient_program_congr I H H' HA⟩

end Lean4Lean.VEnv.Strengthening.PureObservation
