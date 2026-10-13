import Lean4Lean.Theory.Typing.FullReduction

/-! # Generated prefix syntax preserves unused binders

Generation commutes with raw substitution and renaming. Substituting an arbitrary
syntactic dummy into an unused binder, regenerating, and renaming back recovers the
same program by determinism. This proves scope preservation without assuming that
the dummy has the removed binder's type. It does not lower replay typing checks.
-/
namespace Lean4Lean.InductiveSignature.RecursorData
open VExpr VEnv

/-- Invert a binder insertion in the singleton generator. The lowered
program is generated below syntactically; no smaller-context replay is claimed. -/
theorem singletonUnfolding_liftN_inv {data : RecursorData} {env : VEnv}
    {levels : List VLevel} (henv : env.WF) (hr : RecursorRegistered env data)
    (hlarge : data.largeTarget = true) (hzero : data.sourceLevel levels ≈ .zero)
    (htype : data.recursorType = some recType) (hclosed : recType.Closed)
    (H : data.singletonUnfolding env U levels (args.map (·.liftN n k)) = some program) :
    ∃ lower, data.singletonUnfolding env U levels args = some lower ∧
      program = lower.rename ((Lift.refl.skipN n).consN k) := by
  have existsLower : ∀ n {program},
      data.singletonUnfolding env U levels (args.map (·.liftN n k)) = some program →
      ∃ lower, data.singletonUnfolding env U levels args = some lower := by
    intro n
    induction n with
    | zero => intro program H; exact ⟨program, by simpa using H⟩
    | succ n ih =>
      intro program H
      have hlower := singletonUnfolding_inst (arg := .sort .zero) (k := k)
        henv hr hlarge hzero htype hclosed H
      simp only [List.map_map, Function.comp_def, inst_liftN'] at hlower
      exact ih hlower
  obtain ⟨lower, hlower⟩ := existsLower n H
  refine ⟨lower, hlower, ?_⟩
  have hback := singletonUnfolding_lift' (ρ := (Lift.refl.skipN n).consN k)
    henv hr hlarge hzero htype hclosed hlower
  simp only [lift'_consN_skipN] at hback
  exact Option.some.inj (H.symm.trans hback)

end Lean4Lean.InductiveSignature.RecursorData

namespace Lean4Lean.QuotPrefixUnfolding
open VExpr InductiveSignature.RecursorData

/-- The quotient generator also reflects a binder insertion by a purely
syntactic dummy substitution and deterministic regeneration. -/
theorem generate_liftN_inv {levels : List VLevel}
    (H : generate levels (args.map (·.liftN n k)) = some program) :
    ∃ lower, generate levels args = some lower ∧
      program = lower.rename ((Lift.refl.skipN n).consN k) := by
  have existsLower : ∀ n {program}, generate levels (args.map (·.liftN n k)) = some program →
      ∃ lower, generate levels args = some lower := by
    intro n
    induction n with
    | zero => intro program H; exact ⟨program, by simpa using H⟩
    | succ n ih =>
      intro program H
      have hlower := generate_inst (arg := .sort .zero) (k := k) H
      simp only [List.map_map, Function.comp_def, inst_liftN'] at hlower
      exact ih hlower
  obtain ⟨lower, hlower⟩ := existsLower n H
  refine ⟨lower, hlower, ?_⟩
  have hback := generate_rename (ρ := (Lift.refl.skipN n).consN k) hlower
  simp only [lift'_consN_skipN] at hback
  exact Option.some.inj (H.symm.trans hback)

end Lean4Lean.QuotPrefixUnfolding

namespace Lean4Lean.VEnv.Strengthening
open VExpr InductiveSignature.RecursorData
variable {name : Name} {levels : List VLevel} {args : List VExpr}

/-- A checked singleton prefix whose arguments omit a binder has an output which
omits it too. The returned witness is syntax, not a replay check below. -/
theorem prefixUnfold_liftN_scope (henv : env.WF)
    (H : PrefixUnfold env U registry Γ name levels (args.map (·.liftN n k)) rhs) :
    ∃ lower : VExpr, rhs = lower.liftN n k := by
  cases H with
  | @intro data program _ hr _ hl _ hz hg replay =>
    have hex : ∃ type, data.recursorType = some type := by
      cases hh : data.recursorType with
      | some type => exact ⟨type, rfl⟩
      | none =>
        unfold singletonUnfolding at hg
        split at hg <;> simp [hh] at hg
    obtain ⟨type, htype⟩ := hex
    obtain ⟨lower, _, he⟩ := singletonUnfolding_liftN_inv henv hr hl hz htype
      (hr.recursorType_closed henv htype) hg
    have hscope := (replay.templateScope henv).2.1
    rw [he] at hscope ⊢
    simp only [PrefixUnfolding.rename, List.length_map] at hscope
    exact ⟨lower.rhs, by simpa only [lift'_consN_skipN] using PrefixUnfolding.rename_rhs (ρ := (Lift.refl.skipN n).consN k) hscope⟩

/-- Scope preservation for every quotient prefix, with no additional typing or
inhabitation premise in the smaller context. -/
theorem quotPrefixUnfold_liftN_scope (henv : env.WF)
    (H : QuotPrefixUnfold env U Γ levels (args.map (·.liftN n k)) rhs) :
    ∃ lower : VExpr, rhs = lower.liftN n k := by
  cases H with
  | @intro program _ _ _ hg replay =>
    obtain ⟨lower, _, he⟩ := QuotPrefixUnfolding.generate_liftN_inv hg
    have hscope := (replay.templateScope henv).2.1
    rw [he] at hscope ⊢
    simp only [PrefixUnfolding.rename, List.length_map] at hscope
    exact ⟨lower.rhs, by simpa only [lift'_consN_skipN] using PrefixUnfolding.rename_rhs (ρ := (Lift.refl.skipN n).consN k) hscope⟩

end Lean4Lean.VEnv.Strengthening
