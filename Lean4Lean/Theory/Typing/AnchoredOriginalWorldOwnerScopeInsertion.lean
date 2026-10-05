import Lean4Lean.Theory.Typing.AnchoredOriginalGeneratedResourceCaps

/-! Insert a common scope beneath the exact retained owner prefix. Prefix
values and resource predicates remain unchanged; the new tail is supplied by
the actual outer scope. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

/-- The two concrete context legs commute without typing a new substitution. -/
theorem ownerScopeInsertion
    (front : Ctx.Lift' (.skipN .refl depth) common scope)
    (insertion : Ctx.Lift' ρ common next) :
    ∃ expanded, Ctx.Lift' (.consN ρ depth) scope expanded ∧
      Ctx.Lift' (.skipN .refl depth) next expanded := by
  induction depth generalizing scope with
  | zero =>
    cases front
    exact ⟨next, insertion, .refl⟩
  | succ depth ih =>
    cases front with
    | skip front =>
      obtain ⟨expanded, across, over⟩ := ih front
      exact ⟨_, across.cons, over.skip⟩

def retainedPrefix (depth : Nat) (old next : Nat → α) : Nat → α :=
  match depth with
  | 0 => next
  | depth + 1 => fun
    | 0 => old 0
    | index + 1 => retainedPrefix depth (fun i => old (i + 1)) next index

theorem retainedPrefix_tail (depth : Nat) (old next : Nat → α) :
    ∀ i, retainedPrefix depth old next (i + depth) = next i := by
  induction depth generalizing old with
  | zero => intro i; rfl
  | succ depth ih =>
    intro i
    exact ih (fun i => old (i + 1)) i

theorem retainedPrefix_pullback (ρ : Lift) (depth : Nat) (old next : Nat → α)
    (agrees : ∀ i, next (ρ.liftVar i) = old (i + depth)) :
    ∀ i, retainedPrefix depth old next ((ρ.consN depth).liftVar i) = old i := by
  induction depth generalizing old with
  | zero => exact agrees
  | succ depth ih =>
    intro i
    cases i with
    | zero => rfl
    | succ i => exact ih (fun i => old (i + 1)) agrees i

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
