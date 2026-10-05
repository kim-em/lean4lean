import Lean4Lean.Theory.Typing.AnchoredSortableCert

/-! A sort-grade promotion beneath eta's application body is not an existing
function-output adapter. The hereditary eta factor must retain that code
action explicitly rather than reusing the legacy reversible trace. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics

 theorem no_sortPad_atomAdapter
    {n : Nat} {flag other : Bool} :
    ¬ Nonempty (AtomAdapter env U registry target (n := n + 2)
      (.pad (.sort flag)) (.sort other)) := by
  intro ⟨adapter⟩
  cases adapter

 theorem no_sortPad_functionAdapter
    {n : Nat} {flag other : Bool} {left right : Key (n + 2)} :
    ¬ Nonempty (NormalAtomAdapter env U registry target (n := n + 3)
      (.fn left (.pad (.sort flag))) (.fn right (.sort other))) := by
  intro ⟨adapter⟩
  change AtomAdapter env U registry target (n := n + 3)
    (.fn (AdapterNormal.key left) (.pad (.sort flag)))
    (.fn (AdapterNormal.key right) (.sort other)) at adapter
  obtain ⟨key, output, equality, _, result⟩ := adapter.fn_inv
  cases equality
  exact no_sortPad_atomAdapter result

/-- The same promotion can occur in eta's bound-variable argument. Existing
key programs expose only ordinary contravariant argument adapters. -/
theorem no_sortPad_inputAdapter
    {n : Nat} {flag other : Bool} :
    ¬ Nonempty (ProfileAdapter env U registry target (n := n + 2)
      (.singleton (.pad (.sort flag))) (.singleton (.sort other))) := by
  intro ⟨adapter⟩
  obtain ⟨original, member, result⟩ := adapter.origin (List.mem_singleton_self _)
  cases List.mem_singleton.mp member
  exact no_sortPad_atomAdapter result

theorem no_sortPad_keyProgram
    {n : Nat} {flag other : Bool}
    {old new : Key (n + 2)}
    (oldInput : old.input = .singleton (.sort other))
    (newInput : new.input = .singleton (.pad (.sort flag))) :
    ¬ Nonempty (KeyProgram env U registry target old new) := by
  intro ⟨program⟩
  have arguments := program.arguments
  rw [oldInput, newInput] at arguments
  exact no_sortPad_inputAdapter ⟨arguments⟩

/-- The richer computational grammar really admits the body promotion,
with exactly the original source footprint. -/
noncomputable def SortableObs.promoteSort
    (source : SortableObs env U registry target locals σ expression (Profile.sort (n := n) flag) footprint)
    (formed : (Profile.sort (n := n) flag).HasType (.sort relevant)) :
    SortableObs env U registry target locals σ expression (Profile.sort (n := n + 1) flag) footprint :=
  .code relevant (.sortPad (.observe source formed))

end Lean4Lean.AnchoredSource.Adapted
