import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceGradedCode

/-! Hereditary function adapters preserve record observations literally.
An actual returned observation can therefore be pruned and lowered to the
original record demand, retaining its finite source resources. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

private inductive RecordAtom : {n : Nat} → Atom n → Prop where
  | record (demand : RecordData (Profile n)) : RecordAtom (n := n + 1) (.record demand)
  | pad {atom : Atom n} : RecordAtom atom → RecordAtom (n := n + 1) (.pad atom)

private theorem RecordAtom.rigid {a b : Atom n}
    (shape : RecordAtom b) (adapter : AtomAdapter env U registry Γ a b) : a = b := by
  induction shape with
  | record demand => cases adapter; rfl
  | pad shape ih =>
    cases adapter with
    | refl => rfl
    | pad child => exact congrArg AtomData.pad (ih child)

private theorem RecordAtom.shift {a : Atom n} (shape : RecordAtom a) :
    AdapterNormal.shiftAtom a = AtomData.pad a := by
  cases shape <;> rfl

private theorem RecordAtom.normal {a : Atom n} (shape : RecordAtom a) :
    AdapterNormal.atom a = a := by
  induction shape with
  | record demand => rfl
  | pad shape ih =>
    change AdapterNormal.shiftAtom (AdapterNormal.atom _) = _
    rw [ih, shape.shift]

private theorem RecordAtom.raise {n N : Nat} (bound : n ≤ N) {a : Atom n}
    (shape : RecordAtom a) : RecordAtom (raiseAtom N bound a) := by
  induction N with
  | zero =>
    have equal : n = 0 := by omega
    subst n
    simpa only [raiseAtom_self] using shape
  | succ N ih =>
    by_cases equal : n = N + 1
    · subst n
      simpa only [raiseAtom_self] using shape
    · have small : n ≤ N := by omega
      rw [raiseAtom_step small]
      exact .pad (ih small)

theorem Obs.record_of_adapter
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) {target : List VExpr} {locals : List Nat}
    {σ : Subst} {expression : VExpr} {available : Valuation}
    {demand : RecordData (Profile n)} {N : Nat} (bound : n + 1 ≤ N)
    {raw : Profile N} {footprint : Footprint}
    (observation : Obs env U registry target locals σ expression raw footprint)
    (adapter : NormalProfileAdapter env U registry target raw
      (raiseProfile N bound (Profile.singleton (n := n + 1) (.record demand))))
    (resources : footprint.Available available) (closed : available.AtomClosed) :
    ∃ required, Nonempty (Obs env U registry target locals σ expression
      (Profile.singleton (n := n + 1) (.record demand)) required) ∧
      required.Available available := by
  let atom := raiseAtom N bound (AtomData.record demand)
  have shape : RecordAtom atom := (RecordAtom.record demand).raise bound
  have canonical : AdapterNormal.profile
      (raiseProfile N bound (Profile.singleton (n := n + 1) (.record demand))) =
      Profile.singleton atom := by
    rw [raiseProfile_singleton]
    change [AdapterNormal.atom atom] = [atom]
    rw [shape.normal]
  have adapter' : ProfileAdapter env U registry target (AdapterNormal.profile raw)
      (Profile.singleton atom) := by
    change ProfileAdapter env U registry target _ _ at adapter
    rwa [canonical] at adapter
  obtain ⟨origin, member, ⟨entry⟩⟩ := adapter'.origin (List.mem_singleton_self _)
  have equal := shape.rigid entry
  subst origin
  obtain ⟨normalizedFootprint, ⟨normalized⟩, normalization⟩ := observation.normalize henv
  obtain ⟨selected⟩ := normalized.atom member
  have raised : Obs env U registry target locals σ expression
      (raiseProfile N bound (Profile.singleton (n := n + 1) (.record demand)))
      selected.footprint := by
    simpa only [raiseProfile_singleton] using selected.observation
  exact ⟨selected.footprint, ⟨raised.lower bound⟩,
    (selected.atomizes.trans normalization).available_closed resources closed⟩

end Lean4Lean.AnchoredSource.Adapted
