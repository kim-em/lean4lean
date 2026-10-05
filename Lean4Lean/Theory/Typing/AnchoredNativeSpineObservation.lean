import Lean4Lean.Theory.Typing.AnchoredNativeSpineDemand

/-! Replay the retained actual application frames after constructing the
bare native observer. Each application uses its stored original argument
observation and admission; literal grade lowering restores the requested
terminal atom. Original type conversions change no source expression. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

theorem NativeSpineDemandPath.observe
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {source target : List VExpr} {locals : List Nat} {σ : Subst} {available : Valuation}
    {name : Name} {levels : List VLevel} {expression assigned : VExpr}
    {atom : Atom n} {root : Atom N}
    (path : NativeSpineDemandPath sourceEnv env U registry source target locals σ available
      name levels expression assigned atom root)
    {headFootprint : Footprint}
    (head : Obs env U registry target locals σ (.const name levels) (.singleton root) headFootprint)
    (headResources : headFootprint.Available available) :
    ∃ footprint, Nonempty (Obs env U registry target locals σ expression (.singleton atom) footprint) ∧
      footprint.Available available := by
  induction path with
  | constant => exact ⟨headFootprint, ⟨head⟩, headResources⟩
  | application frame function ih =>
    obtain ⟨footprint, ⟨fn⟩, resources⟩ := ih head
    have application := Obs.app fn frame.argumentObservation (.refl _) frame.guard.anchor
    refine ⟨footprint ++ (frame.seed.footprint ++ frame.collected.argumentFootprint), ⟨?_⟩,
      fun i need member => (List.mem_append.mp member).elim
        (resources i need) (frame.argumentResources i need)⟩
    apply Obs.lower (Nat.le_trans (Nat.le_max_left _ _) frame.collected.bound)
    simpa only [raiseProfile_singleton, SeededApplicationCodeInput.output] using application
  | conversion _ _ ih => exact ih head

end Lean4Lean.AnchoredSource.Adapted
