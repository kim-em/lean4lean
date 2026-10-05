import Lean4Lean.Theory.Typing.AnchoredSourceFundamental

/-! A finite closure of the available source demands under literal singleton
selection. New entries retain the original actual-type certificate; no code
profile restriction or arbitrary function-input change is used. -/

namespace Lean4Lean.AnchoredSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

def Need.singletons (need : Need) : List Need :=
  need.profile.atoms.map fun atom => ⟨need.rank, .singleton atom⟩

def Valuation.atomize (available : Valuation) : Valuation :=
  fun index => available index ++ (available index).flatMap Need.singletons

theorem Valuation.mem_atomize (h : need ∈ available index) :
    need ∈ Valuation.atomize available index :=
  List.mem_append_left _ h

theorem Footprint.Available.atomize
    (h : Footprint.Available required available) :
    Footprint.Available required (Valuation.atomize available) :=
  fun index need hm => Valuation.mem_atomize (h index need hm)

/-- Output selection retains a whole child or one literal variable atom. -/
def Footprint.Atomizes (selected original : Footprint) : Prop :=
  ∀ index need, (index, need) ∈ selected →
    ∃ old, (index, old) ∈ original ∧ (need = old ∨ need ∈ old.singletons)

theorem Footprint.Atomizes.available
    {selected original : Footprint} {available : Valuation}
    (selection : Footprint.Atomizes selected original)
    (resources : Footprint.Available original available) :
    Footprint.Available selected (Valuation.atomize available) := by
  intro index need hm
  obtain ⟨old, hold, same | atom⟩ := selection index need hm
  · subst need
    exact Valuation.mem_atomize (resources index old hold)
  · apply List.mem_append_right
    exact List.mem_flatMap.mpr ⟨old, resources index old hold, atom⟩

/-- Atomization preserves the actual full lookup type and its source
certificate. Only the computational value profile is selected literally. -/
theorem Fits.atomize
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {source target : List VExpr} {locals : List Nat} {left right : Subst}
    {available : Valuation}
    (fits : Fits env U registry source target locals left right available) :
    Fits env U registry source target locals left right (Valuation.atomize available) := by
  constructor
  intro index need hm sourceType lookup
  rcases List.mem_append.mp hm with old | selected
  · obtain ⟨entry⟩ := fits.entry index need old sourceType lookup
    exact ⟨{ entry with available := entry.available.atomize }⟩
  · obtain ⟨original, horiginal, hselected⟩ := List.mem_flatMap.mp selected
    obtain ⟨atom, hatom, heq⟩ := List.mem_map.mp hselected
    subst need
    obtain ⟨entry⟩ := fits.entry index original horiginal sourceType lookup
    exact ⟨{
      support := entry.support
      footprint := entry.footprint
      certificate := entry.certificate
      available := entry.available.atomize
      typed := entry.typed.singleton_of_mem hatom
      related := entry.related.singleton_of_mem hatom }⟩

end Lean4Lean.AnchoredSource
