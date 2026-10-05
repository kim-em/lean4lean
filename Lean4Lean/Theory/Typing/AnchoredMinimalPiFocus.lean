import Lean4Lean.Theory.Typing.AnchoredSupportBasis
import Lean4Lean.Theory.Typing.AnchoredDiagonal
import Lean4Lean.Theory.Typing.AnchoredFrame

/-! The Pi case of hereditary support selection. Shrinking its domain does
not retain an arbitrary old row-domain witness: the bridge is rebuilt at
the selected minimal domain. All semantic hypotheses concern the strictly
smaller rank and the concrete anchored relation. -/

namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles

set_option backward.isDefEq.respectTransparency false

def PiWitness.focusMinimal
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {n : Nat}
    (lowerFocus : ∀ Γ left right (value support bound : Profile n),
      Minimal value support → value.HasType support → support ≤ bound →
      TypeRelated env U registry Γ left right bound →
      TypeRelated env U registry Γ left right support)
    (lowerCompose : ∀ Γ left middle right (value support other : Profile n),
      Minimal value support → value.HasType other →
      TypeRelated env U registry Γ left middle support →
      TypeRelated env U registry Γ middle right other →
      TypeRelated env U registry Γ left right support)
    (lowerSymm : ∀ Γ left right (support : Profile n),
      support.WF →
      TypeRelated env U registry Γ left right support →
      TypeRelated env U registry Γ right left support)
    {Γ : List VExpr} {left right A B : VExpr}
    {domain selectedDomain selectedResult result : Profile n}
    {rows : List (Key n × Profile n)} {key : Key n} {output : Atom n}
    (display : PiWitness env U registry (relations env U registry n)
      Γ left right A B domain rows)
    (hrow : (key, result) ∈ rows)
    (minimalDomain : Minimal key.input selectedDomain)
    (minimalResult : Minimal (.singleton output) selectedResult)
    (inputTyped : key.input.HasType selectedDomain)
    (outputTyped : (Profile.singleton output).HasType selectedResult)
    (domainFormation : selectedDomain.HasType (.sort true))
    (domainBound : selectedDomain ≤ domain)
    (resultBound : selectedResult ≤ result) :
    PiWitness env U registry (relations env U registry n)
      Γ left right A B selectedDomain [(key, selectedResult)] := by
  have domainRelated : TypeRelated env U registry display.context
      display.leftDomain display.rightDomain (selectedDomain.rename display.map) :=
    lowerFocus _ _ _ _ _ _ (minimalDomain.rename display.map)
      (Profile.rename_hasType_iff.mpr inputTyped)
      (Profile.rename_le_iff.mpr domainBound) display.domainRelated
  refine {
    display with
    domainRelated := domainRelated
    rowDomains := ?_
    rowBodies := ?_ }
  · intro k r hm
    cases List.mem_singleton.mp hm
    obtain ⟨support, hs, hsort, _, path, link⟩ := display.rowDomains key result hrow
    have reversed := lowerSymm _ _ _ _ hs.wf_type link
    have newLink := lowerCompose _ _ _ _ _ _ _ (minimalDomain.rename display.map) hs
      (TypeRelated.left_diagonal domainRelated) reversed
    refine ⟨selectedDomain.rename display.map,
      Profile.rename_hasType_iff.mpr inputTyped, ?_, Profile.le_refl _, path,
      lowerSymm _ _ _ _ (Profile.rename_wf_iff.mpr inputTyped.wf_type) newLink⟩
    simpa only [Profile.rename_sort] using
      (Profile.rename_hasType_iff (ρ := display.map)).mpr domainFormation
  · intro k r hm Δ ρ future x y admitted
    cases List.mem_singleton.mp hm
    obtain ⟨hl, hr, hc⟩ := display.rowBodies key result hrow Δ ρ future x y admitted
    have hm := minimalResult.rename (display.map.comp ρ)
    have ht := (Profile.rename_hasType_iff (ρ := display.map.comp ρ)).mpr outputTyped
    have hb := (Profile.rename_le_iff (ρ := display.map.comp ρ)).mpr resultBound
    exact ⟨lowerFocus _ _ _ _ _ _ hm ht hb hl,
      lowerFocus _ _ _ _ _ _ hm ht hb hr, lowerFocus _ _ _ _ _ _ hm ht hb hc⟩

end Lean4Lean.AnchoredSemantics
