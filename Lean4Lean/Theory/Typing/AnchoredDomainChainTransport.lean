import Lean4Lean.Theory.Typing.AnchoredDomainChain

/-! Replay a finite domain chain without identifying the supports carried
by its different edges. The destination certificate supplies the final
support; intermediate conversions retain their own checked support. -/
namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles
set_option backward.isDefEq.respectTransparency false

noncomputable def DomainChain.trans
    (first : DomainChain env U registry Γ input left middle)
    (second : DomainChain env U registry Γ input middle right) :
    DomainChain env U registry Γ input left right := by
  induction first with
  | refl => exact second
  | step path typed formed related tail ih =>
    exact .step path typed formed related (ih second)

noncomputable def DomainChain.symm (henv : env.Ordered)
    (chain : DomainChain env U registry Γ input left right) :
    DomainChain env U registry Γ input right left := by
  induction chain with
  | refl => exact .refl _
  | step path typed formed related tail ih =>
    exact ih.trans (.step path.symm typed formed (related.symm henv typed.wf_type) (.refl _))

/-- The output is supported by the actual destination certificate. No
single support is asserted for all intermediate domain conversions. -/
theorem DomainChain.related
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) {input initial final : Profile n}
    (chain : DomainChain env U registry Γ input leftType rightType)
    (typed : input.HasType final)
    (code : TypeRelated env U registry Γ rightType rightType final)
    (value : Related env U registry Γ left right leftType input initial) :
    Related env U registry Γ left right rightType input final := by
  induction chain generalizing initial with
  | refl => exact value.retag henv typed code
  | step path edgeTyped formed related tail ih =>
    exact ih code (value.convert henv edgeTyped related)

noncomputable def DomainChain.future
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) {Γ Δ : List VExpr} {ρ : Lift}
    (W : FutureInsertion env U Γ Δ ρ)
    {input : Profile n} (chain : DomainChain env U registry Γ input left right) :
    DomainChain env U registry Δ (input.rename ρ) (left.lift' ρ) (right.lift' ρ) := by
  induction chain with
  | refl => exact .refl _
  | step path typed formed related tail ih =>
    exact .step (path.weak' henv W.weakening) (Profile.rename_hasType_iff.mpr typed)
      (by simpa only [Profile.rename_sort] using
        (Profile.rename_hasType_iff (ρ := ρ)).mpr formed)
      (related.future henv W) ih

end Lean4Lean.AnchoredSemantics
