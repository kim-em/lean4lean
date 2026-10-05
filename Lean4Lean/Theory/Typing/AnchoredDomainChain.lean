import Lean4Lean.Theory.Typing.AnchoredAdapterViewEmbedding

/-! Finite domain alignment for a source Pi row. Each actual conversion edge
keeps the finite support which types its input; different edges need not share
one support. This is concrete evidence, not an alignment callback. -/
namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles
set_option backward.isDefEq.respectTransparency false

inductive DomainChain (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (Γ : List VExpr) (input : Profile n) : VExpr → VExpr → Type where
  | refl (domain : VExpr) : DomainChain env U registry Γ input domain domain
  | step {left middle right : VExpr} {support : Profile n}
      (path : TypeConversion env U Γ left middle)
      (typed : input.HasType support) (formed : support.HasType (.sort true))
      (related : TypeRelated env U registry Γ left middle support)
      (tail : DomainChain env U registry Γ input middle right) :
      DomainChain env U registry Γ input left right

theorem DomainChain.path (chain : DomainChain env U registry Γ input left right) :
    TypeConversion env U Γ left right := by
  induction chain with
  | refl => exact .refl
  | step path _ _ _ _ ih => exact path.trans ih

noncomputable def DomainChain.mapInput
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (view : ProfileView env U registry Γ input output)
    (chain : DomainChain env U registry Γ input left right) :
    DomainChain env U registry Γ output left right := by
  induction chain with
  | refl => exact .refl _
  | step path typed formed related tail ih =>
    exact .step path (view.mapType_typed typed) (view.mapType_sort formed)
      (view.codeMap henv hscoped related) ih

noncomputable def DomainChain.pad (henv : env.Ordered)
    (chain : DomainChain env U registry Γ (input : Profile n) left right) :
    DomainChain env U registry Γ input.pad left right := by
  induction chain with
  | refl => exact .refl _
  | step path typed formed related tail ih =>
    exact .step path typed.pad formed.pad_sort (related.pad henv) ih

noncomputable def DomainChain.unpad (henv : env.Ordered)
    (chain : DomainChain env U registry Γ (input : Profile n).pad left right) :
    DomainChain env U registry Γ input left right := by
  generalize he : input.pad = padded at chain
  induction chain with
  | refl => exact .refl _
  | step path typed formed related tail ih =>
    subst padded
    exact .step path typed.pad_inv
      (by simpa only [Profile.down_sort] using formed.down)
      (related.down henv) ih

theorem DomainChain.admission (henv : env.Ordered)
    (chain : DomainChain env U registry Γ (input : Profile n) left right)
    (admitted : Admitted env U registry Γ ⟨left, anchor, input⟩ x y) :
    Admitted env U registry Γ ⟨right, anchor, input⟩ x y := by
  induction chain with
  | refl => exact admitted
  | step path typed formed related tail ih =>
    exact ih (admitted.rekey henv path typed formed related)

end Lean4Lean.AnchoredSemantics
