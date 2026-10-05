import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceGradedSort
import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceGradedEmpty

/-! Proof irrelevance consumes only the original proposition and proof
children. Their actual certificates force every proof demand to be empty. -/

namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

theorem CodeCert.sortCorrect
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {target : List VExpr} {locals : List Nat} {σ : Subst} {available : Valuation}
    {expression : VExpr} {level : VLevel} {relevant : Bool}
    (correct : SortCorrect env U registry target locals σ available expression (.sort level))
    (flag : Relevant level relevant)
    {profile : Profile n} {footprint : Footprint}
    (certificate : CodeCert env U registry target locals σ expression profile footprint)
    (resources : footprint.Available available) : profile.HasType (.sort relevant) := by
  match certificate with
  | .seed observation _ => exact correct level relevant rfl flag observation resources
  | .union left right =>
    exact (left.sortCorrect correct flag
      (fun i need hm => resources i need (List.mem_append_left _ hm))).union
      (right.sortCorrect correct flag
        (fun i need hm => resources i need (List.mem_append_right _ hm)))
  | .pad source => exact (source.sortCorrect correct flag resources).pad_sort
  | .familyPad source => exact (source.sortCorrect correct flag resources).familyPad
  | .unpad source =>
    simpa only [Profile.down_sort] using (source.sortCorrect correct flag resources).pad_inv
  | .down source =>
    simpa only [Profile.down_sort] using (source.sortCorrect correct flag resources).down
  | .map view source => exact view.mapType_sort (source.sortCorrect correct flag resources)
  | .select source member => exact (source.sortCorrect correct flag resources).singleton_of_mem member
  | .focusMinimal source minimal focusedBound => exact (source.sortCorrect correct flag resources).restrict focusedBound minimal.typed.wf_type
termination_by sizeOf certificate

theorem GradedTransfer.proofIrrel
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {target : List VExpr} {locals : List Nat} {σ τ : Subst} {available : Valuation}
    {left right proposition : VExpr}
    (propositionCorrect : SortCorrect env U registry target locals σ
      available proposition (.sort .zero))
    (original : GradedTransfer env U registry target locals σ τ
      available left left proposition) :
    GradedTransfer env U registry target locals σ τ
      available left right proposition := by
  intro n demand footprint observation resources
  obtain ⟨result⟩ := original observation resources
  have propositionTyped := result.requestedCertificate.sortCorrect propositionCorrect
    (show Relevant .zero false from rfl) result.typeAvailable
  have empty := result.requestedTyped.proof_empty propositionTyped
  change demand = .empty at empty
  subst demand
  exact ⟨GradedTransferResult.empty⟩

theorem GradedJoint.proofIrrel
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered)
    {source : List VExpr} {left right proposition : VExpr}
    (originalProposition : GradedJoint env U registry source proposition proposition (.sort .zero))
    (originalLeft : GradedJoint env U registry source left left proposition)
    (originalRight : GradedJoint env U registry source right right proposition) :
    GradedJoint env U registry source left right proposition := by
  apply GradedJoint.of_transfers henv
  intro target locals σ τ available closed hTarget substitutions fits
  have hp := originalProposition target locals σ τ available closed hTarget substitutions fits
  have hl := originalLeft target locals σ τ available closed hTarget substitutions fits
  have hr := originalRight target locals σ τ available closed hTarget substitutions fits
  exact ⟨GradedTransfer.proofIrrel hp.2.2.1 hl.1,
    GradedTransfer.proofIrrel hp.2.2.1 hr.1⟩

end Lean4Lean.AnchoredSource.Adapted
