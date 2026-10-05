import Lean4Lean.Theory.Typing.AnchoredBoundedConversion

/-! Proof irrelevance consumes only the original proposition and proof
children. Their actual certificates force every proof demand to be empty. -/

namespace Lean4Lean.AnchoredSource.Adapted.Staged
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false
variable {current : Name → Bool} {fuel : Nat}

theorem CodeCert.sortCorrect
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {target : List VExpr} {locals : List Nat} {σ : Subst} {available : Valuation}
    {expression : VExpr} {level : VLevel} {relevant : Bool}
    (correct : SortCorrect current fuel env U registry target locals σ available expression (.sort level))
    (flag : Relevant level relevant)
    {profile : Profile n} {footprint : Footprint}
    (certificate : CodeCert env U registry target locals σ expression profile footprint)
    (bound : certificate.nativeDepth current ≤ fuel)
    (resources : footprint.Available available) : profile.HasType (.sort relevant) := by
  match certificate with
  | .seed observation _ => exact correct level relevant rfl flag observation (by simpa only [CodeCert.nativeDepth] using bound) resources
  | .union left right =>
    have bounds := Nat.max_le.mp (show max (left.nativeDepth current) (right.nativeDepth current) ≤ fuel by simpa only [CodeCert.nativeDepth] using bound)
    exact (CodeCert.sortCorrect correct flag left bounds.1
      (fun i need hm => resources i need (List.mem_append_left _ hm))).union
      (CodeCert.sortCorrect correct flag right bounds.2
        (fun i need hm => resources i need (List.mem_append_right _ hm)))
  | .pad source => exact (CodeCert.sortCorrect correct flag source (by simpa only [CodeCert.nativeDepth] using bound) resources).pad_sort
  | .familyPad source => exact (CodeCert.sortCorrect correct flag source (by simpa only [CodeCert.nativeDepth] using bound) resources).familyPad
  | .unpad source =>
    simpa only [Profile.down_sort] using (CodeCert.sortCorrect correct flag source (by simpa only [CodeCert.nativeDepth] using bound) resources).pad_inv
  | .down source =>
    simpa only [Profile.down_sort] using (CodeCert.sortCorrect correct flag source (by simpa only [CodeCert.nativeDepth] using bound) resources).down
  | .map view source => exact view.mapType_sort (CodeCert.sortCorrect correct flag source (by simpa only [CodeCert.nativeDepth] using bound) resources)
  | .select source member => exact (CodeCert.sortCorrect correct flag source (by simpa only [CodeCert.nativeDepth] using bound) resources).singleton_of_mem member
  | .focusMinimal source minimal focusedBound => exact (CodeCert.sortCorrect correct flag source (by simpa only [CodeCert.nativeDepth] using bound) resources).restrict focusedBound minimal.typed.wf_type
termination_by sizeOf certificate

theorem Transfer.proofIrrel
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {target : List VExpr} {locals : List Nat} {σ τ : Subst} {available : Valuation}
    {left right proposition : VExpr}
    (propositionCorrect : SortCorrect current fuel env U registry target locals σ
      available proposition (.sort .zero))
    (original : Transfer current fuel env U registry target locals σ τ
      available left left proposition) :
    Transfer current fuel env U registry target locals σ τ
      available left right proposition := by
  intro n demand footprint observation bound resources
  obtain ⟨result⟩ := original observation bound resources
  have propositionTyped := CodeCert.sortCorrect propositionCorrect
    (show Relevant .zero false from rfl) result.toGradedTransferResult.requestedCertificate
    (by simpa only [GradedTransferResult.requestedCertificate, CodeCert.nativeDepth_lower] using result.certificateBound) result.typeAvailable
  have empty := result.toGradedTransferResult.requestedTyped.proof_empty propositionTyped
  change demand = .empty at empty
  subst demand
  exact ⟨Result.empty⟩

theorem Joint.proofIrrel
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered)
    {source : List VExpr} {left right proposition : VExpr}
    (originalProposition : Joint current fuel env U registry source proposition proposition (.sort .zero))
    (originalLeft : Joint current fuel env U registry source left left proposition)
    (originalRight : Joint current fuel env U registry source right right proposition) :
    Joint current fuel env U registry source left right proposition := by
  apply Joint.of_transfers henv
  intro target locals σ τ available closed hTarget substitutions fits
  have hp := originalProposition target locals σ τ available closed hTarget substitutions fits
  have hl := originalLeft target locals σ τ available closed hTarget substitutions fits
  have hr := originalRight target locals σ τ available closed hTarget substitutions fits
  exact ⟨Transfer.proofIrrel hp.2.2.1 hl.1,
    Transfer.proofIrrel hp.2.2.1 hr.1⟩

end Lean4Lean.AnchoredSource.Adapted.Staged
