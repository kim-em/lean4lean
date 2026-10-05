import Lean4Lean.Theory.Typing.AnchoredNativeDepthProvenance
import Lean4Lean.Theory.Typing.AnchoredBoundedStage
import Lean4Lean.Theory.Typing.AnchoredStageBudgets

/-! A result actually constructed by an old header at its own finite control
budget satisfies the new block's budget on the SAME witnesses. In particular
this covers NEW observers/certificates produced by reverse unfolding, not just
the unchanged native packet returned by constDF. -/
namespace Lean4Lean.AnchoredSource.Adapted.Staged
open VExpr VEnv AnchoredProfiles
variable {base env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
  {target : List VExpr} {locals : List Nat} {σ τ : Subst} {available : Valuation}
  {before declarations : List VDecl} {old : Name → Option InductiveSignature.NativeRecursorData}
  {first : NativeRegistryHistory base before old}
  {last : NativeRegistryHistory env declarations registry.natives}
  {oldControl : Name → Bool} {oldFuel fuel : Nat}
  {left right sourceType : VExpr} {demand : Profile n}

/-- Only depth proof fields change. The supplied result is the actual result
of the old-stage call; no new typing proof is interpreted here. -/
def Result.recontrol
    (continuation : NativeRegistryHistory.Prefix first last)
    (current : Name → Bool)
    (quiet : ∀ name value, base.constants name = some value → current name = false)
    (rightKnown : right.ConstantsIn base) (typeKnown : sourceType.ConstantsIn base)
    (result : Result oldControl oldFuel env U registry target locals σ τ available
      left right sourceType demand) :
    Result current fuel env U registry target locals σ τ available left right sourceType demand where
  toGradedTransferResult := result.toGradedTransferResult
  observationBound := by rw [result.observation.nativeDepth_of_constants continuation current quiet rightKnown]; omega
  certificateBound := by rw [result.certificate.nativeDepth_of_constants continuation current quiet typeKnown]; omega

/-- Actual current-block freshness and the original earlier endpoint/type
roots discharge every new bound, regardless of the old result's own fuel. -/
def Result.beforeBlock
    (continuation : NativeRegistryHistory.Prefix first last)
    (stages : VInductBlock.TypingStages base block installed)
    (originalRight : base.IsDefEqStrong sourceU source right other sourceType)
    (result : Result oldControl oldFuel env U registry target locals σ τ available
      left right sourceType demand) :
    Result (fun name => block.recursors.any (fun value => value.name == name)) fuel
      env U registry target locals σ τ available left right sourceType demand :=
  result.recontrol continuation _ (fun _ _ present => stages.currentNames_old present)
    originalRight.constantsIn.1 originalRight.typeConstantsIn

private theorem PairedFits.independentControl
    {source : List VExpr} {current : Name → Bool}
    (fits : PairedFits current fuel env U registry source target locals σ τ available)
    (control : Name → Bool) :
    ∃ lower, ∀ upper, lower ≤ upper →
      PairedFits control upper env U registry source target locals σ τ available := by
  have finite : Budgeted.PairedFits [] env U registry source target locals σ τ available := by
    constructor <;> constructor
    · intro index need member type lookup
      obtain ⟨entry, bounded⟩ := fits.forward.entry index need member type lookup
      exact ⟨entry, by intro _ _ member; cases member⟩
    · intro index need member type lookup
      obtain ⟨entry, bounded⟩ := fits.backward.entry index need member type lookup
      exact ⟨entry, by intro _ _ member; cases member⟩
  obtain ⟨lower, chosen⟩ := finite.finiteControl control
  refine ⟨lower, fun upper bound => ?_⟩
  constructor <;> constructor
  · intro index need member type lookup
    obtain ⟨entry, bounded⟩ := chosen.forward.entry index need member type lookup
    exact ⟨entry, Nat.le_trans (bounded control lower (List.mem_singleton_self _)) bound⟩
  · intro index need member type lookup
    obtain ⟨entry, bounded⟩ := chosen.backward.entry index need member type lookup
    exact ⟨entry, Nat.le_trans (bounded control lower (List.mem_singleton_self _)) bound⟩

/-- Reuse a REAL completed header induction hypothesis at its own control.
The finite input valuation and observer determine the single local fuel used
for each call. Both returned source witnesses are bounded independently by
their earlier source provenance, so no all-filter semantic hypothesis is
assumed and no newly returned observer is recursively interpreted. -/
theorem Joint.recontrol
    {source : List VExpr}
    (continuation : NativeRegistryHistory.Prefix first last)
    (current : Name → Bool)
    (quiet : ∀ name value, base.constants name = some value → current name = false)
    (leftKnown : left.ConstantsIn base) (rightKnown : right.ConstantsIn base)
    (typeKnown : sourceType.ConstantsIn base)
    (original : ∀ localFuel, Joint oldControl localFuel env U registry source left right sourceType) :
    Joint current fuel env U registry source left right sourceType := by
  intro target locals σ τ available closed hTarget substitutions fits
  obtain ⟨fitFuel, fitted⟩ := fits.independentControl oldControl
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n demand footprint observation bound resources
    let localFuel := max fitFuel (observation.nativeDepth oldControl)
    have joint := original localFuel target locals σ τ available closed hTarget substitutions
      (fitted localFuel (Nat.le_max_left _ _))
    obtain ⟨result⟩ := joint.1 observation (Nat.le_max_right _ _) resources
    exact ⟨result.recontrol continuation current quiet rightKnown typeKnown⟩
  · intro n demand footprint observation bound resources
    let localFuel := max fitFuel (observation.nativeDepth oldControl)
    have joint := original localFuel target locals σ τ available closed hTarget substitutions
      (fitted localFuel (Nat.le_max_left _ _))
    obtain ⟨result⟩ := joint.2.1 observation (Nat.le_max_right _ _) resources
    exact ⟨result.recontrol continuation current quiet leftKnown typeKnown⟩
  · intro level relevant typeEq relevance n demand footprint observation bound resources
    let localFuel := max fitFuel (observation.nativeDepth oldControl)
    have joint := original localFuel target locals σ τ available closed hTarget substitutions
      (fitted localFuel (Nat.le_max_left _ _))
    exact joint.2.2.1 level relevant typeEq relevance observation (Nat.le_max_right _ _) resources
  · intro level relevant typeEq relevance n demand footprint observation bound resources
    let localFuel := max fitFuel (observation.nativeDepth oldControl)
    have joint := original localFuel target locals σ τ available closed hTarget substitutions
      (fitted localFuel (Nat.le_max_left _ _))
    exact joint.2.2.2 level relevant typeEq relevance observation (Nat.le_max_right _ _) resources

theorem Joint.beforeBlock
    {source : List VExpr}
    (continuation : NativeRegistryHistory.Prefix first last)
    (stages : VInductBlock.TypingStages base block installed)
    (raw : base.IsDefEqStrong sourceU source left right sourceType)
    (original : ∀ localFuel, Joint oldControl localFuel env U registry source left right sourceType) :
    Joint (fun name => block.recursors.any (fun value => value.name == name)) fuel
      env U registry source left right sourceType :=
  Joint.recontrol continuation _ (fun _ _ present => stages.currentNames_old present)
    raw.constantsIn.1 raw.constantsIn.2 raw.typeConstantsIn original

end Lean4Lean.AnchoredSource.Adapted.Staged
