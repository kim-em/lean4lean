import Lean4Lean.Theory.Typing.AnchoredNativeCaptureRouting

/-! The actual common-prefix capture route places every RHS requirement
strictly before the major. This holds for every requested RHS observation,
including when the zero-field native program is eliminating a neutral major. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics InductiveSignature NativeRecursorData

theorem InitialNativeCaptureRoute.prefix_noMajor
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {target : List VExpr}
    {data : NativeRecursorData} {program : SaturatedProgram data}
    {nativeArguments capturePrefix : List VExpr}
    (nativeValues : program.prefixArgs = nativeArguments.map (·.subst σ))
    (prefixEq : capturePrefix = nativeArguments.take data.indexOffset)
    (bound : data.indexOffset ≤ nativeArguments.length)
    (ledger : NativeArgumentLedger env U registry target locals σ available capturePrefix required)
    (saturated : nativeArguments.length = data.majorOffset + 1) (need : Need) :
    (0, need) ∉ (InitialNativeCaptureRoute.prefix nativeValues prefixEq bound ledger
      (witnesses := witnesses)).nativeFootprint := by
  change (0, need) ∉ Footprint.sourceLift
    (.skipN .refl (program.prefixArgs.length - data.indexOffset)) required
  rw [nativeValues, List.length_map]
  intro member
  obtain ⟨⟨index, oldNeed⟩, _, same⟩ := List.mem_map.mp member
  have first := congrArg Prod.fst same
  simp only [Lift.liftVar_skipN, Lift.liftVar, saturated, majorOffset] at first
  omega

end Lean4Lean.AnchoredSource.Adapted
