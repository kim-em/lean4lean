import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCertifiedRecordNative
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureIgnoredRecordStructure

/-! # Joint record demands with independent family evidence

Family evidence supplies only its explicitly stated structural laws. Full
computation preservation is discharged independently of the joint native proof.
-/
namespace Lean4Lean.VEnv.Strengthening.CertifiedRecordDemand
open _root_.Lean4Lean Params ProofShape
open ConstructorDemand (Key TypeEquality Sets unitCarrier UnitArrows)
open IgnoredRecordDemand (recordCarrier constructor_instL header_erasure)
variable [Params] {evidence : FamilyEvidence}
variable (hi : env.projections s (PositiveHeaderRegistration.info 0 [] s uc))
variable (hS : env.HasType univs [] (.const s []) (.sort (.succ .zero)))
variable (Q : UnitArrows)
local notation "U" => unitCarrier hi hS
variable (hTag : env.projections t (PositiveHeaderRegistration.info 0 [(Q.control (unitCarrier hi hS)).expr] t c))
variable (hF : env.HasType univs [] (.const t []) (.forallE (Q.control (unitCarrier hi hS)).expr (.sort (.succ .zero))))

local notation "RT" => recordCarrier hi hS Q hTag hF

/-- Every conversion tail of the actual constant certificate starts at the
observed stored Pi. Type-computation preservation is discharged by stage
induction later, rather than assumed as semantic type coverage. -/
theorem registered_constructor_native_of_type_preservation
    (hΓ : OnCtx Γ (env.IsType univs))
    (hcomp : ∀ {a b key}, ScopedCompute Step (proofEraseCtx Γ) a b →
      Obs evidence U RT (Q.control U) uc c t (proofEraseCtx Γ) S a (.type key) →
      Obs evidence U RT (Q.control U) uc c t (proofEraseCtx Γ) S b (.type key))
    (RN : ScopedTypeRecovery Step (proofEraseCtx Γ) (.const c []) out) :
    Obs evidence U RT (Q.control U) uc c t (proofEraseCtx Γ) S out (.type (.fn (Q.control U) [] .record)) := by
  have R := RN.const_compute (henv.ordered.projectionConstructor hTag)
  rw [constructor_instL hi hS Q] at R
  rw [header_erasure hi hS Q hF (by trivial)] at R
  exact hcomp R (Obs.of_ignored (IgnoredRecordDemand.registered_header_observation hi hS Q hTag hF hΓ))

end Lean4Lean.VEnv.Strengthening.CertifiedRecordDemand
