import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCertifiedRecordSubstitution
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureSpineEtaDiamond
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEtaHead

/-! # Joint record demands with independent family evidence

Family evidence supplies only its explicitly stated structural laws. Full
computation preservation is discharged independently of the joint native proof.
-/
namespace Lean4Lean.VEnv.Strengthening.CertifiedRecordDemand
open _root_.Lean4Lean Params ProofShape
open ConstructorDemand (Key TypeEquality Sets lambda_domain_equality)
open private erase_app_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
variable [Params] {evidence : FamilyEvidence} {unit record : AtomicControl.Atom} {parameter : HeterogeneousControl.ControlType} {uc ctor family : Name}

/-- Native outputs of unit values need only the ordinary unit-carrier
certificate; there is no dependent parameter to lose in this ground case. -/
theorem Obs.native_unit (hstep : ErasedScopedPrimitiveDescent Step)
    (H : Obs evidence unit record parameter uc ctor family Δ S source .unit)
    (RN : ScopedTypeRecovery Step Δ source out) :
    Obs evidence unit record parameter uc ctor family Δ S out (.type .unit) :=
  .unit_type (TypeEquality.of_native hstep H.typing RN)

/-- A native output of an observed type is an ordinary universe certificate.
This handles all higher type keys without requiring literal sort normalization. -/
theorem Obs.native_type (hstep : ErasedScopedPrimitiveDescent Step)
    (H : Obs evidence unit record parameter uc ctor family Δ S source (.type key))
    (RN : ScopedTypeRecovery Step Δ source out) :
    Obs evidence unit record parameter uc ctor family Δ S out (.type (.type key)) :=
  .univ (by simpa only [Key.Valid] using H.valid) (TypeEquality.of_native hstep H.typing RN)

/-- Missing type-computation closure is isolated here as a premise. With it
and the function's native induction hypothesis, the application case recovers
an observed dependent result using demanded argument substitution. No native
certificate for the current argument occurs in the theorem. -/
theorem application_native_of_type_preservation
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hcomp : ∀ {a b key}, ScopedCompute Step Δ a b →
      Obs evidence unit record parameter uc ctor family Δ S a (.type key) → Obs evidence unit record parameter uc ctor family Δ S b (.type key))
    (HT : HeterogeneousControl.ControlTyping Δ (.app f a) (result.control unit record))
    (HF : ∀ X Y, ScopedTypeRecovery Step Δ f (.forallE X Y) →
      Obs evidence unit record parameter uc ctor family Δ S (.forallE X Y) (.type (.fn domain keys result)))
    (HX : ∀ key ∈ keys, Obs evidence unit record parameter uc ctor family Δ S a key)
    (HS : S.Typed unit record Δ)
    (RN : ScopedTypeRecovery Step Δ (.app f a) out) :
    Obs evidence unit record parameter uc ctor family Δ S out (.type result) := by
  obtain ⟨X, Y, RF, RC⟩ := RN.app_origin
  have Hpi := HF X Y RF
  obtain ⟨Γ, e, hΓ, EΓ, ht, Ee⟩ := HT
  obtain ⟨f₀, x, rfl, _, Ef, Ex⟩ := erase_app_inv Ee
  obtain ⟨A, B, hf, hx⟩ := ht.app_inv henv hΓ
  obtain ⟨A', B', hfPi, EA, _⟩ := proofErase_scoped_recovered_pi_descend hstep hΓ hΓ
    (Ctx.LiftN.zero []) hf (by simpa only [List.length_nil, ProofShape.liftN_zero, EΓ, Ef] using RF)
  simp only [List.length_nil, ProofShape.liftN_zero] at EA
  have hxA := argument_at_displayed_domain hΓ hf hfPi hx
  obtain ⟨_, hPi⟩ := hfPi.isType henv hΓ
  obtain ⟨⟨u, hA⟩, _, _⟩ := hPi.forallE_inv henv
  have hΓA : OnCtx (A' :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  have W : ContextSubstitution (X :: Δ) Δ (Subst.one a) := by
    have Wraw : ContextSubstitution (proofEraseCtx (A' :: Γ)) (proofEraseCtx Γ)
        (Subst.one (proofErase Γ x)) :=
      ContextSubstitution.of_typed hΓ (Ctx.InstN.zero.substEq hΓA hxA) (erasedSubstAgreement_one hΓA hxA)
    intro Γ₀ hΓ₀ EΓ₀
    simpa only [EΓ, Ex] using Wraw hΓ₀ (by simpa only [proofEraseCtx, EA, EΓ] using EΓ₀)
  exact hcomp RC (Hpi.pi_instantiate W HX HS)

end Lean4Lean.VEnv.Strengthening.CertifiedRecordDemand
