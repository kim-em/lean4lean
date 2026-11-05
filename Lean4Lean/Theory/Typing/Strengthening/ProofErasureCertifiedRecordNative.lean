import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCertifiedRecordTransport

/-! # Joint record demands with independent family evidence

Family evidence supplies only its explicitly stated structural laws. Full
computation preservation is discharged independently of the joint native proof.
-/
namespace Lean4Lean.VEnv.Strengthening.CertifiedRecordDemand
open _root_.Lean4Lean Params ProofShape
open ConstructorDemand (Key TypeEquality Sets lambda_domain_equality)
variable [Params] {evidence : FamilyEvidence} {unit record : AtomicControl.Atom} {parameter : HeterogeneousControl.ControlType} {uc ctor family : Name}

/-- Every native output carries the source's type key once observed type
computation and the constructor header is supplied. These are explicit
remaining obligations, not consequences claimed from ordinary typing. -/
theorem Obs.native_of_type_preservation
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hcomp : ∀ {Δ S a b key}, S.Typed unit record Δ → Valuation evidence unit record parameter uc ctor family Δ S →
      ScopedCompute Step Δ a b → Obs evidence unit record parameter uc ctor family Δ S a (.type key) →
      Obs evidence unit record parameter uc ctor family Δ S b (.type key))
    (hctor : ∀ {Δ S T},
      HeterogeneousControl.ControlTyping Δ (.const ctor []) (.arrow parameter (.atom record)) →
      ScopedTypeRecovery Step Δ (.const ctor []) T →
      Obs evidence unit record parameter uc ctor family Δ S T (.type (.fn parameter [] .record)))
    (H : Obs evidence unit record parameter uc ctor family Δ S source key)
    (HS : S.Typed unit record Δ) (HV : Valuation evidence unit record parameter uc ctor family Δ S)
    (RN : ScopedTypeRecovery Step Δ source out) : Obs evidence unit record parameter uc ctor family Δ S out (.type key) := by
  induction H generalizing out with
  | var _ _ hi => exact hcomp HS HV RN.bvar_compute (HV _ _ hi)
  | unit_ctor HT => exact .unit_type (TypeEquality.of_native hstep HT RN)
  | record_ctor HT => exact hctor HT RN
  | family HT => exact .family_type (TypeEquality.of_native hstep HT RN)
  | family_type HE => exact (Obs.family_type HE).native_type hstep RN
  | record_type HE HR => exact (Obs.record_type HE HR).native_type hstep RN
  | unit_type HE => exact (Obs.unit_type HE).native_type hstep RN
  | univ HK HE => exact (Obs.univ HK HE).native_type hstep RN
  | app HT _ HX ihf _ =>
    exact application_native_of_type_preservation hstep (hcomp HS HV) HT
      (fun X Y RF => ihf HS HV RF) HX HS RN
  | lam HT HE HK HA HB _ ihb =>
    exact lambda_native_of_type_preservation hstep (hcomp HS HV) (.lam HT HE HK HA HB)
      (fun R => ihb (HS.cons HE HK) (HV.cons HE HA) R) RN
  | pi HT HE HK HA HB => exact (Obs.pi HT HE HK HA HB).native_type hstep RN

end Lean4Lean.VEnv.Strengthening.CertifiedRecordDemand
