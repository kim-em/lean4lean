import Lean4Lean.Theory.Typing.Strengthening.ProofErasureConstructorDemandTransport

/-! # Native recovery for the joint observer, conditional on type evolution

The induction is complete for variables, applications, lambdas, ground unit
values and every type key. The remaining premises are preservation of observed
types by the selected computation language and the constructor native header. These premises are not asserted for the full enriched union here.
-/
namespace Lean4Lean.VEnv.Strengthening.ConstructorDemand
open _root_.Lean4Lean Params ProofShape
variable [Params] {unit record : AtomicControl.Atom} {uc ctor family : Name}

/-- Every native output carries the source's type key once observed type
computation and the constructor header is supplied. These are explicit
remaining obligations, not consequences claimed from ordinary typing. -/
theorem Obs.native_of_type_preservation
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hcomp : ∀ {Δ S a b key}, S.Typed unit record Δ → Valuation unit record uc ctor family Δ S →
      ScopedCompute Step Δ a b → Obs unit record uc ctor family Δ S a (.type key) →
      Obs unit record uc ctor family Δ S b (.type key))
    (hctor : ∀ {Δ S T},
      HeterogeneousControl.ControlTyping Δ (.const ctor []) (.arrow (.atom unit) (.atom record)) →
      ScopedTypeRecovery Step Δ (.const ctor []) T →
      Obs unit record uc ctor family Δ S T (.type (.fn (.atom unit) [.unit] .record)))
    (H : Obs unit record uc ctor family Δ S source key)
    (HS : S.Typed unit record Δ) (HV : Valuation unit record uc ctor family Δ S)
    (RN : ScopedTypeRecovery Step Δ source out) : Obs unit record uc ctor family Δ S out (.type key) := by
  induction H generalizing out with
  | var _ _ hi => exact hcomp HS HV RN.bvar_compute (HV _ _ hi)
  | unit_ctor HT => exact .unit_type (TypeEquality.of_native hstep HT RN)
  | record_ctor HT => exact hctor HT RN
  | family HT => exact .family_type (TypeEquality.of_native hstep HT RN)
  | family_type HE => exact (Obs.family_type HE).native_type hstep RN
  | unit_type HE => exact (Obs.unit_type HE).native_type hstep RN
  | univ HK HE => exact (Obs.univ HK HE).native_type hstep RN
  | app HT _ HX ihf _ =>
    exact application_native_of_type_preservation hstep (hcomp HS HV) HT
      (fun X Y RF => ihf HS HV RF) HX HS RN
  | lam HT HE HK HA HB _ ihb =>
    exact lambda_native_of_type_preservation hstep (hcomp HS HV) (.lam HT HE HK HA HB)
      (fun R => ihb (HS.cons HE HK) (HV.cons HE HA) R) RN
  | pi HT HE HK HA HB => exact (Obs.pi HT HE HK HA HB).native_type hstep RN

/-- Under the stated native-induction premises, an actual selected Tag p
guard exposes an observed unit parameter. This is the parameter needed by a
record-structure root; no exact recovery of p is assumed. -/
theorem Obs.native_parameter_of_type_preservation
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hcomp : ∀ {Δ S a b key}, S.Typed unit record Δ → Valuation unit record uc ctor family Δ S →
      ScopedCompute Step Δ a b → Obs unit record uc ctor family Δ S a (.type key) →
      Obs unit record uc ctor family Δ S b (.type key))
    (hctor : ∀ {Δ S T},
      HeterogeneousControl.ControlTyping Δ (.const ctor []) (.arrow (.atom unit) (.atom record)) →
      ScopedTypeRecovery Step Δ (.const ctor []) T →
      Obs unit record uc ctor family Δ S T (.type (.fn (.atom unit) [.unit] .record)))
    (H : Obs unit record uc ctor family Δ S source .record)
    (HS : S.Typed unit record Δ) (HV : Valuation unit record uc ctor family Δ S)
    (RN : ScopedTypeRecovery Step Δ source (.app (.const family []) p)) :
    Obs unit record uc ctor family Δ S p .unit :=
  (H.native_of_type_preservation hstep hcomp hctor HS HV RN).family_parameter

end Lean4Lean.VEnv.Strengthening.ConstructorDemand
