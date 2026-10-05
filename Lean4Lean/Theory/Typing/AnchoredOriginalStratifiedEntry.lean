import Lean4Lean.Theory.Typing.AnchoredOriginalRichHeadDepth
import Lean4Lean.Theory.Typing.EquationControls

/-! The proposed stratified induction imposes no new query restriction at
the final environment. Its full equation cutoff makes every actual query and
certificate admissible with zero higher fuel, using the existing Ordered
assumption alone. Closing the recursive induction remains separate. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
set_option Elab.async false

theorem RichObs.initialStratifiedControls (ordered : env.Ordered)
    (query : RichObs sourceEnv env U registry target node locals σ profile footprint) :
    EquationStratifiedFuel.WithinAbove ordered.equationStrata.rules.length (fun _ => 0)
      (fun control => query.stratifiedDepth (ordered.equationStrata.headOrdinal registry) control) := by
  intro control above
  exact Nat.le_of_eq (query.stratifiedDepth_above _
    (ordered.equationStrata.headOrdinal_le registry) above)

theorem RichCert.initialStratifiedControls (ordered : env.Ordered)
    (certificate : RichCert sourceEnv env U registry target node locals σ relevant profile footprint) :
    EquationStratifiedFuel.WithinAbove ordered.equationStrata.rules.length (fun _ => 0)
      (fun control => certificate.stratifiedDepth (ordered.equationStrata.headOrdinal registry) control) := by
  intro control above
  exact Nat.le_of_eq (certificate.stratifiedDepth_above _
    (ordered.equationStrata.headOrdinal_le registry) above)

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
