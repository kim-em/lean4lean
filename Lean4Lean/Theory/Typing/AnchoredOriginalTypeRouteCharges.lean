import Lean4Lean.Theory.Typing.AnchoredOriginalTypeRouteLedger

/-! An exact producer reserve recovers the structural charges required by
recursive application histories. Every original closure and frame ledger is
preserved; no numerical bound is used to manufacture a charge. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalEndpointFactor.Dependency
open OriginalClosureMeasure

def ParameterRouteCharges.head
    (charges : ParameterRouteCharges sources initial count (closure :: rest)) :
    ParameterRouteCharge sources initial count closure := by
  cases charges with
  | cons charge _ => exact charge

def ParameterRouteCharges.tail
    (charges : ParameterRouteCharges sources initial count (closure :: rest)) :
    ParameterRouteCharges sources initial count rest := by
  cases charges with
  | cons _ tail => exact tail

noncomputable def ParameterRouteCharges.split
    (first second : List Closure)
    (charges : ParameterRouteCharges sources initial count (first ++ second)) :
    ParameterRouteCharges sources initial count first × ParameterRouteCharges sources initial count second := by
  induction first with
  | nil => exact ⟨.nil, charges⟩
  | cons closure rest ih =>
    have next := ih charges.tail
    exact ⟨.cons charges.head next.1, next.2⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalEndpointFactor.Dependency

namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail OriginalEndpointFactor.Dependency
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1200000

variable {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {target common : List VExpr}
set_option Elab.async false

/-- Recover the finite tree's exact charges from its already charged output
list. This allows an existential source producer to feed the next applyPi
without exposing or choosing a different history. -/
noncomputable def RawGeneratedTypeRoute.chargedOfReserve
    {left : OriginalNestedDisplay U common leftExpression leftAssigned}
    {right : OriginalNestedDisplay U common rightExpression rightAssigned}
    (route : RawGeneratedTypeRoute env registry target commonLeft commonRight left right first last)
    (charges : ParameterRouteCharges sources initial count route.reserve) :
    route.Charged sources initial count := by
  match route with
  | .identity .. => rw [Charged.eq_def]; exact PUnit.unit
  | .same .. | .assigned .. | .equality .. =>
    rw [Charged.eq_def]
    rw [reserve.eq_def] at charges
    exact charges.head
  | .typedEquality .. =>
    rw [Charged.eq_def]
    rw [reserve.eq_def] at charges
    exact ⟨charges.head, charges.tail.head⟩
  | .trans first second =>
    rw [reserve.eq_def] at charges
    have split := charges.split first.reserve second.reserve
    rw [Charged.eq_def]
    exact ⟨first.chargedOfReserve split.1, second.chargedOfReserve split.2⟩
  | .piDomain _ _ _ child =>
    rw [reserve.eq_def] at charges
    rw [Charged.eq_def]
    exact child.chargedOfReserve charges
  | .applyPi (whole := whole) .. =>
    rw [reserve.eq_def] at charges
    have split := charges.split whole.reserve _
    rw [Charged.eq_def]
    exact ⟨whole.chargedOfReserve split.1, split.2.head, split.2.tail.head⟩
termination_by sizeOf route

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
