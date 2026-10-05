import Lean4Lean.Theory.Typing.AnchoredOriginalScopedResourceTransfer

/-! Project shared resource-transfer syntax from the actual scoped replay
producer's SAME queries, adapters, footprint, and selected merged frame.
There is no fresh observation selection or semantic transfer hypothesis. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure OriginalEndpointFactor
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false

noncomputable def RichArgumentSupply.footprintTransfer
    {available : Valuation}
    {destination : OriginalNestedDisplay U common expression assigned}
    (supply : RichArgumentSupply destination.sourceEnv env U registry target destination.node locals
      (destination.raw.comp commonLeft) available needs)
    (sourceRaw : Subst) (index : Nat) (agreement : expression = sourceRaw index) :
    RichFootprintTransfer sourceRaw destination.sourceEnv env U registry target destination.context
      destination.raw locals commonLeft (needs.map fun need => (index, need)) supply.footprint := by
  induction supply with
  | nil => exact .nil
  | cons head tail ih =>
    exact .query destination.node destination.provenance (destination.expression_eq.symm.trans agreement)
      head.bound head.observation head.adapter ih

/-- The map uses exactly the queries retained by the finite scoped R producer.
Different owner scopes have already been eliminated by genuine R/unweaken;
the subsequent merge changes availability proofs, not these queries. -/
noncomputable def ScopedResourceSupply.footprintTransfer
    {base : OriginalCaptureBase env U registry target}
    {destination : OriginalNestedDisplay U common expression assigned}
    (supply : ScopedResourceSupply base caps commonLeft commonRight destination capacity needs)
    (sourceRaw : Subst) (index : Nat) (agreement : expression = sourceRaw index) :
    RichFootprintTransfer sourceRaw destination.sourceEnv env U registry target destination.context
      destination.raw supply.locals commonLeft (needs.map fun need => (index, need)) supply.supply.footprint :=
  supply.supply.footprintTransfer sourceRaw index agreement

/-- The advertised shared footprint is actually available in the SAME
selected generated frame; this is not a claimed empty footprint. -/
theorem ScopedResourceSupply.footprintTransfer_available
    (supply : ScopedResourceSupply base caps commonLeft commonRight destination capacity needs) :
    supply.supply.footprint.Available supply.available := supply.supply.available

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
