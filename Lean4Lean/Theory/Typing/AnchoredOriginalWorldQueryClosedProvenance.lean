import Lean4Lean.Theory.Typing.AnchoredOriginalWorldQueryContextualProvenance

/-! Closed initial queries receive actual opening provenance without a new
annotation premise. This constructs the finite initial dependency data only;
recursive sponsorship must preserve the initial frontier rather than rebuild
an unconstrained envelope at every returned query. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalFactorCut
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

noncomputable def RichObs.closedInitialWorldProvenance
    (strata : EquationStratification env) (henv : env.Ordered)
    (ordered : sourceEnv.Ordered) (below : sourceEnv ≤ env) (fuel : Nat → Nat)
    (reference : EndpointRef sourceEnv U [] expression assigned)
    (query : RichObs sourceEnv env U registry target (.ref reference) [] σ profile []) :
    WorldObsProvenance strata query := by
  let controls : OriginalWorldControls strata sourceEnv :=
    ⟨ordered, strata.rules.length, Nat.le_refl _, strata.fullCutoff.source_mono below, fuel⟩
  let occurrence : OriginalRichOccurrenceFrame (.here (root := reference)) .nil env registry target
      [] σ σ (fun _ => []) ordered [] := ⟨.nil, .nil, Nat.le_refl _⟩
  exact RichObs.contextualWorldProvenance query controls occurrence .nil henv below
    (by intro _ _ member; cases member)

noncomputable def RichCert.closedInitialWorldProvenance
    (strata : EquationStratification env) (henv : env.Ordered)
    (ordered : sourceEnv.Ordered) (below : sourceEnv ≤ env) (fuel : Nat → Nat)
    (reference : EndpointRef sourceEnv U [] expression assigned)
    (certificate : RichCert sourceEnv env U registry target (.ref reference) [] σ relevant profile []) :
    WorldCertProvenance strata certificate := by
  let controls : OriginalWorldControls strata sourceEnv :=
    ⟨ordered, strata.rules.length, Nat.le_refl _, strata.fullCutoff.source_mono below, fuel⟩
  let occurrence : OriginalRichOccurrenceFrame (.here (root := reference)) .nil env registry target
      [] σ σ (fun _ => []) ordered [] := ⟨.nil, .nil, Nat.le_refl _⟩
  exact RichCert.contextualWorldProvenance certificate controls occurrence .nil henv below
    (by intro _ _ member; cases member)

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
