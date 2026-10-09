import Lean4Lean.Theory.Typing.Strengthening.Descents
import Lean4Lean.Theory.Typing.Strengthening.SpineClosure
import Lean4Lean.Theory.Typing.Strengthening.MajorEta

/-! # Typing strengthening: the final theorem

Direction F (`docs/inductives/STRENGTHENING_F_LOG.md`). Under `env.WF` and canonical `Eq`:

```
Strengthening ⇔ Cancel ⇔ TypedFront
```

given `GenericTypesTyped₀` (the generic case types are typed in `[]`, giving `ElimFrontN`),
`GenericRulesTyped₀` (the generic case equations are typed in `[]`, giving with `TypedFront` the
case-iota guard descent `caseRedexDescends`), `ProjFieldFrontPropN` (the field-type closure for
structures in `Prop`, giving `ProjFrontN` through the proved eta closure and the descent of the
composite major-eta step `majorEtaDescends`) and `UnfoldingCheckDescends` (the descent of the
prefix-unfolding guard, see the log for why it is not a `TypedFront` instance as stated).
`cancel_iff_typedFront_and_elim` is the variant exact in the eliminator component. -/

namespace Lean4Lean.VEnv.StrengtheningFinal
open VExpr VEnv.StrengtheningTypingFront VEnv.StrengtheningReplay VEnv.StrengtheningExposure
  VEnv.StrengtheningEtaNormal VEnv.StrengtheningEtaPostponement VEnv.StrengtheningEtaClosure
  VEnv.StrengtheningSpineExposure VEnv.StrengtheningClosures VEnv.StrengtheningDescents
  VEnv.StrengtheningSpineClosure VEnv.StrengtheningMajorEta

variable {env : VEnv}

/-- The guard descents from the typed front: the case-iota guard (`caseRedexDescends`) and the
composite major-eta step (`majorEtaDescends`), at every universe bound. -/
theorem descents_of_typedFront (henv : env.WF) (heq : env.HasCanonicalEq)
    (hTF : StrengtheningKripke.TypedFront env) (hRules : GenericRulesTyped₀ env)
    (hField : ProjFieldFrontN env) :
    (∀ U, @CaseRedexDescends (henv.params U)) ∧ (∀ U, @MajorEtaDescends (henv.params U)) := by
  have hTFN := (typedFrontN_iff_typedFront henv heq).mpr hTF
  have hcase : ∀ U, @CaseRedexDescends (henv.params U) := fun U =>
    letI := henv.params U
    caseRedexDescends hTFN hRules
  refine ⟨hcase, fun U => ?_⟩
  letI := henv.params U
  exact majorEtaDescends hTFN (hcase U) (fun hp => Params.checkVars henv U hp) hField

/-- `Cancel ↔ TypedFront ∧ ElimFrontN`, given the generic rule typings, the field-type closure
in `Prop` and the unfolding-check descent. The `ElimFrontN` component is exact: `Cancel`
implies it (`cancel_iff_typedFront_and_closures`). -/
theorem cancel_iff_typedFront_and_elim (henv : env.WF) (heq : env.HasCanonicalEq)
    (hRules : GenericRulesTyped₀ env) (hField : ProjFieldFrontPropN env)
    (hunfold : ∀ U, @UnfoldingCheckDescends (henv.params U)) :
    Cancel env ↔ StrengtheningKripke.TypedFront env ∧ ElimFrontN env := by
  constructor
  · intro hc
    have h := (cancel_iff_typedFront_and_closures henv heq).mp hc
    exact ⟨h.1, h.2.2.2⟩
  · rintro ⟨hTF, hElim⟩
    have hFieldN := ProjFieldFrontN.of_notNeverZero henv hField
    obtain ⟨hcase, hmajor⟩ := descents_of_typedFront henv heq hTF hRules hFieldN
    exact (cancel_iff_typedFront_B3 henv heq hcase hunfold hmajor
      (ProjFrontN.of_closure henv heq hTF hcase hunfold hmajor hFieldN) hElim).mpr hTF

/-- The final theorem: under `WF` and canonical `Eq`, `Cancel ↔ TypedFront` given the generic
type and rule typings of the registered case schemas, the field-type closure for structures in
`Prop`, and the unfolding-check descent. -/
theorem cancel_iff_typedFront_final (henv : env.WF) (heq : env.HasCanonicalEq)
    (hGen : GenericTypesTyped₀ env) (hRules : GenericRulesTyped₀ env)
    (hField : ProjFieldFrontPropN env)
    (hunfold : ∀ U, @UnfoldingCheckDescends (henv.params U)) :
    Cancel env ↔ StrengtheningKripke.TypedFront env :=
  ⟨fun hc => ((cancel_iff_typedFront_and_elim henv heq hRules hField hunfold).mp hc).1,
    fun hTF => (cancel_iff_typedFront_and_elim henv heq hRules hField hunfold).mpr
      ⟨hTF, ElimFrontN.of_generic henv hGen⟩⟩

/-- Typing strengthening itself, in the same terms. -/
theorem strengthening_iff_typedFront_final (henv : env.WF) (heq : env.HasCanonicalEq)
    (hGen : GenericTypesTyped₀ env) (hRules : GenericRulesTyped₀ env)
    (hField : ProjFieldFrontPropN env)
    (hunfold : ∀ U, @UnfoldingCheckDescends (henv.params U)) :
    env.Strengthening ↔ StrengtheningKripke.TypedFront env :=
  (strengthening_iff_cancel henv).trans
    (cancel_iff_typedFront_final henv heq hGen hRules hField hunfold)

end Lean4Lean.VEnv.StrengtheningFinal
