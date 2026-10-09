import Lean4Lean.Theory.Typing.Strengthening.Exposure
import Lean4Lean.Theory.Typing.Strengthening.SpineExposure

/-! # Typing strengthening: the environment-level closures

The two closures that `cancel_iff_typedFront_of` (`Exposure.lean`) assumes, reduced to
environment-level typing facts about closed, environment-determined terms
(`docs/inductives/STRENGTHENING_E_LOG.md`):

* `ElimFrontN` follows from `GenericTypesTyped₀`: the generic type of every registered case
  schema is typed at a sort in the empty context at the generic universes (`elimDF` takes its
  specialization's sort typing as a premise in every context, so a typed eliminator above gives
  nothing below without it). The closed rule typings of `CaseStep.iota` likewise follow from
  `GenericRulesTyped₀`.
* `ProjFrontN` follows from `EtaReplay` (spine exposure of the major's type) and
  `ProjFieldFrontN` (`SpineExposure.lean`), itself reduced to its instances at structures whose
  sort is not never-zero (`ProjFieldFrontPropN`).

`cancel_iff_typedFront_of_etaReplay` is the assembled biconditional. -/

namespace Lean4Lean.VEnv.StrengtheningClosures
open VExpr VEnv.StrengtheningTypingFront VEnv.StrengtheningReplay VEnv.StrengtheningExposure
  VEnv.StrengtheningSpineExposure InductiveSignature

variable {env : VEnv} {U : Nat} {block : Name} {levels : List VLevel} {target : VLevel}

/-! ## The eliminator closure -/

/-- OPEN (environment lemma): the generic type of every registered case schema, at every owner
slot, is typed at a sort in the empty context at the generic universes. The registration
certificate records closedness (`WF.eliminator_genericType_closed`) and the formation data of
the compilation, not this typing. -/
def GenericTypesTyped₀ (env : VEnv) : Prop :=
  ∀ ⦃block : Name⦄ ⦃schema : CaseSchema⦄ ⦃owner : Fin schema.signature.families.size⦄ ⦃type⦄,
    env.eliminators block schema → schema.genericType owner = some type →
    ∃ l, env.HasType schema.genericUvars [] type (.sort l)

/-- Every permitted specialization of a generic type typed at the generic universes is typed. -/
theorem GenericTypesTyped.of_generic (H : GenericTypesTyped₀ env) : GenericTypesTyped env := by
  intro U block schema owner type target levels hl ht hp
  obtain ⟨l, h⟩ := H hl ht
  have := h.instL hp.packedWF
  simp only [List.map_nil, VExpr.instL] at this
  exact ⟨_, this⟩

theorem ElimFrontN.of_generic (henv : env.WF) (H : GenericTypesTyped₀ env) : ElimFrontN env :=
  ElimFrontN.of_genericTyped henv (GenericTypesTyped.of_generic H)

/-- OPEN (environment lemma): the generic case equations of every registered schema are typed
in the empty context at the generic universes. -/
def GenericRulesTyped₀ (env : VEnv) : Prop :=
  ∀ ⦃block : Name⦄ ⦃schema : CaseSchema⦄ ⦃owner : Fin schema.signature.families.size⦄ ⦃rules df⦄,
    env.eliminators block schema → schema.genericEquations block owner = some rules →
    df ∈ rules →
    env.HasType schema.genericUvars [] df.lhs df.type ∧
      env.HasType schema.genericUvars [] df.rhs df.type

/-- The closed typing premises of `CaseStep.iota` (and `IsDefEq.elimIota`) at every permitted
specialization, in every context: closed typings in `[]` specialize by `instL` and weaken by
`weak0`. -/
theorem GenericRulesTyped₀.caseStep_premises (henv : env.WF) (H : GenericRulesTyped₀ env)
    {schema : CaseSchema} {owner : Fin schema.signature.families.size}
    {rule : CaseSchema.AppliedRule} (hl : env.eliminators block schema)
    (hgen : schema.Generates block owner rule) (hp : schema.Permission U owner levels target)
    (Γ : List VExpr) :
    env.HasType U Γ (rule.equation.lhs.instL (target :: levels))
      (rule.equation.type.instL (target :: levels)) ∧
    env.HasType U Γ (rule.equation.rhs.instL (target :: levels))
      (rule.equation.type.instL (target :: levels)) := by
  obtain ⟨rules, hrules, hmem, -⟩ := hgen
  obtain ⟨h1, h2⟩ := H hl hrules hmem
  have h1' := h1.instL hp.packedWF
  have h2' := h2.instL hp.packedWF
  simp only [List.map_nil] at h1' h2'
  exact ⟨h1'.weak0 henv.ordered, h2'.weak0 henv.ordered⟩

/-! ## The assembled biconditional -/

/-- `Cancel ↔ TypedFront` from the replay obligation (`EtaReplay`), the generic-type typing
(`GenericTypesTyped`, discharged by `GenericTypesTyped₀`) and the field-type closure
(`ProjFieldFrontN`). -/
theorem cancel_iff_typedFront_of_etaReplay (henv : env.WF) (heq : env.HasCanonicalEq)
    (H : ∀ U, @EtaReplay (henv.params U)) (hGen : GenericTypesTyped env)
    (hField : ProjFieldFrontN env) :
    Cancel env ↔ StrengtheningKripke.TypedFront env :=
  cancel_iff_typedFront_of henv heq H (ProjFrontN.of_etaReplay henv heq H hField)
    (ElimFrontN.of_genericTyped henv hGen)

/-- The same with the two environment-level obligations in their sharpest form: the generic
types typed at the generic universes, and the field-type closure at structures whose sort is not
never-zero (outside `Prop` it is a library fact, `projField_of_neverZero`). -/
theorem cancel_iff_typedFront_of_etaReplay₀ (henv : env.WF) (heq : env.HasCanonicalEq)
    (H : ∀ U, @EtaReplay (henv.params U)) (hGen : GenericTypesTyped₀ env)
    (hField : ProjFieldFrontPropN env) :
    Cancel env ↔ StrengtheningKripke.TypedFront env :=
  cancel_iff_typedFront_of_etaReplay henv heq H (GenericTypesTyped.of_generic hGen)
    (ProjFieldFrontN.of_notNeverZero henv hField)

end Lean4Lean.VEnv.StrengtheningClosures
