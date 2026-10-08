import Lean4Lean.Theory.Typing.NativeConstructorRigidity
import Lean4Lean.Theory.Typing.QuotPrefixReduction
import Batteries.Tactic.OpenPrivate
import Lean4Lean.Theory.Typing.NativeRecursorRegistration
import Lean4Lean.Theory.Inductive.NativeConstructorCoverage
import Lean4Lean.Theory.Inductive.CaseRuleUniqueness
import Lean4Lean.Theory.Typing.NativeRuleRegistration
import Lean4Lean.Theory.Typing.PatternCaptures
import Lean4Lean.Theory.Typing.Pattern
import Lean4Lean.Theory.Typing.DefinitionRegistryInstallation
import Lean4Lean.Theory.Typing.NativeRegistryInstallation
import Lean4Lean.Theory.Typing.Strong
import Lean4Lean.Theory.Typing.EnvLemmas
import Lean4Lean.Theory.Inductive.CaseRegistration
import Lean4Lean.Theory.Inductive.NativeRecursorData
import Lean4Lean.Theory.Inductive.CaseReductionData
import Lean4Lean.Theory.DeclarationData
import Lean4Lean.Theory.Typing.NativeCompiledRegistration
import Lean4Lean.Theory.Typing.CanonicalRegistryMetadata
import Lean4Lean.Theory.Quot
import Lean4Lean.Theory.Inductive.Formation
import Lean4Lean.Theory.Typing.QuotPatternTyping
import Lean4Lean.Theory.Typing.NativeConstructorUniqueness
import Lean4Lean.Theory.Typing.NativeMajorFamily
import Lean4Lean.Theory.Typing.DefinitionPatterns
import Lean4Lean.Theory.Typing.Injectivity
import Lean4Lean.Theory.Typing.CaseReduction

/-! Structure majors of registered case eliminators.

A case schema is registered (`VEnv.WF'.inductEliminators`) over a base
environment that is only required to agree with the current one on its
equations and to contain the certified declaration's constants. Nothing ties
the certified declaration to the projection metadata already registered for
the same family names. The resulting gap is genuine: the confluence of the
full reduction fails without the coherence hypothesis below.

Counterexample. Start from the empty environment and register, by
`inductProjections` over the axioms `S : Type` and `S.a : S`, the structure
`structure S : Type where a ::` (one constructor `S.a`, no parameters, no
fields). Add the axiom `S.b : S`, and register by `inductEliminators`, over
the empty base, the case schema of `inductive S : Type | b : S`. Every premise
holds: the schema is certified over the empty base, the environment contains
the constants `S` and `S.b` at that declaration's values, no equation was
added, the schema needs no projection names, and its key is fresh. In a
context with a motive `m : S → Type` and a minor `x : m S.b`, the case
application `elim S (m, x) S.b` computes to `x`, while structure eta gives
`S.b ≡ S.a`, so the same application is definitionally equal to
`elim S (m, x) S.a`, which has no rule and no reduct other than eta
re-expansions; `x` and it are not normally equal, and proof irrelevance does
not apply at `Type`. Hence `IsDefEq.full_church_rosser` is false for this
well-formed environment, and the case-schema structure-major fact needs
`VEnv.EliminatorsCoherent`.

Decision (2026-10-07): this was a specification defect. `inductEliminators`
now requires `VInductDecl.ProjectionsCoherent` (Theory/Typing/Env.lean), which
excludes the example above, and `VEnv.WF.eliminatorsCoherent`
(EliminatorCoherenceOfWF.lean) derives `VEnv.EliminatorsCoherent` from
`VEnv.WF`. No producer in the verified pipeline registers schemas for foreign
projection metadata: `Certified.register_after_constructors` proves the premise
from freshness, and `CheckingEnv.Valid.registerCases` takes it. -/

namespace Lean4Lean.InductiveSignature.CaseSchema
open VExpr
open private reduction_head_app reduction_head_mkApps restoration_vars view_constructor_external
  from Lean4Lean.Theory.Inductive.CaseReductionLemmas

end Lean4Lean.InductiveSignature.CaseSchema

namespace Lean4Lean.VEnv
open InductiveSignature CaseSchema VExpr
set_option linter.unusedSectionVars false

variable {env : VEnv}

/-- Every registered case eliminator is certified by a source declaration
whose constants are present and which owns the projection metadata of its
original families. It follows from well-formedness (`VEnv.WF.eliminatorsCoherent`). Nested containers need no premise: they
are certified installations, whose projection metadata is coherent in every
well-formed environment. -/
def EliminatorsCoherent (env : VEnv) : Prop :=
  ∀ key schema, env.eliminators key schema → ∃ base source block,
    base ≤ env ∧ schema.Certified base source block ∧
    (∀ value ∈ block.types ++ block.ctors, env.constants value.name = some value.toVConstant) ∧
    ∀ type ∈ source.types, ∀ info, env.projections type.name info →
      (⟨type.name, info⟩ : VProjectionEntry) ∈ source.projectionEntries

theorem CaseStep.generated (H : CaseStep env U Γ rule levels arguments) :
    ∃ block schema owner, env.eliminators block schema ∧ schema.Generates block owner rule := by
  cases H with
  | iota hl hg => exact ⟨_, _, _, hl, hg⟩

private theorem instL_wrapForalls'' (ds : List VExpr) (body : VExpr) (packed : List VLevel) :
    (VExpr.wrapForalls ds body).instL packed =
      VExpr.wrapForalls (ds.map (·.instL packed)) (body.instL packed) := by
  induction ds with
  | nil => rfl
  | cons d ds ih => simp only [VExpr.wrapForalls, List.foldr_cons, List.map_cons, VExpr.instL] at ih ⊢; rw [ih]

end Lean4Lean.VEnv
