import Lean4Lean.Theory.Inductive.RecursorData
import Lean4Lean.Theory.Inductive.CaseReductionData
import Lean4Lean.Theory.DeclarationData
import Lean4Lean.Theory.Typing.RecursorRuleRegistration
import Lean4Lean.Theory.Typing.PatternCaptures
import Lean4Lean.Theory.Typing.Pattern
import Lean4Lean.Theory.Typing.DefinitionRegistryInstallation
import Lean4Lean.Theory.Quot
import Lean4Lean.Theory.Typing.RecursorRegistryInstallation
import Lean4Lean.Theory.Typing.Strong
import Lean4Lean.Theory.Typing.EnvLemmas
import Lean4Lean.Theory.Typing.EtaOpening
import Lean4Lean.Theory.Inductive.CaseReductionLemmas
import Lean4Lean.Theory.Inductive.RestorationNaturality
import Lean4Lean.Theory.Inductive.CaseProjections
import Lean4Lean.Theory.Inductive.CaseRegistration

/-! Scope for the concrete data machine from actual declaration history and
the original generic case headers. Generated equation scope is derived, rather
than supplied as an additional registry-correctness assumption. -/

namespace Lean4Lean.VEnv
open InductiveSignature

/-- The restoration table is the one checked by the original compilation. -/
theorem WF.eliminator_restoration_scoped {env : VEnv} {schema : CaseSchema}
    (formed : env.WF)
    (lookup : env.eliminators block schema) : schema.restoration.Scoped := by
  obtain ⟨base, source, generated, _, _, certified, _, _⟩ :=
    formed.eliminator_origin lookup
  obtain ⟨expanded, auxiliaries, compilation, _, restoration, _, _⟩ := certified
  rw [restoration]
  exact compilation.restorationScoped

end Lean4Lean.VEnv

namespace Lean4Lean.CanonicalDataHead
open InductiveSignature VEnv

end Lean4Lean.CanonicalDataHead
