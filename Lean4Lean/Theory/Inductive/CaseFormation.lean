import Lean4Lean.Theory.Inductive.Compilation
import Lean4Lean.Theory.Inductive.CaseSchema

/-! The schema registry uses the same finite compilation evidence as native
inductive installation. No case types or equations are supplied by a caller. -/

namespace Lean4Lean.InductiveSignature.CaseSchema

/-- The abstract registry entry is determined by the same normalized
signature and restoration data as the native generated block. -/
def ofCompilation (source : VInductDecl) (signature : InductiveSignature)
    (auxiliaries : List ContainerSpecialization) : CaseSchema where
  originalFamilies := source.types.map (·.name)
  signature := signature
  restoration := compilationRestoration source auxiliaries

/-- Retain the normalized signature and exact restoration of one finite
compilation. Concrete recursor checking is not needed to register its abstract
case schemas once the source constructors and expanded formation are checked. -/
def Certified (schema : CaseSchema) (base : VEnv)
    (source : VInductDecl) (block : VInductBlock) : Prop :=
  ∃ expanded, ∃ (g : Instance schema.signature), ∃ auxiliaries,
    CompilationData base source expanded schema.signature g auxiliaries block ∧
    CertifiedSpecializations base auxiliaries ∧
    schema.restoration = compilationRestoration source auxiliaries ∧
    schema.originalFamilies = source.types.map (·.name)

/-- Keys and native-family ownership are both fresh. Lowering auxiliaries do
not reserve native names: they are identified by their block and owner slot. -/
def Fresh (schema : CaseSchema) (env : VEnv) (key : Name) : Prop :=
  (∀ previous, ¬env.eliminators key previous) ∧
  ∀ previousKey previous, env.eliminators previousKey previous →
    List.Disjoint schema.originalFamilies previous.originalFamilies

theorem ofCompilation_certified
    {s : InductiveSignature} {g : Instance s}
    (H : CompilationData base source expanded s g auxiliaries block)
    (hprior : CertifiedSpecializations base auxiliaries) :
    (ofCompilation source s auxiliaries).Certified base source block :=
  ⟨expanded, g, auxiliaries, H, hprior, rfl, rfl⟩

theorem Certified.compiled {schema : CaseSchema}
    (H : schema.Certified base source block) :
    CompiledInductive base source block := by
  rcases H with ⟨expanded, g, auxiliaries, hdata, hprior, _⟩
  exact .intro hdata hprior

theorem Certified.originalFamilies_nodup {schema : CaseSchema}
    (H : schema.Certified base source block) : schema.originalFamilies.Nodup := by
  rcases H with ⟨expanded, g, auxiliaries, hdata, _, _, hnames⟩
  rw [hnames]
  exact source.typeNames_nodup hdata.sourceWF.2.1

end Lean4Lean.InductiveSignature.CaseSchema
