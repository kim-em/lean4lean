import Lean4Lean.Theory.Inductive.Compilation
import Lean4Lean.Theory.Inductive.CaseSchema
import Lean4Lean.Theory.Inductive.CompilationNames

/-! The schema registry uses the same finite compilation evidence as native
inductive installation. No case types or equations are supplied by a caller.

Registration additionally certifies `CaseSchema.ProjNamesRegistered`: the
schema's generic type and generic equations project only out of structures
registered (as projections) in the environment at registration time. This is
an obligation on the producer of a registration (`VEnv.WF'.inductEliminators`),
not a consequence of `Certified`: the normalized index telescopes and recursive
shapes are checked in the expanded environment, whose projection table may
contain never-installed auxiliary structure families. -/

namespace Lean4Lean

namespace VExpr

/-- Every projection type name of the term satisfies `ok`. -/
def ProjNamesOK (ok : Name → Prop) : VExpr → Prop
  | .bvar _ | .sort _ | .const .. | .elim .. => True
  | .app f a | .lam f a | .forallE f a => f.ProjNamesOK ok ∧ a.ProjNamesOK ok
  | .proj n _ e => ok n ∧ e.ProjNamesOK ok

theorem ProjNamesOK.mono {ok ok' : Name → Prop} (hok : ∀ s, ok s → ok' s) :
    ∀ {e : VExpr}, e.ProjNamesOK ok → e.ProjNamesOK ok'
  | .bvar _, _ | .sort _, _ | .const .., _ | .elim .., _ => trivial
  | .app _ _, h | .lam _ _, h | .forallE _ _, h => ⟨ProjNamesOK.mono hok h.1, ProjNamesOK.mono hok h.2⟩
  | .proj _ _ _, h => ⟨hok _ h.1, ProjNamesOK.mono hok h.2⟩

end VExpr

namespace InductiveSignature.CaseSchema

/-- The generic type and generic equations (at registry key `key`) of the
schema project only out of structures registered in `env`. -/
def ProjNamesRegistered (schema : CaseSchema) (env : VEnv) (key : Name) : Prop :=
  (∀ owner type, schema.genericType owner = some type →
    type.ProjNamesOK fun S => ∃ info, env.projections S info) ∧
  (∀ owner rules, schema.genericEquations key owner = some rules → ∀ df ∈ rules,
    df.lhs.ProjNamesOK (fun S => ∃ info, env.projections S info) ∧
    df.rhs.ProjNamesOK (fun S => ∃ info, env.projections S info) ∧
    df.type.ProjNamesOK (fun S => ∃ info, env.projections S info))

/-- Registration of projections is monotone along environment extension. -/
theorem ProjNamesRegistered.mono {schema : CaseSchema} {env env' : VEnv}
    (H : schema.ProjNamesRegistered env key) (hle : env ≤ env') :
    schema.ProjNamesRegistered env' key := by
  have hok : ∀ S, (∃ info, env.projections S info) → ∃ info, env'.projections S info :=
    fun _ ⟨info, h⟩ => ⟨info, hle.projections h⟩
  refine ⟨fun owner type h => (H.1 owner type h).mono hok, fun owner rules h df hdf => ?_⟩
  obtain ⟨hl, hr, ht⟩ := H.2 owner rules h df hdf
  exact ⟨hl.mono hok, hr.mono hok, ht.mono hok⟩

/-- The abstract registry entry is determined by the same normalized
signature and restoration data as the native generated block. -/
def ofCompilation (source : VInductDecl) (signature : InductiveSignature)
    (auxiliaries : List ContainerSpecialization) : CaseSchema where
  originalFamilies := source.types.map (·.name)
  signature := signature
  restoration := compilationRestoration source auxiliaries

/-- Retain the normalized signature and exact restoration of one finite
compilation. Concrete recursor checking is not needed to register its abstract
case schemas once the source constructors and expanded formation are checked:
the certificate is the case part `CaseCompilationData` of a compilation, which
fixes everything the eliminator rules read and nothing about the generated
native recursors. -/
def Certified (schema : CaseSchema) (base : VEnv)
    (source : VInductDecl) (block : VInductBlock) : Prop :=
  ∃ expanded, ∃ auxiliaries,
    CaseCompilationData base source expanded schema.signature auxiliaries block ∧
    CertifiedSpecializations base auxiliaries ∧
    schema.restoration = compilationRestoration source auxiliaries ∧
    schema.originalFamilies = source.types.map (·.name) ∧
    RecursorNamesFresh base source expanded auxiliaries

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
  ⟨expanded, auxiliaries, H.toCaseCompilationData, hprior, rfl, rfl, H.recursorNamesFresh⟩

theorem ofCaseCompilation_certified {s : InductiveSignature}
    (H : CaseCompilationData base source expanded s auxiliaries block)
    (hprior : CertifiedSpecializations base auxiliaries)
    (hdisj : RecursorNamesFresh base source expanded auxiliaries) :
    (ofCompilation source s auxiliaries).Certified base source block :=
  ⟨expanded, auxiliaries, H, hprior, rfl, rfl, hdisj⟩

theorem Certified.originalFamilies_nodup {schema : CaseSchema}
    (H : schema.Certified base source block) : schema.originalFamilies.Nodup := by
  rcases H with ⟨expanded, auxiliaries, hdata, _, _, hnames, _⟩
  rw [hnames]
  exact source.typeNames_nodup hdata.sourceWF.2.1

end InductiveSignature.CaseSchema

end Lean4Lean
