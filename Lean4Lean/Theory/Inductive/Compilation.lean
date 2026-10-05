import Lean4Lean.Theory.Inductive.Formation
import Lean4Lean.Theory.Inductive.Restoration

/-! Finite compilation from certified parameter specializations.

Every leaf is a previously installed block with its own finite compilation
derivation. The chosen family fixes both the restoration heads and the entire
ordered constructor list. The normalized expanded signature determines every
recursor and equation; restoration accepts no independent equation templates.

This is the replacement specification. The legacy `CompilesTo` interface is
retained separately while its producers are migrated.
-/

namespace Lean4Lean
namespace InductiveSignature

/-- Select a family of a prior container and specialize its parameters.
Constructor names and their order are derived from this family. -/
structure ContainerSpecialization where
  container : VInductDecl
  family : Fin container.types.length
  auxiliary : Name
  levels : List VLevel
  arguments : List VExpr

namespace ContainerSpecialization

def source (a : ContainerSpecialization) : VInductiveType := a.container.types[a.family]

def constructorName (a : ContainerSpecialization) (ctor : VConstVal) : Name :=
  ctor.name.replacePrefix a.source.name a.auxiliary

/-- Only names obtained from the certified container can be restoration
targets. In particular callers cannot choose a replacement constructor body. -/
def heads (a : ContainerSpecialization) (uvars nparams : Nat) : List HeadSpecialization :=
  { auxiliary := a.auxiliary, uvars, nparams, target := a.source.name,
    levels := a.levels, arguments := a.arguments } ::
  a.source.ctors.map fun ctor =>
    { auxiliary := a.constructorName ctor, uvars, nparams, target := ctor.name,
      levels := a.levels, arguments := a.arguments }

/-- The direct auxiliary before recursive occurrences in its fields are
expanded. Its types are specialized from the prior source, never supplied by
the caller. Partial parameter telescopes fail explicitly. -/
def directFamily (a : ContainerSpecialization) (uvars : Nat)
    (params : List VExpr) : Option VInductiveType := do
  let type ← specializeType (a.source.type.instL a.levels) a.arguments
  let ctors ← a.source.ctors.mapM fun ctor => do
    let type ← specializeType (ctor.type.instL a.levels) a.arguments
    return ({
      name := a.constructorName ctor
      uvars := uvars
      type := VExpr.wrapForalls params type } : VConstVal)
  return {
    name := a.auxiliary
    uvars := uvars
    type := VExpr.wrapForalls params type
    numIndices := a.source.numIndices
    resultLevel := a.source.resultLevel.inst a.levels
    ctors := ctors }

/-- Scope, safety, and typing of an actual container parameter application.
The context contains the current block's common parameters; the environment
contains its original headers, but no current recursors or equations. -/
def WellFormed (a : ContainerSpecialization) (envTypes : VEnv)
    (source : VInductDecl) (params : List VExpr) : Prop :=
  a.arguments.length = a.container.nparams ∧
  (∀ arg ∈ a.arguments, arg.ClosedN source.nparams) ∧
  a.levels.length = a.container.uvars ∧
  (∀ level ∈ a.levels, level.WF source.uvars) ∧
  (source.isUnsafe = true ∨ a.container.isUnsafe = false) ∧
  ∃ type, envTypes.HasType source.uvars params.reverse
    (VExpr.mkApps (.const a.source.name a.levels) a.arguments) type

end ContainerSpecialization

/-- Restoration is fixed by the ordered finite specialization list.
The ordinary case is exactly the empty list and the identity restoration. -/
def compilationRestoration (source : VInductDecl)
    (auxiliaries : List ContainerSpecialization) : Restoration where
  heads := auxiliaries.flatMap fun a => a.heads source.uvars source.nparams
  recursors := auxiliaries.zipIdx.map fun (a, i) =>
    (a.auxiliary.str "rec", (((source.types.head?).map (fun t : VInductiveType => t.name)).getD (default : Name)).str "rec" |>.appendIndexAfter (i + 1))

/-- Restoration of a type is exact syntax followed by typed equality.
Typing takes place before any equation from this compilation is installed. -/
def RestoresType (r : Restoration) (env : VEnv) (uvars : Nat)
    (normalized source : VExpr) : Prop :=
  ∃ restored, r.expr normalized = some restored ∧
    env.IsDefEqU uvars [] restored source

/-- Ordered family and constructor correspondence. For an auxiliary, `source`
is the direct specialization generated from its certified container. -/
structure RestoresFamily (r : Restoration) (envTypes : VEnv) (uvars : Nat)
    (normalized source : VInductiveType) : Prop where
  name : normalized.name = source.name
  universes : normalized.uvars = source.uvars
  indices : normalized.numIndices = source.numIndices
  resultLevel : normalized.resultLevel ≈ source.resultLevel
  type : RestoresType r envTypes uvars normalized.type source.type
  constructors : List.Forall₂ (fun normalized source =>
    normalized.name = source.name ∧ normalized.uvars = source.uvars ∧
    RestoresType r envTypes uvars normalized.type source.type)
    normalized.ctors source.ctors

/-- The ordinary source model supplies the empty-restoration correspondence;
the global constructor list is split using the recorded family boundaries. -/
theorem Models.restores_empty {s : InductiveSignature} {env envTypes : VEnv}
    {decl : VInductDecl} (H : s.Models env decl)
    (htypes : env.addConstVals decl.typeConstants = some envTypes) :
    List.Forall₂ (RestoresFamily {} envTypes decl.uvars) s.declaration.types decl.types := by
  rcases H.constructors with ⟨oldTypes, holdTypes, hctors⟩
  have heq : oldTypes = envTypes := Option.some.inj (holdTypes.symm.trans htypes)
  subst oldTypes
  have hfamilies := H.families
  simp only [VInductDecl.constructorConstants] at hctors
  generalize s.declaration.types = left at hfamilies hctors ⊢
  generalize decl.types = right at hfamilies hctors ⊢
  induction hfamilies with
  | nil => exact .nil
  | @cons normalized source left right h htail ih =>
    simp only [List.flatMap_cons] at hctors
    have hlength : normalized.ctors.length = source.ctors.length := by
      have := congrArg List.length h.2.2.2.2.2
      simpa using this
    rcases (Lean4Lean.List.Forall₂.append_of_left hlength).mp hctors with ⟨hhead, hrest⟩
    refine .cons ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, ?_, ?_⟩ (ih hrest)
    · exact ⟨normalized.type, Restoration.expr_empty _,
        h.2.2.2.2.1.mono (VEnv.addConstVals_le htypes)⟩
    · exact Lean4Lean.List.Forall₂.imp (fun n t hc =>
        ⟨hc.1, hc.2.1, n.type, Restoration.expr_empty _, hc.2.2⟩) hhead

/-- A single expansion witness fixes formation and generated artifacts.
Every auxiliary family is covered, including semantically unused auxiliaries
introduced by erased concrete occurrences. -/
structure CompilationData (env : VEnv) (source expanded : VInductDecl)
    (s : InductiveSignature) (g : Instance s)
    (auxiliaries : List ContainerSpecialization) (block : VInductBlock) : Prop where
  sourceWF : VInductDecl.SourceWF env source
  sourceParameters : VInductDecl.SourceParameterWF env source
  expandedWF : VInductDecl.SourceWF env expanded
  /-- Lowering preserves every original family header literally; only new
  auxiliary headers may follow this prefix. -/
  headerPrefix : source.typeConstants = expanded.typeConstants.take source.types.length
  expandedFormation : VInductDecl.FormationWF env expanded
  model : s.Models env expanded
  uvars : expanded.uvars = source.uvars
  nparams : expanded.nparams = source.nparams
  safety : expanded.isUnsafe = source.isUnsafe
  restorationScoped : (compilationRestoration source auxiliaries).Scoped
  correspondence : ∃ envTypes direct,
    env.addConstVals source.typeConstants = some envTypes ∧
    auxiliaries.mapM (fun a => a.directFamily source.uvars s.params) = some direct ∧
    (∀ a ∈ auxiliaries, a.WellFormed envTypes source s.params) ∧
    List.Forall₂
      (RestoresFamily (compilationRestoration source auxiliaries) envTypes source.uvars)
      s.declaration.types (source.types ++ direct)
  admissible : ∃ envExpandedTypes,
    env.addConstVals expanded.typeConstants = some envExpandedTypes ∧
    g.Admissible envExpandedTypes
  recursiveTypesWF : ∃ envExpandedTypes,
    env.addConstVals expanded.typeConstants = some envExpandedTypes ∧
    g.RecursiveTypesWF envExpandedTypes
  recursorNames : ∀ owner, g.recursorName owner = s.families[owner].name.str "rec"
  generatedNames : ((expanded.typeConstants ++ expanded.constructorConstants ++
    g.recursors).map (·.name)).Nodup
  recursorsFresh : ∀ recursor ∈ g.recursors, env.constants recursor.name = none
  types : block.types = source.typeConstants
  ctors : block.ctors = source.constructorConstants
  projections : block.projections = source.projectionEntries
  recursors : g.restoredRecursors (compilationRestoration source auxiliaries) =
    some block.recursors
  equations : g.restoredEquations (compilationRestoration source auxiliaries) =
    some block.rules
  names : ((block.types ++ block.ctors ++ block.recursors).map (·.name)).Nodup

end InductiveSignature

mutual

/-- Shared finite ordinary/nested compilation. Empty specializations give
ordinary compilation. A nested container is certified recursively by this
same judgment, so arbitrary environment lookups cannot serve as provenance. -/
inductive CompiledInductive : VEnv → VInductDecl → VInductBlock → Prop
  | intro {env source expanded s g auxiliaries block} :
      InductiveSignature.CompilationData env source expanded s g auxiliaries block →
      CertifiedSpecializations env auxiliaries →
      CompiledInductive env source block
  | replay {base env source block} :
      CompiledInductive base source block →
      base ≤ env →
      block.WF env →
      CompiledInductive env source block

/-- Each selected container was installed below the original source
environment. Current headers, current recursors, and future blocks cannot
justify a specialization. The constructors make the provenance tree finite. -/
inductive CertifiedSpecializations : VEnv →
    List InductiveSignature.ContainerSpecialization → Prop
  | nil {env} : CertifiedSpecializations env []
  | cons {env a rest base block installed} :
      CompiledInductive base a.container block →
      block.WF base →
      VInductBlock.install base block = some installed →
      installed ≤ env →
      CertifiedSpecializations env rest →
      CertifiedSpecializations env (a :: rest)

end

/-- Replay retains the original finite derivation. Lowering-only names need
not remain fresh in the larger environment, since they are never installed
there; freshness and checking of the actual output are required explicitly. -/
theorem CompiledInductive.mono {base env source block}
    (H : CompiledInductive base source block) (hle : base ≤ env)
    (Hblock : block.WF env) : CompiledInductive env source block :=
  .replay H hle Hblock

/-- Canonical ordinary compilation is the zero-specialization case of the
same finite derivation. Formation and output checking are supplied by their
existing independent judgments. -/
theorem CompiledInductive.ordinary {env : VEnv} {source : VInductDecl}
    {block : VInductBlock}
    (Hsource : VInductDecl.SourceWF env source)
    (Hformation : VInductDecl.FormationWF env source)
    (Hcanonical : InductiveSignature.Compiles env source block)
    (Hblock : block.WF env)
    (htypes : block.types = source.typeConstants)
    (hctors : block.ctors = source.constructorConstants)
    (hprojections : block.projections = source.projectionEntries)
    (hnames : ((block.types ++ block.ctors ++ block.recursors).map (·.name)).Nodup) :
    CompiledInductive env source block := by
  rcases Hcanonical.generated with ⟨s, g, envTypes, Hmodel, hadded, Hadmissible, Hrec,
    hrecNames, hrecs, hrules⟩
  have hrestore : InductiveSignature.compilationRestoration source [] = {} := rfl
  have hfresh : ∀ recursor ∈ block.recursors, env.constants recursor.name = none := by
    rcases Hblock with ⟨typesEnv, ctorsEnv, recsEnv, ht, hc, hr, _⟩
    have hle := (VEnv.addConstVals_le ht).trans (VEnv.addConstVals_le hc)
    intro recursor hrec
    have hf := VEnv.addConstVals_names_fresh hr recursor hrec
    cases he : env.constants recursor.name with
    | none => rfl
    | some value =>
      have hv := hle.constants he
      simp only [VEnv.addProjections_constants] at hf
      rw [hv] at hf
      contradiction
  apply CompiledInductive.intro (expanded := source) (s := s) (g := g)
    (auxiliaries := []) ?_ .nil
  refine {
    sourceWF := Hsource
    sourceParameters := Hformation.sourceParameterWF
    expandedWF := Hsource
    headerPrefix := (List.take_of_length_le (by simp [VInductDecl.typeConstants])).symm
    expandedFormation := Hformation
    model := Hmodel
    uvars := rfl
    nparams := rfl
    safety := rfl
    restorationScoped := ?_
    correspondence := ?_
    admissible := ⟨envTypes, hadded, Hadmissible⟩
    recursiveTypesWF := ⟨envTypes, hadded, Hrec⟩
    recursorNames := hrecNames
    generatedNames := ?_
    recursorsFresh := ?_
    types := htypes
    ctors := hctors
    projections := hprojections
    recursors := ?_
    equations := ?_
    names := hnames }
  · simp [hrestore, InductiveSignature.Restoration.Scoped]
  · refine ⟨envTypes, [], hadded, rfl, ?_, ?_⟩
    · simp
    · simpa only [hrestore, List.append_nil] using Hmodel.restores_empty hadded
  · simpa only [← hrecs, ← htypes, ← hctors] using hnames
  · simpa only [← hrecs] using hfresh
  · simp [hrestore, hrecs]
  · simp [hrestore, hrules]

end Lean4Lean
