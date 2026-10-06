import Lean4Lean.Verify.Inductive.Context
import Lean4Lean.Verify.Inductive.Header.LoopInd
import Lean4Lean.Theory.Inductive.Normalization
namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel
namespace VerifyInductive
open InductiveSignature

/-- Close two definitionally equal dependent contexts around equally typed
bodies. This changes the chosen binder domains by typed equality. -/
theorem _root_.Lean4Lean.VEnv.IsDefEqCtx.closeForalls
    (H : VEnv.IsDefEqCtx env U [] left right)
    (Hbody : env.IsDefEq U left body body' (.sort bodyLevel)) :
    ∃ resultLevel, env.IsDefEq U []
      (VExpr.wrapForalls left.reverse body)
      (VExpr.wrapForalls right.reverse body') (.sort resultLevel) := by
  induction H generalizing body body' bodyLevel with
  | zero => exact ⟨bodyLevel, Hbody⟩
  | succ hctx hdom ih =>
    rcases ih (.forallEDF hdom Hbody) with ⟨level, hclosed⟩
    exact ⟨level, by simpa [List.reverse_cons, VExpr.wrapForalls_append, VExpr.wrapForalls] using hclosed⟩

/-- Replace an independently checked parameter prefix by the one shared
source prefix while preserving the selected index domains exactly. -/
theorem canonicalFamilyOfTelescope
    {env : VEnv} {U : Nat} {params ownParams indices : List VExpr}
    {source result exprType : VExpr} {resultLevel : VLevel}
    (henv : env.WF) (htype : env.IsType U [] source)
    (hnormalized : env.IsDefEq U [] source
      (VExpr.wrapForalls (ownParams ++ indices) result) exprType)
    (hparams : env.IsDefEqCtx U [] params.reverse ownParams.reverse)
    (hresult : env.IsDefEq U (indices.reverse ++ ownParams.reverse)
      result (.sort resultLevel) (.sort (.succ resultLevel))) :
    env.IsDefEqU U [] source
      (VExpr.wrapForalls (params ++ indices) (.sort resultLevel)) := by
  have hnormalizedType := htype.defeqU_l henv trivial ⟨_, hnormalized⟩
  have htelescope := VEnv.IsType.wrapForalls_inv henv trivial hnormalizedType
  obtain ⟨sortLevel, hwrapped⟩ := VExpr.wrapForalls_defeq
    (domains := ownParams ++ indices) (Γ := [])
    (by simpa using htelescope.1)
    (by simpa [List.reverse_append] using hresult)
  have hownType : env.IsType U []
      (VExpr.wrapForalls ownParams (VExpr.wrapForalls indices (.sort resultLevel))) := by
    simpa [VExpr.wrapForalls_append] using
      (show env.IsType U []
        (VExpr.wrapForalls (ownParams ++ indices) (.sort resultLevel)) from
        ⟨sortLevel, hwrapped.hasType.2⟩)
  obtain ⟨_, bodyLevel, hbody⟩ := VEnv.IsType.wrapForalls_inv henv trivial hownType
  have hbody' : env.HasType U ownParams.reverse
      (VExpr.wrapForalls indices (.sort resultLevel)) (.sort bodyLevel) := by
    simpa using hbody
  obtain ⟨canonicalLevel, hcanonical⟩ :=
    (hparams.symm henv.ordered).closeForalls hbody'
  refine VEnv.IsDefEqU.trans henv trivial
    (VEnv.IsDefEqU.trans henv trivial ⟨_, hnormalized⟩ ⟨_, hwrapped⟩) ?_
  simpa [List.reverse_reverse, VExpr.wrapForalls_append] using
    (show env.IsDefEqU U []
      (VExpr.wrapForalls ownParams.reverse.reverse
        (VExpr.wrapForalls indices (.sort resultLevel)))
      (VExpr.wrapForalls params.reverse.reverse
        (VExpr.wrapForalls indices (.sort resultLevel))) from
        ⟨.sort canonicalLevel, hcanonical⟩)

/-- Express each checked source family using the block's one shared parameter
telescope, keeping all choices at the original declaration universes. -/
theorem _root_.Lean4Lean.VInductDecl.TypeShape.canonicalFamily
    {env : VEnv} {decl : VInductDecl} {params : List VExpr} {family : VInductiveType}
    (H : decl.TypeShape env params family) (henv : env.WF)
    (htype : env.IsType decl.uvars [] family.type) :
    ∃ indices, indices.length = family.numIndices ∧
      env.IsDefEqU decl.uvars [] family.type
        (VExpr.wrapForalls (params ++ indices) (.sort family.resultLevel)) := by
  rcases H with ⟨normalized, ownParams, afterParams, indices, result, exprType,
    hnormalized, hparamsTake, hindicesTake, hparams, hresult⟩
  obtain ⟨hparamsRebuild, _⟩ := VExpr.takeForalls_rebuild hparamsTake
  obtain ⟨hindicesRebuild, hindicesLength⟩ := VExpr.takeForalls_rebuild hindicesTake
  have hnormalizedRebuild : normalized = VExpr.wrapForalls (ownParams ++ indices) result := by
    rw [hparamsRebuild, hindicesRebuild, VExpr.wrapForalls_append]
  rw [hnormalizedRebuild] at hnormalized
  exact ⟨indices, hindicesLength, canonicalFamilyOfTelescope henv htype hnormalized hparams hresult⟩

/-- A retained uniform positive normal form determines exactly the recursive
shape expected by the independent generator, using the shared family table. -/
theorem _root_.Lean4Lean.VInductDecl.UniformFieldNormalForm.recursiveShape
    {decl : VInductDecl} {s : InductiveSignature}
    (huvars : s.uvars = decl.uvars) (hparams : s.params.length = decl.nparams)
    (hnames : s.families.toList.map (·.name) = decl.types.map (·.name))
    (H : decl.UniformFieldNormalForm (VLevel.params decl.uvars) depth normalized) :
    normalized.SourceConstFree (s.families.toList.map (·.name)) ∨
      ∃ r : Recursive s.families.size,
        normalized = s.recursiveType depth r ∧
        (∀ domain ∈ r.binders, domain.SourceConstFree (s.families.toList.map (·.name))) ∧
        (∀ index ∈ r.indices, index.SourceConstFree (s.families.toList.map (·.name))) := by
  rcases H with hfree | ⟨domains, result, rfl, hdomains, hresult, sourceHead, hsourceHead, hhead⟩
  · exact .inl (by simpa [hnames] using hfree)
  rcases hresult with ⟨source, hsource, _, levels, hfn, hlevels, hargs, hparamsAt, hindices⟩
  have hlevelsEq : levels = VLevel.params decl.uvars :=
    (VExpr.const.inj (hfn.symm.trans hhead)).2
  subst levels
  change result.getAppFnArgs.1 = .const source.name (VLevel.params decl.uvars) at hfn
  change result.getAppFnArgs.2.take decl.nparams = decl.paramVars (depth + domains.length) at hparamsAt
  have hsourceName : source.name ∈ s.families.toList.map (·.name) := by
    rw [hnames]
    exact List.mem_map.mpr ⟨source, hsource, rfl⟩
  rcases List.mem_map.mp hsourceName with ⟨family, hfamily, hname⟩
  rcases List.mem_iff_getElem.mp hfamily with ⟨owner, howner, rfl⟩
  let r : Recursive s.families.size := {
    binders := domains
    target := ⟨owner, by simpa using howner⟩
    indices := result.getAppFnArgs.2.drop decl.nparams }
  refine .inr ⟨r, ?_, ?_, ?_⟩
  · unfold InductiveSignature.recursiveType InductiveSignature.familyApp
    dsimp only [r]
    have hname' : s.families[r.target].name = source.name := by simpa [r] using hname
    rw [huvars, hname']
    congr 1
    have hrebuild := VerifyInductive.VExpr.mkApps_getAppFnArgs result
    change VExpr.mkApps result.getAppFnArgs.1 result.getAppFnArgs.2 = result at hrebuild
    rw [hfn] at hrebuild
    have hparamVars : vars s.params.length (depth + domains.length) =
        decl.paramVars (depth + domains.length) := by
      simp [vars, VInductDecl.paramVars, hparams]
    rw [hparamVars, ← hparamsAt, List.take_append_drop]
    exact hrebuild.symm
  · intro domain hdomain
    simpa [hnames] using hdomains domain hdomain
  · intro index hindex
    simpa [hnames] using hindices index hindex

/-- Classification part of the per-field source signature model: an external
field normalizes to a source-free type, and a recursive field is
definitionally its generated recursive type with source-free binders and
indices. -/
def SignatureFieldClass (env : VEnv) (U : Nat) (s : InductiveSignature)
    (ctx : List VExpr) (depth : Nat) : Field s.families.size → Prop
  | .external type => s.isUnsafe = true ∨ ∃ normalized,
      env.IsDefEqU U ctx type normalized ∧
      normalized.SourceConstFree (s.families.toList.map (·.name))
  | .recursive type r =>
      env.IsDefEqU U ctx type (s.recursiveType depth r) ∧
      (s.isUnsafe = true ∨
        (∀ domain ∈ r.binders, domain.SourceConstFree (s.families.toList.map (·.name))) ∧
        (∀ index ∈ r.indices, index.SourceConstFree (s.families.toList.map (·.name))))

/-- Per-field part of the source signature model, indexed by the real prefix
context. Stored field domains remain exactly the source domains. Besides the
classification, every field's domain is definitionally a uniform positive
normal form at the source universes, independently of its classification. -/
def SignatureFieldModel (env : VEnv) (decl : VInductDecl) (s : InductiveSignature)
    (ctx : List VExpr) (depth : Nat) (field : Field s.families.size) : Prop :=
  SignatureFieldClass env decl.uvars s ctx depth field ∧
  (s.isUnsafe = true ∨ ∃ normalized,
    env.IsDefEqU decl.uvars ctx (s.fieldType depth field) normalized ∧
    decl.UniformFieldNormalForm (VLevel.params decl.uvars) depth normalized)

/-- Select the independent field classification from the successful source
check, retaining the exact domain in both external and recursive cases. -/
theorem signatureFieldOfUniform
    {decl : VInductDecl} {s : InductiveSignature}
    (huvars : s.uvars = decl.uvars) (hparams : s.params.length = decl.nparams)
    (hnames : s.families.toList.map (·.name) = decl.types.map (·.name))
    (hsafety : s.isUnsafe = decl.isUnsafe)
    (H : decl.isUnsafe = true ∨ ∃ normalized,
      env.IsDefEqU decl.uvars ctx domain normalized ∧
      decl.UniformFieldNormalForm (VLevel.params decl.uvars) depth normalized) :
    ∃ field : Field s.families.size, s.fieldType depth field = domain ∧
      SignatureFieldModel env decl s ctx depth field := by
  rcases H with hunsafe | ⟨normalized, hnormal, hshape⟩
  · exact ⟨.external domain, rfl, .inl (hsafety.trans hunsafe), .inl (hsafety.trans hunsafe)⟩
  have hpositive : ∀ field : Field s.families.size, s.fieldType depth field = domain →
      s.isUnsafe = true ∨ ∃ normalized,
        env.IsDefEqU decl.uvars ctx (s.fieldType depth field) normalized ∧
        decl.UniformFieldNormalForm (VLevel.params decl.uvars) depth normalized :=
    fun _ hfield => .inr ⟨normalized, hfield ▸ hnormal, hshape⟩
  rcases hshape.recursiveShape huvars hparams hnames with hfree | ⟨r, hr, hdomains, hindices⟩
  · exact ⟨.external domain, rfl, .inr ⟨normalized, hnormal, hfree⟩, hpositive _ rfl⟩
  · have hpos := hpositive (.recursive domain r) rfl
    rw [hr] at hnormal
    exact ⟨.recursive domain r, rfl, ⟨hnormal, .inr ⟨hdomains, hindices⟩⟩, hpos⟩

/-- Fold the original telescope in binder order. Classification does not
replace a domain, so every later field keeps exactly its source context. -/
theorem signatureFieldsOfUniform
    {decl : VInductDecl} {s : InductiveSignature}
    (huvars : s.uvars = decl.uvars) (hparams : s.params.length = decl.nparams)
    (hnames : s.families.toList.map (·.name) = decl.types.map (·.name))
    (hsafety : s.isUnsafe = decl.isUnsafe)
    {domains : List VExpr}
    (H : ∀ i (hi : i < domains.length),
      decl.isUnsafe = true ∨ ∃ normalized,
        env.IsDefEqU decl.uvars ((domains.take i).reverse ++ ctx) domains[i] normalized ∧
        decl.UniformFieldNormalForm (VLevel.params decl.uvars) (depth + i) normalized) :
    ∃ fields : List (Field s.families.size),
      fields.map (s.fieldType 0) = domains ∧
      ∀ i (hi : i < fields.length),
        SignatureFieldModel env decl s ((domains.take i).reverse ++ ctx)
          (depth + i) fields[i] := by
  induction domains generalizing ctx depth with
  | nil => exact ⟨[], rfl, by intro i hi; simp at hi⟩
  | cons domain domains ih =>
    have hhead := H 0 (by simp)
    simp only [List.take_zero, List.reverse_nil, List.nil_append, List.getElem_cons_zero,
      Nat.add_zero] at hhead
    obtain ⟨field, hfield, hmodel⟩ := signatureFieldOfUniform huvars hparams hnames hsafety hhead
    have htail : ∀ i (hi : i < domains.length),
        decl.isUnsafe = true ∨ ∃ normalized,
          env.IsDefEqU decl.uvars ((domains.take i).reverse ++ (domain :: ctx)) domains[i] normalized ∧
          decl.UniformFieldNormalForm (VLevel.params decl.uvars) (depth + 1 + i) normalized := by
      intro i hi
      have hnext := H (Nat.succ i) (by simpa using hi)
      simp only [List.getElem_cons_succ] at hnext
      simpa [List.take_succ_cons, List.reverse_cons, List.append_assoc,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hnext
    obtain ⟨fields, hfields, hmodels⟩ := ih htail
    refine ⟨field :: fields, ?_, ?_⟩
    · simp only [List.map_cons, hfields]
      change s.fieldType depth field :: domains = domain :: domains
      rw [hfield]
    · intro i hi
      cases i with
      | zero => simpa using hmodel
      | succ i =>
        have hi' : i < fields.length := by simpa using hi
        simpa [List.take_succ_cons, List.reverse_cons, List.append_assoc,
          Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hmodels i hi'

theorem _root_.Lean4Lean.VInductDecl.UniformCtorTail.defeqCtx
    (H : VInductDecl.UniformCtorTail env decl target levels ctx₁ depth tail)
    (henv : env.Ordered) (hctx : env.IsDefEqCtx decl.uvars base ctx₁ ctx₂) :
    decl.UniformCtorTail env target levels ctx₂ depth tail := by
  induction H generalizing ctx₂ with
  | result hresult hhead => exact .result hresult hhead
  | field htype hfield _ ih =>
    obtain ⟨u, hu⟩ := htype
    refine .field ⟨u, hu.defeqDFC henv hctx⟩ ?_ (ih (.succ hctx hu))
    rcases hfield with hunsafe | ⟨normalized, hnormal, hshape⟩
    · exact .inl hunsafe
    · exact .inr ⟨normalized, hnormal.defeqDFC henv hctx, hshape⟩

theorem signatureFieldTypes_eq_map (s : InductiveSignature)
    (ctor : Constructor s.families.size) :
    s.fieldTypes ctor = ctor.fields.map (s.fieldType 0) := by
  change ctor.fields.zipIdx.map ((s.fieldType 0) ∘ Prod.fst) = _
  rw [← List.map_map]
  simp

/-- Build a constructor's generator data from the retained literal source
telescope. Field selection preserves every domain, and its semantic model
uses exactly the preceding domains in that same telescope. -/
theorem signatureConstructorOfUniform
    {decl : VInductDecl} {s : InductiveSignature} {target : VInductiveType}
    (huvars : s.uvars = decl.uvars) (hparams : s.params.length = decl.nparams)
    (hnames : s.families.toList.map (·.name) = decl.types.map (·.name))
    (hsafety : s.isUnsafe = decl.isUnsafe)
    (owner : Fin s.families.size) (howner : s.families[owner].name = target.name)
    (ctorName : Name)
    (H : decl.UniformCtorTail env target (VLevel.params decl.uvars)
      s.params.reverse 0 tail) :
    ∃ ctor : Constructor s.families.size,
      ctor.name = ctorName ∧ ctor.owner = owner ∧
      VExpr.wrapForalls s.params tail = s.constructorType ctor ∧
      ∀ i (hi : i < ctor.fields.length),
        SignatureFieldModel env decl s
          (((s.fieldTypes ctor).take i).reverse ++ s.params.reverse) i ctor.fields[i] := by
  obtain ⟨domains, result, rfl, hresult, hhead, hfields⟩ := H.telescope
  obtain ⟨fields, hfieldsEq, hmodels⟩ := signatureFieldsOfUniform
    huvars hparams hnames hsafety (fun i hi => (hfields i hi).2)
  have hlength : fields.length = domains.length := by
    simpa using congrArg List.length hfieldsEq
  let ctor : Constructor s.families.size := {
    name := ctorName
    owner := owner
    fields := fields
    indices := result.getAppFnArgs.2.drop decl.nparams }
  have hfieldTypes : s.fieldTypes ctor = domains := by
    rw [signatureFieldTypes_eq_map]
    exact hfieldsEq
  refine ⟨ctor, rfl, rfl, ?_, ?_⟩
  · unfold InductiveSignature.constructorType
    rw [VExpr.wrapForalls_append, hfieldTypes]
    congr 2
    rcases hresult with ⟨family, hfamily, htarget, levels, hfn, hlevels, hargs, hparamAt, hindices⟩
    change result.getAppFnArgs.2.take decl.nparams = decl.paramVars (0 + domains.length) at hparamAt
    simp only [Nat.zero_add] at hparamAt
    have hrebuild := VExpr.mkApps_getAppFnArgs result
    change VExpr.mkApps result.getAppFnArgs.1 result.getAppFnArgs.2 = result at hrebuild
    rw [hhead] at hrebuild
    unfold InductiveSignature.familyApp
    dsimp only [ctor]
    rw [howner, huvars, hlength]
    have hparamVars : vars s.params.length domains.length = decl.paramVars domains.length := by
      simp [vars, VInductDecl.paramVars, hparams]
    rw [hparamVars, ← hparamAt, List.take_append_drop]
    exact hrebuild.symm
  · intro i hi
    rw [hfieldTypes]
    simpa only [Nat.zero_add] using hmodels i hi

namespace checkInductiveTypes.loopInd

/-- Select one normalized source header per family, before adding the fresh
recursor universe. The family table and later generation share this choice. -/
noncomputable def MaterializedHeaderResult.signatureFamily
    (H : MaterializedHeaderResult env Us Δ stats decl depth)
    (i : Nat) (hi : i < decl.types.length) : InductiveSignature.Family :=
  let source := Classical.choose (H.normalizedShapes i hi)
  { name := decl.types[i].name
    indices := source.indices
    resultLevel := decl.types[i].resultLevel }

noncomputable def MaterializedHeaderResult.signatureFamilies
    (H : MaterializedHeaderResult env Us Δ stats decl depth) :
    Array InductiveSignature.Family :=
  Array.ofFn fun i : Fin decl.types.length => H.signatureFamily i.val i.isLt

@[simp] theorem MaterializedHeaderResult.signatureFamilies_size
    (H : MaterializedHeaderResult env Us Δ stats decl depth) :
    H.signatureFamilies.size = decl.types.length := by
  simp [signatureFamilies]

@[simp] theorem MaterializedHeaderResult.signatureFamilies_at
    (H : MaterializedHeaderResult env Us Δ stats decl depth)
    (i : Nat) (hi : i < decl.types.length) :
    H.signatureFamilies[i]'(by simpa using hi) = H.signatureFamily i hi := by
  simp [signatureFamilies]

/-- The chosen index domains are those of the same retained normalized source
header that proves this family's model; their universe context is unchanged. -/
theorem MaterializedHeaderResult.signatureFamily_model
    (H : MaterializedHeaderResult env Us Δ stats decl depth)
    (henv : env.WF)
    (i : Nat) (hi : i < decl.types.length)
    (htype : env.IsType decl.uvars [] decl.types[i].type) :
    (H.signatureFamily i hi).name = decl.types[i].name ∧
    (H.signatureFamily i hi).indices.length = decl.types[i].numIndices ∧
    (H.signatureFamily i hi).resultLevel = decl.types[i].resultLevel ∧
    env.IsDefEqU decl.uvars [] decl.types[i].type
      (VExpr.wrapForalls (H.headers.params ++ (H.signatureFamily i hi).indices)
        (.sort (H.signatureFamily i hi).resultLevel)) := by
  let source := Classical.choose (H.normalizedShapes i hi)
  obtain ⟨result, exprType, hnormalized, hresult⟩ :=
    Classical.choose_spec (H.normalizedShapes i hi)
  refine ⟨rfl, source.indexCount, rfl, ?_⟩
  have hcanonical := canonicalFamilyOfTelescope henv
    (by simpa [H.uvars] using htype) hnormalized source.parameters hresult
  simpa [signatureFamily, source, H.uvars] using hcanonical

theorem MaterializedHeaderResult.signatureFamilies_names
    (H : MaterializedHeaderResult env Us Δ stats decl depth) :
    H.signatureFamilies.toList.map (·.name) = decl.types.map (·.name) := by
  apply List.ext_getElem
  · simp
  · intro i hleft hright
    have hi : i < decl.types.length := by simpa using hright
    simp [signatureFamilies, signatureFamily]

/-- The common source parameter list has exactly the arity checked by the
executable parameter cache. -/
theorem MaterializedHeaderResult.signatureParams_length
    (H : MaterializedHeaderResult env Us Δ stats decl depth) :
    H.headers.params.length = decl.nparams := by
  have hcontext := H.paramsContext.length_eq
  have hcached := checkInductiveTypes.loopType.CachedParameterDecl.forall₂_toCtx_length H.cachedScope
  have hscope := List.Forall₂.length_eq H.cachedScope
  have htranslated := List.Forall₂.length_eq H.params
  simp only [List.length_reverse, Array.length_toList,
    VInductDecl.paramVars, List.length_map, List.length_reverse, List.length_range] at *
  omega

/-- Shared source-universe family and parameter choices. Constructor fields
are filled from the checked source-tail certificates over this same table. -/
noncomputable def MaterializedHeaderResult.signatureHeader
    (H : MaterializedHeaderResult env Us Δ stats decl depth) : InductiveSignature where
  uvars := decl.uvars
  params := H.headers.params
  families := H.signatureFamilies
  constructors := #[]
  isUnsafe := decl.isUnsafe

end checkInductiveTypes.loopInd

end VerifyInductive
end Lean4Lean
