import Lean4Lean.Verify.Inductive.Nested.Opening

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

open private Lean.Kernel.Environment.add from Lean.Environment

namespace VerifyInductive

/-- Exact rule-level restoration contract used by `processRec`. -/
structure RuleRestoration
    (result : Lean4Lean.ElimNestedInductive.Result)
    (env : Environment) (auxRec : NameMap Name)
    (oldRecName newRecName : Name)
    (oldRule newRule : RecursorRule) : Prop where
  ctor : newRule.ctor = if newRecName == oldRecName then oldRule.ctor
    else result.restoreCtorName env oldRule.ctor
  nfields : newRule.nfields = oldRule.nfields
  rhs : NestedRestoration result env auxRec oldRule.rhs newRule.rhs

theorem restoreRule_refines
    (result : Lean4Lean.ElimNestedInductive.Result)
    (env : Environment) (auxRec : NameMap Name)
    (oldRecName newRecName : Name) (rule : RecursorRule)
    (Htelescope : RestoreTelescope rule.rhs result.nparams) :
    RuleRestoration result env auxRec oldRecName newRecName rule
      (result.restoreRule env auxRec oldRecName newRecName rule) where
  ctor := rfl
  nfields := rfl
  rhs := restoreNested_refines result env auxRec rule.rhs Htelescope

inductive RulesRestoration
    (result : Lean4Lean.ElimNestedInductive.Result)
    (env : Environment) (auxRec : NameMap Name)
    (oldRecName newRecName : Name) :
    List RecursorRule → List RecursorRule → Prop
  | nil : RulesRestoration result env auxRec oldRecName newRecName [] []
  | cons : RuleRestoration result env auxRec oldRecName newRecName old new →
      RulesRestoration result env auxRec oldRecName newRecName olds news →
      RulesRestoration result env auxRec oldRecName newRecName
        (old :: olds) (new :: news)

theorem RulesRestoration.length
    (H : RulesRestoration result env auxRec oldRecName newRecName olds news) :
    news.length = olds.length := by
  induction H with
  | nil => rfl
  | cons _ _ ih => simp [ih]

theorem RulesRestoration.entry
    (H : RulesRestoration result env auxRec oldRecName newRecName olds news) :
    ∀ i (hold : i < olds.length) (hnew : i < news.length),
      RuleRestoration result env auxRec oldRecName newRecName
        olds[i] news[i] := by
  induction H with
  | nil =>
    intro i hold
    simp at hold
  | @cons old new olds news Hhead Htail ih =>
    intro i hold hnew
    cases i with
    | zero => simpa using Hhead
    | succ i => exact ih i (by simpa using hold) (by simpa using hnew)

theorem restoreRules_refines
    (result : Lean4Lean.ElimNestedInductive.Result)
    (env : Environment) (auxRec : NameMap Name)
    (oldRecName newRecName : Name) :
    ∀ rules,
      (∀ rule ∈ rules, RestoreTelescope rule.rhs result.nparams) →
      RulesRestoration result env auxRec oldRecName newRecName rules
        (rules.map (result.restoreRule env auxRec oldRecName newRecName)) := by
  intro rules Htelescope
  induction rules with
  | nil => exact .nil
  | cons rule rules ih =>
    exact .cons
      (restoreRule_refines result env auxRec oldRecName newRecName rule
        (Htelescope rule (by simp)))
      (ih fun tail htail => Htelescope tail (by simp [htail]))

/-- A complete generated constructor batch satisfies the operational
restoration precondition without an additional telescope assumption. -/
theorem BoundGeneratedRecursorRules.restoreRules_refines
    (H : BoundGeneratedRecursorRules indTypes stats motives minors lvls
      ctors start rules)
    (hparams : result.nparams = stats.params.size)
    (prodEnv : Environment) (auxRec : NameMap Name)
    (oldRecName newRecName : Name) :
    RulesRestoration result prodEnv auxRec oldRecName newRecName rules
      (rules.map
        (result.restoreRule prodEnv auxRec oldRecName newRecName)) := by
  apply Lean4Lean.VerifyInductive.restoreRules_refines
  intro rule hrule
  rcases List.mem_iff_getElem.mp hrule with ⟨i, hi, rfl⟩
  have hctor : i < ctors.length := by
    rw [← H.length]
    exact hi
  rcases H.entry i hctor hi with ⟨Hrule⟩
  exact Hrule.rhsRestoreTelescope hparams

/-- Recursor-level restoration records every overwritten metadata field and
the pointwise rule restoration relation. -/
structure RecursorRestoration
    (result : Lean4Lean.ElimNestedInductive.Result)
    (env : Environment) (auxRec : NameMap Name)
    (allIndNames : List Name) (oldRecName newRecName : Name)
    (oldInfo newInfo : RecursorVal) : Prop where
  name : newInfo.name = newRecName
  levelParams : newInfo.levelParams = oldInfo.levelParams
  type : NestedRestoration result env auxRec oldInfo.type newInfo.type
  all : newInfo.all = allIndNames
  numParams : newInfo.numParams = oldInfo.numParams
  numIndices : newInfo.numIndices = oldInfo.numIndices
  numMotives : newInfo.numMotives = oldInfo.numMotives
  numMinors : newInfo.numMinors = oldInfo.numMinors
  rules : RulesRestoration result env auxRec oldRecName newRecName
    oldInfo.rules newInfo.rules
  k : newInfo.k = oldInfo.k
  isUnsafe : newInfo.isUnsafe = oldInfo.isUnsafe

/-- Combining the generation and restoration certificates exposes the exact
complete telescope of the restored primary recursor.  In particular, nested
restoration preserves all motive and minor binders, including those belonging
to auxiliary families, as well as the owner's indices and major premise. -/
theorem RecursorRestoration.typeForallTelescope
    (Hentry : GeneratedRecursorEntry safety venv lparams elimLevel c stats
      indTypes recInfos ownerIdx entry)
    (Hrestore : RecursorRestoration result prodEnv auxRec allIndNames
      oldRecName newRecName Hentry.info newInfo)
    (Hselections : RecursorLocalSelections c stats recInfos ownerIdx)
    (hparams : result.nparams = stats.params.size) :
    ∃ residual,
      Expr.ForallTelescope newInfo.type
        (result.nparams + ((recInfos.map (·.motive)).size +
          (recInfos.flatMap (·.minors)).size +
          recInfos[ownerIdx]!.indices.size + 1))
        residual := by
  rcases Hentry.typeForallTelescope Hselections with ⟨residual, Htype⟩
  rw [← hparams] at Htype
  apply Hrestore.type.forallTelescope (suffixArity :=
    (recInfos.map (·.motive)).size +
      (recInfos.flatMap (·.minors)).size +
      recInfos[ownerIdx]!.indices.size + 1) (by
        simpa [Nat.add_assoc] using Htype) (by omega)

/-- Exact restored telescope, including the canonical motive application at
its residual.  This is the syntactic certificate consumed by the independent
source-side nested recursor specification. -/
theorem RecursorRestoration.typeConcreteRecursorResultForallTelescope
    (Hentry : GeneratedRecursorEntry safety venv lparams elimLevel c stats
      indTypes recInfos ownerIdx entry)
    (Hrestore : RecursorRestoration result prodEnv auxRec allIndNames
      oldRecName newRecName Hentry.info newInfo)
    (Hselections : RecursorLocalSelections c stats recInfos ownerIdx)
    (howner : ownerIdx < recInfos.size)
    (hnoalias : Hselections.NoAlias)
    (hparams : result.nparams = stats.params.size) :
    Expr.ForallTelescope newInfo.type
      (result.nparams + ((recInfos.map (·.motive)).size +
        (recInfos.flatMap (·.minors)).size +
        recInfos[ownerIdx]!.indices.size + 1))
      (concreteRecursorResult (recInfos.map (·.motive)).size
        (recInfos.flatMap (·.minors)).size
        recInfos[ownerIdx]!.indices.size ownerIdx) := by
  have Htype := Hselections.forallTelescope
    (.app (mkAppN recInfos[ownerIdx]!.motive
      recInfos[ownerIdx]!.indices) recInfos[ownerIdx]!.major)
  rw [Hselections.residual_eq_concreteRecursorResult howner hnoalias] at Htype
  have Htype' := Htype.inferImplicit_sameResidual (by rfl) 1000 false
  rw [← Hentry.type, ← hparams] at Htype'
  apply Hrestore.type.concreteRecursorResult_forallTelescope
    (numMotives := (recInfos.map (·.motive)).size)
    (numMinors := (recInfos.flatMap (·.minors)).size)
    (numIndices := recInfos[ownerIdx]!.indices.size)
    (ownerIdx := ownerIdx) (by simpa using howner)
  simpa only [Nat.add_assoc] using Htype'

/-- Positional specification of the generated recursor suffix.  Global motive
and minor indices follow the exact `Array.map`/`Array.flatMap` order used by
production; owner indices and the major premise form the final two groups. -/
inductive GeneratedRecursorDomainSlot
  | motive (index : Nat)
  | minor (index : Nat)
  | index (index : Nat)
  | major
  deriving DecidableEq, Repr

def generatedRecursorDomainSlots
    (recInfos : Array AddInductive.RecInfo) (ownerIdx : Nat) :
    List GeneratedRecursorDomainSlot :=
  (List.range (recInfos.map (·.motive)).size).map
      GeneratedRecursorDomainSlot.motive ++
    (List.range (recInfos.flatMap (·.minors)).size).map
      GeneratedRecursorDomainSlot.minor ++
    (List.range recInfos[ownerIdx]!.indices.size).map
      GeneratedRecursorDomainSlot.index ++
    [.major]

@[simp] theorem generatedRecursorDomainSlots_length
    (recInfos : Array AddInductive.RecInfo) (ownerIdx : Nat) :
    (generatedRecursorDomainSlots recInfos ownerIdx).length =
      (recInfos.map (·.motive)).size +
        (recInfos.flatMap (·.minors)).size +
        recInfos[ownerIdx]!.indices.size + 1 := by
  simp [generatedRecursorDomainSlots]
  omega

@[simp] theorem generatedRecursorDomainSlots_motive
    (recInfos : Array AddInductive.RecInfo) (ownerIdx i : Nat)
    (hi : i < (recInfos.map (·.motive)).size) :
    (generatedRecursorDomainSlots recInfos ownerIdx)[i]? =
      some (.motive i) := by
  simp only [Array.size_map] at hi ⊢
  have htotal : i <
      (generatedRecursorDomainSlots recInfos ownerIdx).length := by
    rw [generatedRecursorDomainSlots_length]
    simp only [Array.size_map, Array.size_flatMap]
    omega
  rw [List.getElem?_eq_getElem htotal]
  simp [generatedRecursorDomainSlots, List.getElem_append, hi] <;> omega

@[simp] theorem generatedRecursorDomainSlots_minor
    (recInfos : Array AddInductive.RecInfo) (ownerIdx i : Nat)
    (hi : i < (recInfos.flatMap (·.minors)).size) :
    (generatedRecursorDomainSlots recInfos ownerIdx)[
        (recInfos.map (·.motive)).size + i]? =
      some (.minor i) := by
  simp only [Array.size_map, Array.size_flatMap] at hi ⊢
  have htotal : recInfos.size + i <
      (generatedRecursorDomainSlots recInfos ownerIdx).length := by
    rw [generatedRecursorDomainSlots_length]
    simp only [Array.size_map, Array.size_flatMap]
    omega
  rw [List.getElem?_eq_getElem htotal]
  simp [generatedRecursorDomainSlots, List.getElem_append, hi] <;> omega

@[simp] theorem generatedRecursorDomainSlots_index
    (recInfos : Array AddInductive.RecInfo) (ownerIdx i : Nat)
    (hi : i < recInfos[ownerIdx]!.indices.size) :
    (generatedRecursorDomainSlots recInfos ownerIdx)[
        (recInfos.map (·.motive)).size +
          (recInfos.flatMap (·.minors)).size + i]? =
      some (.index i) := by
  simp only [Array.size_map, Array.size_flatMap] at ⊢
  unfold generatedRecursorDomainSlots
  rw [List.getElem?_append_left (by simp; omega)]
  rw [List.getElem?_append_right (by simp)]
  simp [hi]

@[simp] theorem generatedRecursorDomainSlots_major
    (recInfos : Array AddInductive.RecInfo) (ownerIdx : Nat) :
    (generatedRecursorDomainSlots recInfos ownerIdx)[
        (recInfos.map (·.motive)).size +
          (recInfos.flatMap (·.minors)).size +
          recInfos[ownerIdx]!.indices.size]? = some .major := by
  simp only [Array.size_map, Array.size_flatMap] at ⊢
  unfold generatedRecursorDomainSlots
  rw [List.getElem?_append_right (by simp; omega)]
  rw [List.getElem?_singleton]
  split <;> simp_all <;> omega

/-- Arithmetic-free inverse view of the generated suffix layout.  Consumers
can recover the exact in-group index from an operational list lookup without
repeating the `map`/`flatMap` offset calculation. -/
inductive GeneratedRecursorDomainPosition
    (recInfos : Array AddInductive.RecInfo) (ownerIdx : Nat) :
    Nat → GeneratedRecursorDomainSlot → Prop
  | motive (i : Nat) (hi : i < (recInfos.map (·.motive)).size) :
      GeneratedRecursorDomainPosition recInfos ownerIdx i (.motive i)
  | minor (i : Nat) (hi : i < (recInfos.flatMap (·.minors)).size) :
      GeneratedRecursorDomainPosition recInfos ownerIdx
        ((recInfos.map (·.motive)).size + i) (.minor i)
  | index (i : Nat) (hi : i < recInfos[ownerIdx]!.indices.size) :
      GeneratedRecursorDomainPosition recInfos ownerIdx
        ((recInfos.map (·.motive)).size +
          (recInfos.flatMap (·.minors)).size + i) (.index i)
  | major : GeneratedRecursorDomainPosition recInfos ownerIdx
      ((recInfos.map (·.motive)).size +
        (recInfos.flatMap (·.minors)).size +
        recInfos[ownerIdx]!.indices.size) .major

/-- Every successful operational suffix-slot lookup has exactly one of the
four production origins. -/
theorem GeneratedRecursorDomainPosition.of_lookup
    (hlookup : (generatedRecursorDomainSlots recInfos ownerIdx)[position]? =
      some slot) :
    GeneratedRecursorDomainPosition recInfos ownerIdx position slot := by
  have hposition : position <
      (generatedRecursorDomainSlots recInfos ownerIdx).length :=
    (List.getElem?_eq_some_iff.mp hlookup).1
  have htotal : position <
      (recInfos.map (·.motive)).size +
        (recInfos.flatMap (·.minors)).size +
        recInfos[ownerIdx]!.indices.size + 1 := by
    simpa using hposition
  by_cases hmotive : position < (recInfos.map (·.motive)).size
  · have hcanonical := generatedRecursorDomainSlots_motive recInfos ownerIdx
      position hmotive
    rw [hlookup] at hcanonical
    have heq : slot = .motive position := Option.some.inj hcanonical
    rw [heq]
    exact .motive position hmotive
  · by_cases hminor : position <
        (recInfos.map (·.motive)).size +
          (recInfos.flatMap (·.minors)).size
    · let i := position - (recInfos.map (·.motive)).size
      have hi : i < (recInfos.flatMap (·.minors)).size := by
        dsimp [i]
        omega
      have hoffset : (recInfos.map (·.motive)).size + i = position := by
        dsimp [i]
        omega
      have hcanonical := generatedRecursorDomainSlots_minor recInfos ownerIdx
        i hi
      rw [hoffset, hlookup] at hcanonical
      have heq : slot = .minor i := Option.some.inj hcanonical
      rw [← hoffset, heq]
      exact .minor i hi
    · by_cases hindex : position <
          (recInfos.map (·.motive)).size +
            (recInfos.flatMap (·.minors)).size +
            recInfos[ownerIdx]!.indices.size
      · let i := position - ((recInfos.map (·.motive)).size +
          (recInfos.flatMap (·.minors)).size)
        have hi : i < recInfos[ownerIdx]!.indices.size := by
          dsimp [i]
          omega
        have hoffset : (recInfos.map (·.motive)).size +
            (recInfos.flatMap (·.minors)).size + i = position := by
          dsimp [i]
          omega
        have hcanonical := generatedRecursorDomainSlots_index recInfos
          ownerIdx i hi
        rw [hoffset, hlookup] at hcanonical
        have heq : slot = .index i := Option.some.inj hcanonical
        rw [← hoffset, heq]
        exact .index i hi
      · have hoffset : position =
            (recInfos.map (·.motive)).size +
              (recInfos.flatMap (·.minors)).size +
              recInfos[ownerIdx]!.indices.size := by
          omega
        have hcanonical := generatedRecursorDomainSlots_major recInfos
          ownerIdx
        rw [← hoffset, hlookup] at hcanonical
        have heq : slot = .major := Option.some.inj hcanonical
        rw [hoffset, heq]
        exact .major

/-- A classified suffix slot paired with the exact retained local declaration
whose type production uses as that forall domain. -/
inductive GeneratedRecursorDomainDeclaration
    (c : AddInductive.Context) (recInfos : Array AddInductive.RecInfo)
    (ownerIdx : Nat) : Nat → GeneratedRecursorDomainSlot → Type
  | motive (i : Nat)
      (declaration : BoundFVarDeclarationAt c
        (recInfos.map (·.motive)) i) :
      GeneratedRecursorDomainDeclaration c recInfos ownerIdx i (.motive i)
  | minor (i : Nat)
      (declaration : BoundFVarDeclarationAt c
        (recInfos.flatMap (·.minors)) i) :
      GeneratedRecursorDomainDeclaration c recInfos ownerIdx
        ((recInfos.map (·.motive)).size + i) (.minor i)
  | index (i : Nat)
      (declaration : BoundFVarDeclarationAt c
        recInfos[ownerIdx]!.indices i) :
      GeneratedRecursorDomainDeclaration c recInfos ownerIdx
        ((recInfos.map (·.motive)).size +
          (recInfos.flatMap (·.minors)).size + i) (.index i)
  | major
      (declaration : BoundFVarDeclarationAt c
        #[recInfos[ownerIdx]!.major] 0) :
      GeneratedRecursorDomainDeclaration c recInfos ownerIdx
        ((recInfos.map (·.motive)).size +
          (recInfos.flatMap (·.minors)).size +
          recInfos[ownerIdx]!.indices.size) .major

/-- `RecInfoBindings` does not merely show that generated recursor binders are
free variables: together with context well-formedness it recovers the exact
local declaration behind every classified suffix position. -/
theorem RecInfoBindings.domainDeclaration
    (H : RecInfoBindings c recInfos) (Hc : BindingContextWF c)
    (howner : ownerIdx < recInfos.size)
    (Hposition : GeneratedRecursorDomainPosition recInfos ownerIdx
      position slot) :
    Nonempty (GeneratedRecursorDomainDeclaration c recInfos ownerIdx
      position slot) := by
  cases Hposition with
  | motive =>
      rcases H.motives.declarationAt Hc position (by omega) with
        ⟨Hdeclaration⟩
      exact ⟨.motive position Hdeclaration⟩
  | minor i =>
      rcases H.flatMinors.declarationAt Hc i (by omega) with ⟨Hdeclaration⟩
      exact ⟨.minor i Hdeclaration⟩
  | index i =>
      rcases (H.indices ownerIdx howner).declarationAt Hc i (by omega) with
        ⟨Hdeclaration⟩
      exact ⟨.index i Hdeclaration⟩
  | major =>
      rcases (H.major ownerIdx howner).declarationAt Hc 0 (by simp) with
        ⟨Hdeclaration⟩
      exact ⟨.major Hdeclaration⟩

theorem RecInfoBindings.domainDeclarationOfLookup
    (H : RecInfoBindings c recInfos) (Hc : BindingContextWF c)
    (howner : ownerIdx < recInfos.size)
    (hlookup : (generatedRecursorDomainSlots recInfos ownerIdx)[position]? =
      some slot) :
    Nonempty (GeneratedRecursorDomainDeclaration c recInfos ownerIdx
      position slot) :=
  H.domainDeclaration Hc howner
    (GeneratedRecursorDomainPosition.of_lookup hlookup)

/-- The exact operational trace relevant to semantic transport of a generated
primary recursor: common parameters are opened once, every remaining domain
is paired with its restored domain, and the canonical motive-application
residual is unchanged. -/
structure GeneratedRecursorRestorationTelescopeTrace
    (result : Lean4Lean.ElimNestedInductive.Result)
    (prodEnv : Environment) (auxRec : NameMap Name)
    (newInfo : RecursorVal)
    (Hentry : GeneratedRecursorEntry safety venv lparams elimLevel c stats
      indTypes recInfos ownerIdx entry) where
  opening : NestedRestorationOpening result prodEnv auxRec Hentry.info.type
    newInfo.type
  suffix : ExprReplacement.ForallTelescopeReplacement
    (result.restoreNestedNode prodEnv opening.params auxRec)
    opening.body opening.restoredBody
    ((recInfos.map (·.motive)).size +
      (recInfos.flatMap (·.minors)).size +
      recInfos[ownerIdx]!.indices.size + 1)
    (concreteRecursorResult (recInfos.map (·.motive)).size
      (recInfos.flatMap (·.minors)).size
      recInfos[ownerIdx]!.indices.size ownerIdx)
    (concreteRecursorResult (recInfos.map (·.motive)).size
      (recInfos.flatMap (·.minors)).size
      recInfos[ownerIdx]!.indices.size ownerIdx)

/-- The operational domain replacements and the independent positional
suffix layout have identical length, so subsequent provenance certificates
can zip them without a truncation side condition. -/
theorem GeneratedRecursorRestorationTelescopeTrace.domainSlots_length
    {recInfos : Array AddInductive.RecInfo} {ownerIdx : Nat}
    {Hentry : GeneratedRecursorEntry safety venv lparams elimLevel c stats
      indTypes recInfos ownerIdx entry}
    (H : GeneratedRecursorRestorationTelescopeTrace result prodEnv auxRec
      newInfo Hentry) :
    ∃ pairs : List (Expr × Expr),
      pairs.length = (generatedRecursorDomainSlots recInfos ownerIdx).length ∧
      ∀ pair ∈ pairs,
        ExprReplacement
          (result.restoreNestedNode prodEnv H.opening.params auxRec)
          pair.1 pair.2 := by
  rcases H.suffix.domainPairs with ⟨pairs, hlength, Hpairs⟩
  refine ⟨pairs, ?_, Hpairs⟩
  rw [hlength, generatedRecursorDomainSlots_length]

theorem RecursorRestoration.generatedTelescopeTrace
    (Hentry : GeneratedRecursorEntry safety venv lparams elimLevel c stats
      indTypes recInfos ownerIdx entry)
    (Hrestore : RecursorRestoration result prodEnv auxRec allIndNames
      oldRecName newRecName Hentry.info newInfo)
    (Hselections : RecursorLocalSelections c stats recInfos ownerIdx)
    (howner : ownerIdx < recInfos.size)
    (hnoalias : Hselections.NoAlias)
    (hparams : result.nparams = stats.params.size)
    (hresultParams : result.params.size = result.nparams) :
    Nonempty (GeneratedRecursorRestorationTelescopeTrace result prodEnv auxRec
      newInfo Hentry) := by
  let numMotives := (recInfos.map (·.motive)).size
  let numMinors := (recInfos.flatMap (·.minors)).size
  let numIndices := recInfos[ownerIdx]!.indices.size
  let recResult := concreteRecursorResult numMotives numMinors numIndices
    ownerIdx
  have Hraw := Hselections.forallTelescope
    (.app (mkAppN recInfos[ownerIdx]!.motive
      recInfos[ownerIdx]!.indices) recInfos[ownerIdx]!.major)
  rw [Hselections.residual_eq_concreteRecursorResult howner hnoalias] at Hraw
  have Himplicit := Hraw.inferImplicit_sameResidual (by rfl) 1000 false
  rw [← Hentry.type, ← hparams] at Himplicit
  have Htelescope : Expr.ForallTelescope Hentry.info.type
      (result.nparams + (numMotives + numMinors + numIndices + 1))
      recResult := by
    simpa [numMotives, numMinors, numIndices, recResult, Nat.add_assoc] using
      Himplicit
  rcases Hrestore.type.opening hresultParams with ⟨Hopen⟩
  rcases Hopen.suffixTelescopeReplacement Htelescope
      (concreteRecursorResult_looseBVarRange (by simpa [numMotives] using
        howner)) with ⟨restoredResidual, Hsuffix⟩
  have Hidentity := ExprReplacement.restoreNested_concreteRecursorResult
    result prodEnv Hopen.params auxRec numMotives numMinors numIndices ownerIdx
  have hresidual : restoredResidual = recResult := by
    calc
      restoredResidual = recResult.replace
          (result.restoreNestedNode prodEnv Hopen.params auxRec) :=
        Hsuffix.residualReplacement.eq_replace
      _ = recResult := by
        simpa [recResult] using Hidentity.eq_replace.symm
  subst restoredResidual
  exact ⟨⟨Hopen, by
    simpa [numMotives, numMinors, numIndices, recResult] using Hsuffix⟩⟩

/-- The operational restoration suffix and the generated semantic suffix are
aligned on the same parameter-closed concrete body. -/
structure GeneratedRecursorRestorationTelescopeAlignment
    (result : Lean4Lean.ElimNestedInductive.Result)
    (prodEnv : Environment) (auxRec : NameMap Name)
    (newInfo : RecursorVal)
    (Hentry : GeneratedRecursorEntry safety venv lparams elimLevel c stats
      indTypes recInfos ownerIdx entry) where
  trace : GeneratedRecursorRestorationTelescopeTrace result prodEnv auxRec
    newInfo Hentry
  selections : RecursorLocalSelections c stats recInfos ownerIdx
  noAlias : selections.NoAlias
  nparams_eq : result.nparams = stats.params.size
  oldParamDomains : List VExpr
  oldSuffixTarget : VExpr
  owner_lt : ownerIdx < recInfos.size
  oldParamDomains_length : oldParamDomains.length = result.nparams
  oldPrefix : Expr.ForallTelescope Hentry.info.type result.nparams
    (trace.opening.body.abstractList trace.opening.selection.fvars)
  oldClosed : Hentry.info.type.FVarIdsIn fun _ => False
  oldSuffix : Expr.ForallTelescopeTypeTranslation venv Hentry.info.levelParams
    (abstractForallContext oldParamDomains [])
    (trace.opening.body.abstractList trace.opening.selection.fvars)
    ((recInfos.map (·.motive)).size +
      (recInfos.flatMap (·.minors)).size +
      recInfos[ownerIdx]!.indices.size + 1)
    oldSuffixTarget

/-- The semantic obligation for one concrete restored suffix domain at a
fixed production position.  It is intentionally independent of the slot
category; `GeneratedRecursorRestoredDomainTranslations` assigns one such
obligation to every motive, minor, index, and major origin. -/
def GeneratedRecursorRestoredDomainTranslation
    {recInfos : Array AddInductive.RecInfo} {ownerIdx : Nat}
    {Hentry : GeneratedRecursorEntry safety venv lparams elimLevel c stats
      indTypes recInfos ownerIdx entry}
    (H : GeneratedRecursorRestorationTelescopeAlignment result prodEnv auxRec
      newInfo Hentry)
    (newEnv : VEnv) (newBase : VLCtx)
    (position binderDepth : Nat) (accumulated : List VExpr) : Prop :=
  OnCtx (abstractForallContext accumulated newBase).toCtx
      (newEnv.IsType Hentry.info.levelParams.length) →
    ∀ {oldΔ oldDomain newDomain oldDomainTarget},
    ExprReplacement
        (result.restoreNestedNode prodEnv H.trace.opening.params auxRec)
        oldDomain newDomain →
    TrExprS venv Hentry.info.levelParams oldΔ
      (oldDomain.abstractList H.trace.opening.selection.fvars binderDepth)
      oldDomainTarget →
    venv.IsType Hentry.info.levelParams.length oldΔ.toCtx oldDomainTarget →
    Expr.AbstractTypeTranslation newEnv Hentry.info.levelParams
      (abstractForallContext accumulated newBase)
      (newDomain.abstractList H.trace.opening.selection.fvars binderDepth)

/-- Slot-indexed semantic provenance for every domain of the restored
generated recursor suffix.  The four fields mirror the production order and
retain the exact global position at which each in-group entry is consumed. -/
structure GeneratedRecursorRestoredDomainTranslations
    {recInfos : Array AddInductive.RecInfo} {ownerIdx : Nat}
    {Hentry : GeneratedRecursorEntry safety venv lparams elimLevel c stats
      indTypes recInfos ownerIdx entry}
    (H : GeneratedRecursorRestorationTelescopeAlignment result prodEnv auxRec
      newInfo Hentry)
    (Horigins : RecInfoTypeOrigins c recInfos)
    (newEnv : VEnv) (newBase : VLCtx) : Prop where
  motive : ∀ i (hi : i < (recInfos.map (·.motive)).size)
      (declaration : BoundFVarDeclarationAt c
        (recInfos.map (·.motive)) i)
      (originType_eq : declaration.type = Horigins.motiveTypes[i]!)
      (binderDepth : Nat) (accumulated : List VExpr),
    GeneratedRecursorRestoredDomainTranslation H newEnv newBase i
      binderDepth accumulated
  minor : ∀ i (hi : i < (recInfos.flatMap (·.minors)).size)
      (declaration : BoundFVarDeclarationAt c
        (recInfos.flatMap (·.minors)) i)
      (origin : Horigins.FlatMinorOrigin declaration)
      (binderDepth : Nat) (accumulated : List VExpr),
    GeneratedRecursorRestoredDomainTranslation H newEnv newBase
      ((recInfos.map (·.motive)).size + i) binderDepth accumulated
  index : ∀ i (hi : i < recInfos[ownerIdx]!.indices.size)
      (declaration : BoundFVarDeclarationAt c
        recInfos[ownerIdx]!.indices i)
      (originType_eq : declaration.type =
        Horigins.indexTypes[ownerIdx]![i]!)
      (binderDepth : Nat) (accumulated : List VExpr),
    GeneratedRecursorRestoredDomainTranslation H newEnv newBase
      ((recInfos.map (·.motive)).size +
        (recInfos.flatMap (·.minors)).size + i) binderDepth accumulated
  major : ∀ (declaration : BoundFVarDeclarationAt c
      #[recInfos[ownerIdx]!.major] 0)
      (originType_eq : declaration.type = Horigins.majorTypes[ownerIdx]!)
      (binderDepth : Nat) (accumulated : List VExpr),
    GeneratedRecursorRestoredDomainTranslation H newEnv newBase
      ((recInfos.map (·.motive)).size +
        (recInfos.flatMap (·.minors)).size +
        recInfos[ownerIdx]!.indices.size) binderDepth accumulated

/-- Semantic provenance for the restored result left after every generated
recursor domain has been opened. -/
def GeneratedRecursorRestoredResidualTranslation
    {recInfos : Array AddInductive.RecInfo} {ownerIdx : Nat}
    {Hentry : GeneratedRecursorEntry safety venv lparams elimLevel c stats
      indTypes recInfos ownerIdx entry}
    (H : GeneratedRecursorRestorationTelescopeAlignment result prodEnv auxRec
      newInfo Hentry)
    (newEnv : VEnv) (newBase : VLCtx) : Prop :=
  ∀ {oldDelta oldResidualTarget} (accumulated : List VExpr),
    OnCtx (abstractForallContext accumulated newBase).toCtx
      (newEnv.IsType Hentry.info.levelParams.length) →
    ExprReplacement
      (result.restoreNestedNode prodEnv H.trace.opening.params auxRec)
      (concreteRecursorResult (recInfos.map (·.motive)).size
        (recInfos.flatMap (·.minors)).size
        recInfos[ownerIdx]!.indices.size ownerIdx)
      (concreteRecursorResult (recInfos.map (·.motive)).size
        (recInfos.flatMap (·.minors)).size
        recInfos[ownerIdx]!.indices.size ownerIdx) →
    TrExprS venv Hentry.info.levelParams oldDelta
      ((concreteRecursorResult (recInfos.map (·.motive)).size
        (recInfos.flatMap (·.minors)).size
        recInfos[ownerIdx]!.indices.size ownerIdx).abstractList
        H.trace.opening.selection.fvars
        ((recInfos.map (·.motive)).size +
          (recInfos.flatMap (·.minors)).size +
          recInfos[ownerIdx]!.indices.size + 1))
      oldResidualTarget →
    venv.IsType Hentry.info.levelParams.length oldDelta.toCtx
      oldResidualTarget →
    Expr.AbstractTypeTranslation newEnv Hentry.info.levelParams
      (abstractForallContext accumulated newBase)
      ((concreteRecursorResult (recInfos.map (·.motive)).size
        (recInfos.flatMap (·.minors)).size
        recInfos[ownerIdx]!.indices.size ownerIdx).abstractList
        H.trace.opening.selection.fvars
        ((recInfos.map (·.motive)).size +
          (recInfos.flatMap (·.minors)).size +
          recInfos[ownerIdx]!.indices.size + 1))

/-- Complete source-facing semantic input for transporting one restored
generated recursor suffix. -/
structure GeneratedRecursorRestoredSuffixTranslations
    {recInfos : Array AddInductive.RecInfo} {ownerIdx : Nat}
    {Hentry : GeneratedRecursorEntry safety venv lparams elimLevel c stats
      indTypes recInfos ownerIdx entry}
    (H : GeneratedRecursorRestorationTelescopeAlignment result prodEnv auxRec
      newInfo Hentry)
    (Horigins : RecInfoTypeOrigins c recInfos)
    (newEnv : VEnv) (newBase : VLCtx) : Prop where
  domains : GeneratedRecursorRestoredDomainTranslations H Horigins
    newEnv newBase
  residual : GeneratedRecursorRestoredResidualTranslation H newEnv newBase

/-- Source-facing semantics of one family in the final lowered mutual block.
The payload deliberately stops at the family telescope: motive syntax and
major applications are canonical consequences, rather than additional facts
that every original/generated-family branch must establish independently. -/
structure RestoredFamilySemantics
    (env : VEnv) (levelParams : List Name)
    (parameterDomains : List VExpr) (numIndices : Nat) where
  family : VExpr
  indexDomains : List VExpr
  familyResult : VExpr
  indexCount : indexDomains.length = numIndices
  familyTyping : env.HasType levelParams.length parameterDomains.reverse family
    (VExpr.wrapForalls indexDomains familyResult)
  /-- The restored family applied to its canonical index variables is a
  type, not merely an arbitrary term with a well-formed result type. -/
  familyApplicationType : env.IsType levelParams.length
    (indexDomains.reverse ++ parameterDomains.reverse)
    (VExpr.mkApps (family.liftN indexDomains.length 0)
      (recursorCanonicalVars indexDomains.length))

def RestoredFamilySemantics.motiveType
    (S : RestoredFamilySemantics env levelParams parameterDomains numIndices)
    (resultLevel : VLevel) : VExpr :=
  VExpr.wrapForalls S.indexDomains
    (.forallE
      (VExpr.mkApps (S.family.liftN S.indexDomains.length 0)
        (recursorCanonicalVars S.indexDomains.length))
      (.sort resultLevel))

theorem RestoredFamilySemantics.motiveTelescope
    (S : RestoredFamilySemantics env levelParams parameterDomains numIndices)
    (resultLevel : VLevel) :
    RecursorMotiveTelescope resultLevel S.indexDomains.length S.family
      (VExpr.wrapForalls S.indexDomains S.familyResult)
      (S.motiveType resultLevel) := by
  exact RecursorMotiveTelescope.wrapForalls S.indexDomains S.family
    S.familyResult resultLevel

/-- Canonically applying the restored family to all of its indices exposes
the stored result in the completed family telescope. -/
theorem RestoredFamilySemantics.familyApplicationTyping
    (S : RestoredFamilySemantics env levelParams parameterDomains numIndices)
    (henv : env.Ordered) :
    env.HasType levelParams.length
      (S.indexDomains.reverse ++ parameterDomains.reverse)
      (VExpr.mkApps (S.family.liftN S.indexDomains.length 0)
        (recursorCanonicalVars S.indexDomains.length))
      S.familyResult :=
  VEnv.HasType.mkApps_wrapForalls_canonical henv S.familyTyping

/-- The canonical motive type is well formed in the common parameter
context.  The family application invariant supplies the major domain, while
validity of the family telescope supplies the dependent index context. -/
theorem RestoredFamilySemantics.motiveTypeIsType
    (S : RestoredFamilySemantics env levelParams parameterDomains numIndices)
    (henv : env.Ordered)
    (hparams : OnCtx parameterDomains.reverse
      (env.IsType levelParams.length))
    (resultLevel : VLevel) (hresult : resultLevel.WF levelParams.length) :
    env.IsType levelParams.length parameterDomains.reverse
      (S.motiveType resultLevel) := by
  have HfamilyType := S.familyTyping.isType henv hparams
  have Hindices := VEnv.IsType.wrapForalls_inv henv hparams HfamilyType
  have Hbody : env.IsType levelParams.length
      (S.indexDomains.reverse ++ parameterDomains.reverse)
      (.forallE
        (VExpr.mkApps (S.family.liftN S.indexDomains.length 0)
          (recursorCanonicalVars S.indexDomains.length))
        (.sort resultLevel)) :=
    VEnv.IsType.forallE S.familyApplicationType
      ⟨.succ resultLevel, VEnv.HasType.sort hresult⟩
  exact VEnv.IsType.wrapForalls Hindices.1 Hbody

/-- Weakening the canonical motive type beneath any already well-formed
inner suffix preserves its well-formedness. -/
theorem RestoredFamilySemantics.motiveTypeIsTypeAfter
    (S : RestoredFamilySemantics env levelParams parameterDomains numIndices)
    (henv : env.Ordered) (added : List VExpr)
    (hctx : OnCtx (added.reverse ++ parameterDomains.reverse)
      (env.IsType levelParams.length))
    (resultLevel : VLevel) (hresult : resultLevel.WF levelParams.length) :
    env.IsType levelParams.length
      (added.reverse ++ parameterDomains.reverse)
      ((S.motiveType resultLevel).liftN added.length 0) := by
  have Hbase := S.motiveTypeIsType henv
    (OnCtx.append_right hctx) resultLevel hresult
  exact Hbase.weakN henv (.zero added.reverse (by simp))

/-- The canonical motive/family parallel telescope remains usable beneath an
arbitrary well-formed suffix.  This is the source-facing major-domain/result
interface needed by restored recursor traversal. -/
theorem RestoredFamilySemantics.applyMajorTypedAfter
    (S : RestoredFamilySemantics env levelParams parameterDomains numIndices)
    (henv : env.WF) (added : List VExpr)
    (hctx : OnCtx (added.reverse ++ parameterDomains.reverse)
      (env.IsType levelParams.length))
    (indexTargets : List VExpr)
    (hindices : indexTargets.length = S.indexDomains.length)
    (resultLevel : VLevel) (motive major : VExpr)
    (Hmotive : env.HasType levelParams.length
      (added.reverse ++ parameterDomains.reverse) motive
      ((S.motiveType resultLevel).liftN added.length 0))
    (Hmajor : env.HasType levelParams.length
      (added.reverse ++ parameterDomains.reverse) major
      (VExpr.mkApps (S.family.liftN added.length 0) indexTargets)) :
    env.HasType levelParams.length
      (added.reverse ++ parameterDomains.reverse)
      (.app (VExpr.mkApps motive indexTargets) major)
      (.sort resultLevel) := by
  have W : Ctx.LiftN added.length 0 parameterDomains.reverse
      (added.reverse ++ parameterDomains.reverse) := by
    exact .zero added.reverse (by simp)
  have Hfamily := S.familyTyping.weakN henv.ordered W
  have Htelescope := (S.motiveTelescope resultLevel).liftN added.length 0
  rw [<- hindices] at Htelescope
  exact Htelescope.applyMajorTyped henv hctx Hfamily Hmotive Hmajor

/-- Rebase a canonical first-pass family telescope onto the common restored
parameter context.  This is the generic original-family constructor; the
end-to-end lowering proof supplies the context conversion. -/
def RecursorCanonicalMotiveTelescope.toRestoredFamilySemantics
    (C : RecursorCanonicalMotiveTelescope env levelParams stats decl target info
      elimLevel)
    (henv : env.Ordered)
    (parameterDomains : List VExpr)
    (Hparams : VEnv.IsDefEqCtx env levelParams.length [] C.params.reverse
      parameterDomains.reverse) :
    RestoredFamilySemantics env levelParams parameterDomains info.indices.size :=
  {
    family := C.family
    indexDomains := C.indices
    familyResult := C.familyResult
    indexCount := C.indices_length
    familyTyping := C.family_typing.defeqDFC henv Hparams
    familyApplicationType := C.familyApplicationType.imp fun _ Htype =>
      Htype.defeqDFC' henv Hparams
  }

/-- Stateful semantic obligation for one restored recursor domain.  The
state relates the exact translated prefix to its source recursor slots, so
later domains may rely on more than bare context well-formedness. -/
def GeneratedRecursorRestoredDomainTranslationInvariant
    {recInfos : Array AddInductive.RecInfo} {ownerIdx : Nat}
    {Hentry : GeneratedRecursorEntry safety venv lparams elimLevel c stats
      indTypes recInfos ownerIdx entry}
    (H : GeneratedRecursorRestorationTelescopeAlignment result prodEnv auxRec
      newInfo Hentry)
    (newEnv : VEnv) (newBase : VLCtx)
    (State : Nat -> List VExpr -> Prop)
    (position binderDepth : Nat) (accumulated : List VExpr) : Prop :=
  State position accumulated ->
    OnCtx (abstractForallContext accumulated newBase).toCtx
      (newEnv.IsType Hentry.info.levelParams.length) ->
    forall {oldDelta oldDomain newDomain oldDomainTarget},
    Expr.ForallBinderAt
      (H.trace.opening.body.abstractList
        H.trace.opening.selection.fvars)
      position
      (oldDomain.abstractList H.trace.opening.selection.fvars binderDepth) ->
    ExprReplacement
        (result.restoreNestedNode prodEnv H.trace.opening.params auxRec)
        oldDomain newDomain ->
    TrExprS venv Hentry.info.levelParams oldDelta
      (oldDomain.abstractList H.trace.opening.selection.fvars binderDepth)
      oldDomainTarget ->
    venv.IsType Hentry.info.levelParams.length oldDelta.toCtx oldDomainTarget ->
    exists newDomainTarget,
      TrExprS newEnv Hentry.info.levelParams
        (abstractForallContext accumulated newBase)
        (newDomain.abstractList H.trace.opening.selection.fvars binderDepth)
        newDomainTarget /\
      newEnv.IsType Hentry.info.levelParams.length
        (abstractForallContext accumulated newBase).toCtx newDomainTarget /\
      State (position + 1) (accumulated ++ [newDomainTarget])

/-- Category-indexed stateful provenance for every restored suffix domain. -/
structure GeneratedRecursorRestoredDomainTranslationsInvariant
    {recInfos : Array AddInductive.RecInfo} {ownerIdx : Nat}
    {Hentry : GeneratedRecursorEntry safety venv lparams elimLevel c stats
      indTypes recInfos ownerIdx entry}
    (H : GeneratedRecursorRestorationTelescopeAlignment result prodEnv auxRec
      newInfo Hentry)
    (Horigins : RecInfoTypeOrigins c recInfos)
    (newEnv : VEnv) (newBase : VLCtx)
    (State : Nat -> List VExpr -> Prop) : Prop where
  motive : forall i (hi : i < (recInfos.map (·.motive)).size)
      (declaration : BoundFVarDeclarationAt c
        (recInfos.map (·.motive)) i)
      (originType_eq : declaration.type = Horigins.motiveTypes[i]!)
      (binderDepth : Nat) (accumulated : List VExpr),
    GeneratedRecursorRestoredDomainTranslationInvariant H newEnv newBase
      State i binderDepth accumulated
  minor : forall i (hi : i < (recInfos.flatMap (·.minors)).size)
      (declaration : BoundFVarDeclarationAt c
        (recInfos.flatMap (·.minors)) i)
      (origin : Horigins.FlatMinorOrigin declaration)
      (binderDepth : Nat) (accumulated : List VExpr),
    GeneratedRecursorRestoredDomainTranslationInvariant H newEnv newBase
      State ((recInfos.map (·.motive)).size + i) binderDepth accumulated
  index : forall i (hi : i < recInfos[ownerIdx]!.indices.size)
      (declaration : BoundFVarDeclarationAt c
        recInfos[ownerIdx]!.indices i)
      (originType_eq : declaration.type =
        Horigins.indexTypes[ownerIdx]![i]!)
      (binderDepth : Nat) (accumulated : List VExpr),
    GeneratedRecursorRestoredDomainTranslationInvariant H newEnv newBase
      State ((recInfos.map (·.motive)).size +
        (recInfos.flatMap (·.minors)).size + i) binderDepth accumulated
  major : forall (declaration : BoundFVarDeclarationAt c
      #[recInfos[ownerIdx]!.major] 0)
      (originType_eq : declaration.type = Horigins.majorTypes[ownerIdx]!)
      (binderDepth : Nat) (accumulated : List VExpr),
    GeneratedRecursorRestoredDomainTranslationInvariant H newEnv newBase
      State ((recInfos.map (·.motive)).size +
        (recInfos.flatMap (·.minors)).size +
        recInfos[ownerIdx]!.indices.size) binderDepth accumulated

/-- A logically sufficient semantic certificate for transporting the entire
restored suffix.  Unlike `GeneratedRecursorRestoredSuffixTranslations`, it
threads an explicit source-shape invariant through the dependent fold. -/
structure GeneratedRecursorRestoredSuffixTranslationsInvariant
    {recInfos : Array AddInductive.RecInfo} {ownerIdx : Nat}
    {Hentry : GeneratedRecursorEntry safety venv lparams elimLevel c stats
      indTypes recInfos ownerIdx entry}
    (H : GeneratedRecursorRestorationTelescopeAlignment result prodEnv auxRec
      newInfo Hentry)
    (Horigins : RecInfoTypeOrigins c recInfos)
    (newEnv : VEnv) (newBase : VLCtx) (initialPrefix : List VExpr) where
  State : Nat -> List VExpr -> Prop
  initial : State 0 initialPrefix
  domains : GeneratedRecursorRestoredDomainTranslationsInvariant H Horigins
    newEnv newBase State
  residual : forall {oldDelta oldResidualTarget}
      (accumulated : List VExpr),
    State ((recInfos.map (·.motive)).size +
      (recInfos.flatMap (·.minors)).size +
      recInfos[ownerIdx]!.indices.size + 1) accumulated ->
    OnCtx (abstractForallContext accumulated newBase).toCtx
      (newEnv.IsType Hentry.info.levelParams.length) ->
    ExprReplacement
      (result.restoreNestedNode prodEnv H.trace.opening.params auxRec)
      (concreteRecursorResult (recInfos.map (·.motive)).size
        (recInfos.flatMap (·.minors)).size
        recInfos[ownerIdx]!.indices.size ownerIdx)
      (concreteRecursorResult (recInfos.map (·.motive)).size
        (recInfos.flatMap (·.minors)).size
        recInfos[ownerIdx]!.indices.size ownerIdx) ->
    TrExprS venv Hentry.info.levelParams oldDelta
      ((concreteRecursorResult (recInfos.map (·.motive)).size
        (recInfos.flatMap (·.minors)).size
        recInfos[ownerIdx]!.indices.size ownerIdx).abstractList
        H.trace.opening.selection.fvars
        ((recInfos.map (·.motive)).size +
          (recInfos.flatMap (·.minors)).size +
          recInfos[ownerIdx]!.indices.size + 1)) oldResidualTarget ->
    venv.IsType Hentry.info.levelParams.length oldDelta.toCtx
      oldResidualTarget ->
    Expr.AbstractTypeTranslation newEnv Hentry.info.levelParams
      (abstractForallContext accumulated newBase)
      ((concreteRecursorResult (recInfos.map (·.motive)).size
        (recInfos.flatMap (·.minors)).size
        recInfos[ownerIdx]!.indices.size ownerIdx).abstractList
        H.trace.opening.selection.fvars
        ((recInfos.map (·.motive)).size +
          (recInfos.flatMap (·.minors)).size +
          recInfos[ownerIdx]!.indices.size + 1))

theorem RecursorRestoration.generatedTelescopeAlignment
    (Hentry : GeneratedRecursorEntry safety venv lparams elimLevel c stats
      indTypes recInfos ownerIdx entry)
    (Hrestore : RecursorRestoration result prodEnv auxRec allIndNames
      oldRecName newRecName Hentry.info newInfo)
    (Hselections : RecursorLocalSelections c stats recInfos ownerIdx)
    (howner : ownerIdx < recInfos.size)
    (hnoalias : Hselections.NoAlias)
    (hparams : result.nparams = stats.params.size)
    (hresultParams : result.params.size = result.nparams) :
    Nonempty (GeneratedRecursorRestorationTelescopeAlignment result prodEnv
      auxRec newInfo Hentry) := by
  rcases Hrestore.generatedTelescopeTrace Hentry Hselections howner hnoalias
      hparams hresultParams with ⟨Htrace⟩
  rcases Hentry.telescopeTranslation Hselections howner hnoalias with
    ⟨Hgenerated⟩
  let suffixArity := (recInfos.map (·.motive)).size +
    (recInfos.flatMap (·.minors)).size +
    recInfos[ownerIdx]!.indices.size + 1
  have Htyped : Expr.ForallTelescopeTypeTranslation venv
      Hentry.info.levelParams [] Hentry.info.type
      (stats.params.size + suffixArity) entry.2.type := by
    simpa [suffixArity, Nat.add_assoc] using Hgenerated.typed
  rcases Htyped.dropPrefix
      (prefixArity := stats.params.size) (suffixArity := suffixArity) with
    ⟨paramDomains, suffixSource, suffixTarget, hparamDomains,
      HsourcePrefix, htarget, Hsuffix⟩
  have HsourcePrefix' : Expr.ForallTelescope Hentry.info.type
      result.nparams suffixSource := by
    simpa [hparams] using HsourcePrefix
  have Hinput : Hentry.info.type.FVarsIn fun _ => False := by
    have := Hgenerated.typed.translation.fvarsIn
    simpa using this
  have hbody : Htrace.opening.body.abstractList
      Htrace.opening.selection.fvars = suffixSource :=
    Htrace.opening.abstractBody_eq_suffix HsourcePrefix' Hinput
  refine ⟨⟨Htrace, Hselections, hnoalias, hparams, paramDomains,
    suffixTarget, howner, ?_, ?_, ?_, ?_⟩⟩
  · exact hparamDomains.trans hparams.symm
  · simpa only [hbody] using HsourcePrefix'
  · exact FVarsIn_to_FVarIdsIn Hinput
  · rw [hbody]
    simpa [suffixArity] using Hsuffix

/-- Lift an exact binder of the parameter-closed restoration suffix back to
its global position in the generated source recursor.  This is the common
source identity used to compare an operational replacement domain with the
independently retained local declaration for its classified slot. -/
theorem GeneratedRecursorRestorationTelescopeAlignment.fullDomainAt
    {Hentry : GeneratedRecursorEntry safety venv lparams elimLevel c stats
      indTypes recInfos ownerIdx entry}
    (H : GeneratedRecursorRestorationTelescopeAlignment result prodEnv auxRec
      newInfo Hentry)
    (Hdomain : Expr.ForallBinderAt
      (H.trace.opening.body.abstractList
        H.trace.opening.selection.fvars)
      position domain) :
    Expr.ForallBinderAt Hentry.info.type
      (result.nparams + position) domain :=
  H.oldPrefix.prependBinderAt Hdomain

/-- The operational domain consumed at a motive slot is definitionally the
source declaration closed over the generated parameter and earlier-motive
prefix. -/
theorem GeneratedRecursorRestorationTelescopeAlignment.motiveDomain_eq
    {Hentry : GeneratedRecursorEntry safety venv lparams elimLevel c stats
      indTypes recInfos ownerIdx entry}
    (H : GeneratedRecursorRestorationTelescopeAlignment result prodEnv auxRec
      newInfo Hentry)
    (D : BoundFVarDeclarationAt c (recInfos.map (·.motive)) motiveIdx)
    (Hdomain : Expr.ForallBinderAt
      (H.trace.opening.body.abstractList
        H.trace.opening.selection.fvars)
      motiveIdx domain) :
    domain = D.type.abstractList
      (H.selections.params.fvars ++
        H.selections.motives.fvars.take motiveIdx) := by
  apply (H.fullDomainAt Hdomain).unique
  have Hexpected := H.selections.motiveBinderAt H.noAlias D
  simpa only [Hentry.type, H.nparams_eq] using Hexpected

/-- The operational domain consumed at a flattened minor slot is the exact
minor declaration closed over parameters, motives, and preceding minors. -/
theorem GeneratedRecursorRestorationTelescopeAlignment.minorDomain_eq
    {Hentry : GeneratedRecursorEntry safety venv lparams elimLevel c stats
      indTypes recInfos ownerIdx entry}
    (H : GeneratedRecursorRestorationTelescopeAlignment result prodEnv auxRec
      newInfo Hentry)
    (D : BoundFVarDeclarationAt c
      (recInfos.flatMap (·.minors)) minorIdx)
    (Hdomain : Expr.ForallBinderAt
      (H.trace.opening.body.abstractList
        H.trace.opening.selection.fvars)
      ((recInfos.map (·.motive)).size + minorIdx) domain) :
    domain = D.type.abstractList
      (H.selections.params.fvars ++
        (H.selections.motives.fvars ++
          H.selections.minors.fvars.take minorIdx)) := by
  apply (H.fullDomainAt Hdomain).unique
  have Hexpected := H.selections.minorBinderAt H.noAlias D
  simpa only [Hentry.type, H.nparams_eq, Nat.add_assoc, List.append_assoc]
    using Hexpected

/-- The operational owner-index domain is the retained index declaration
closed over every earlier generated recursor group. -/
theorem GeneratedRecursorRestorationTelescopeAlignment.indexDomain_eq
    {Hentry : GeneratedRecursorEntry safety venv lparams elimLevel c stats
      indTypes recInfos ownerIdx entry}
    (H : GeneratedRecursorRestorationTelescopeAlignment result prodEnv auxRec
      newInfo Hentry)
    (D : BoundFVarDeclarationAt c recInfos[ownerIdx]!.indices indexIdx)
    (Hdomain : Expr.ForallBinderAt
      (H.trace.opening.body.abstractList
        H.trace.opening.selection.fvars)
      ((recInfos.map (·.motive)).size +
        (recInfos.flatMap (·.minors)).size + indexIdx) domain) :
    domain = D.type.abstractList
      (H.selections.params.fvars ++ (H.selections.motives.fvars ++
        (H.selections.minors.fvars ++
          H.selections.indices.fvars.take indexIdx))) := by
  apply (H.fullDomainAt Hdomain).unique
  have Hexpected := H.selections.indexBinderAt H.noAlias D
  simpa only [Hentry.type, H.nparams_eq, Nat.add_assoc] using Hexpected

/-- The operational major-premise domain is the retained major declaration
closed over the complete parameter/motive/minor/index prefix. -/
theorem GeneratedRecursorRestorationTelescopeAlignment.majorDomain_eq
    {Hentry : GeneratedRecursorEntry safety venv lparams elimLevel c stats
      indTypes recInfos ownerIdx entry}
    (H : GeneratedRecursorRestorationTelescopeAlignment result prodEnv auxRec
      newInfo Hentry)
    (D : BoundFVarDeclarationAt c #[recInfos[ownerIdx]!.major] 0)
    (Hdomain : Expr.ForallBinderAt
      (H.trace.opening.body.abstractList
        H.trace.opening.selection.fvars)
      ((recInfos.map (·.motive)).size +
        (recInfos.flatMap (·.minors)).size +
        recInfos[ownerIdx]!.indices.size) domain) :
    domain = D.type.abstractList
      (H.selections.params.fvars ++ (H.selections.motives.fvars ++
        (H.selections.minors.fvars ++ H.selections.indices.fvars))) := by
  apply (H.fullDomainAt Hdomain).unique
  have Hexpected := H.selections.majorBinderAt H.noAlias D
  simpa only [Hentry.type, H.nparams_eq, Nat.add_assoc] using Hexpected

/-- Run the accumulator-aware semantic replacement fold over the exact
generated/restored suffix alignment.  This packages the bookkeeping that is
common to every restored primary recursor: the old parameter variables are
closed at depth zero, the same operational variables close the restored
suffix, and callbacks see the progressively accumulated canonical domains.

The two callbacks are intentionally the remaining semantic boundary.  In
particular, they must interpret recursive replacement nodes (motive and minor
types), rather than merely postulating a translation for the final restored
type. -/
theorem GeneratedRecursorRestorationTelescopeAlignment.transportSuffix
    {recInfos : Array AddInductive.RecInfo} {ownerIdx : Nat}
    {Hentry : GeneratedRecursorEntry safety venv lparams elimLevel c stats
      indTypes recInfos ownerIdx entry}
    (H : GeneratedRecursorRestorationTelescopeAlignment result prodEnv auxRec
      newInfo Hentry)
    (newEnv : VEnv) (newBase : VLCtx) (newPrefix : List VExpr)
    (HnewCtx : OnCtx (abstractForallContext newPrefix newBase).toCtx
      (newEnv.IsType Hentry.info.levelParams.length))
    (Hdomains : ∀ {oldΔ oldDomain newDomain oldDomainTarget}
        (position binderDepth : Nat) (accumulated : List VExpr)
        (slot : GeneratedRecursorDomainSlot),
      (generatedRecursorDomainSlots recInfos ownerIdx)[position]? =
        some slot →
      OnCtx (abstractForallContext accumulated newBase).toCtx
        (newEnv.IsType Hentry.info.levelParams.length) →
      ExprReplacement
          (result.restoreNestedNode prodEnv H.trace.opening.params auxRec)
          oldDomain newDomain →
      TrExprS venv Hentry.info.levelParams oldΔ
        (oldDomain.abstractList H.trace.opening.selection.fvars binderDepth)
        oldDomainTarget →
      venv.IsType Hentry.info.levelParams.length oldΔ.toCtx
        oldDomainTarget →
      Expr.AbstractTypeTranslation newEnv Hentry.info.levelParams
        (abstractForallContext accumulated newBase)
        (newDomain.abstractList H.trace.opening.selection.fvars binderDepth))
    (Hresidual : ∀ {oldΔ oldResidualTarget}
        (accumulated : List VExpr),
      OnCtx (abstractForallContext accumulated newBase).toCtx
        (newEnv.IsType Hentry.info.levelParams.length) →
      ExprReplacement
          (result.restoreNestedNode prodEnv H.trace.opening.params auxRec)
          (concreteRecursorResult (recInfos.map (·.motive)).size
            (recInfos.flatMap (·.minors)).size
            recInfos[ownerIdx]!.indices.size ownerIdx)
          (concreteRecursorResult (recInfos.map (·.motive)).size
            (recInfos.flatMap (·.minors)).size
            recInfos[ownerIdx]!.indices.size ownerIdx) →
      TrExprS venv Hentry.info.levelParams oldΔ
        ((concreteRecursorResult (recInfos.map (·.motive)).size
          (recInfos.flatMap (·.minors)).size
          recInfos[ownerIdx]!.indices.size ownerIdx).abstractList
          H.trace.opening.selection.fvars
          ((recInfos.map (·.motive)).size +
            (recInfos.flatMap (·.minors)).size +
            recInfos[ownerIdx]!.indices.size + 1))
        oldResidualTarget →
      venv.IsType Hentry.info.levelParams.length oldΔ.toCtx
        oldResidualTarget →
      Expr.AbstractTypeTranslation newEnv Hentry.info.levelParams
        (abstractForallContext accumulated newBase)
        ((concreteRecursorResult (recInfos.map (·.motive)).size
          (recInfos.flatMap (·.minors)).size
          recInfos[ownerIdx]!.indices.size ownerIdx).abstractList
          H.trace.opening.selection.fvars
          ((recInfos.map (·.motive)).size +
            (recInfos.flatMap (·.minors)).size +
            recInfos[ownerIdx]!.indices.size + 1))) :
    ∃ target,
      Expr.ForallTelescopeTypeTranslation newEnv Hentry.info.levelParams
        (abstractForallContext newPrefix newBase)
        (H.trace.opening.restoredBody.abstractList
          H.trace.opening.selection.fvars)
        ((recInfos.map (·.motive)).size +
          (recInfos.flatMap (·.minors)).size +
          recInfos[ownerIdx]!.indices.size + 1)
        target := by
  apply H.trace.suffix.transportAbstractedAtFrom
    (oldParams := H.trace.opening.selection.fvars)
    (newParams := H.trace.opening.selection.fvars)
    (depth := 0)
    (limit := (recInfos.map (·.motive)).size +
      (recInfos.flatMap (·.minors)).size +
      recInfos[ownerIdx]!.indices.size + 1)
    (position := 0) (hspan := by omega)
    (newPrefix := newPrefix) (newBase := newBase)
    H.oldSuffix HnewCtx
  · intro oldΔ oldDomain newDomain oldDomainTarget position binderDepth
      accumulated hposition Hctx Hreplacement Htr Htype
    have hslot : position <
        (generatedRecursorDomainSlots recInfos ownerIdx).length := by
      simpa using hposition
    let slot :=
      (generatedRecursorDomainSlots recInfos ownerIdx)[position]'hslot
    apply Hdomains position binderDepth accumulated slot
    · exact List.getElem?_eq_getElem hslot
    · exact Hctx
    · exact Hreplacement
    · exact Htr
    · exact Htype
  intro oldΔ oldResidualTarget accumulated Hctx Hreplacement Htr Htype
  have Htr' : TrExprS venv Hentry.info.levelParams oldΔ
      ((concreteRecursorResult (recInfos.map (·.motive)).size
        (recInfos.flatMap (·.minors)).size
        recInfos[ownerIdx]!.indices.size ownerIdx).abstractList
        H.trace.opening.selection.fvars
        ((recInfos.map (·.motive)).size +
          (recInfos.flatMap (·.minors)).size +
          recInfos[ownerIdx]!.indices.size + 1))
      oldResidualTarget := by
    simpa using Htr
  simpa using Hresidual accumulated Hctx Hreplacement Htr' Htype

/-- Reclose an independently transported restored suffix under a translated
copy of the unchanged concrete parameter prefix.  The template contributes
only those common domains; all motive, minor, index, major, and result
semantics come from `Hsuffix`, so no translation of the auxiliary-bearing
old recursor type is reused in the canonical environment. -/
theorem GeneratedRecursorRestorationTelescopeAlignment.closeTransportedSuffix
    {recInfos : Array AddInductive.RecInfo} {ownerIdx : Nat}
    {Hentry : GeneratedRecursorEntry safety venv lparams elimLevel c stats
      indTypes recInfos ownerIdx entry}
    (H : GeneratedRecursorRestorationTelescopeAlignment result prodEnv auxRec
      newInfo Hentry)
    (Henv : newEnv.Ordered)
    (HtemplatePrefix : Expr.SameForallDomains result.nparams
      template Hentry.info.type)
    (HtemplateTelescope : Expr.ForallTelescope template result.nparams
      templateResidual)
    (Htemplate : TrExprS newEnv Hentry.info.levelParams [] template
      (VExpr.wrapForalls parameterDomains templateTarget))
    (hparameterDomains : parameterDomains.length = result.nparams)
    (Hsuffix : Expr.ForallTelescopeTypeTranslation newEnv
      Hentry.info.levelParams (abstractForallContext parameterDomains [])
      (H.trace.opening.restoredBody.abstractList
        H.trace.opening.selection.fvars)
      ((recInfos.map (·.motive)).size +
        (recInfos.flatMap (·.minors)).size +
        recInfos[ownerIdx]!.indices.size + 1)
      suffixTarget) :
    Expr.ForallTelescopeTypeTranslation newEnv Hentry.info.levelParams []
      newInfo.type
      (result.nparams + ((recInfos.map (·.motive)).size +
        (recInfos.flatMap (·.minors)).size +
        recInfos[ownerIdx]!.indices.size + 1))
      (VExpr.wrapForalls parameterDomains suffixTarget) := by
  let suffixArity := (recInfos.map (·.motive)).size +
    (recInfos.flatMap (·.minors)).size +
    recInfos[ownerIdx]!.indices.size + 1
  have HoldNew : Expr.SameForallPrefix result.nparams Hentry.info.type
      newInfo.type :=
    H.trace.opening.sameForallPrefix H.oldPrefix H.oldClosed
  have HtemplateNew : Expr.SameForallDomains result.nparams template
      newInfo.type := by
    have HoldNewDomains := HoldNew.sameForallDomains
    exact HtemplatePrefix.trans HoldNewDomains
  have HnewPrefix :=
    H.trace.opening.outputPrefixTelescope H.oldPrefix
  have Hwhole : TrExprS newEnv Hentry.info.levelParams [] newInfo.type
      (VExpr.wrapForalls parameterDomains suffixTarget) :=
    HtemplateNew.replaceTranslatedResidual HtemplateTelescope HnewPrefix
      Henv (by trivial) hparameterDomains Htemplate Hsuffix.translation
        Hsuffix.isType
  have HnewSuffix := H.trace.suffix.newTelescope.abstractList
    H.trace.opening.selection.fvars
  have hresidual :
      (concreteRecursorResult (recInfos.map (·.motive)).size
        (recInfos.flatMap (·.minors)).size
        recInfos[ownerIdx]!.indices.size ownerIdx).abstractList
          H.trace.opening.selection.fvars suffixArity =
      concreteRecursorResult (recInfos.map (·.motive)).size
        (recInfos.flatMap (·.minors)).size
        recInfos[ownerIdx]!.indices.size ownerIdx := by
    apply (concreteRecursorResult_noFVars.mono fun fv hfalse =>
      False.elim hfalse).abstractList_eq_self
    have howner : ownerIdx < (recInfos.map (·.motive)).size := by
      simpa using H.owner_lt
    exact concreteRecursorResult_closed howner
  have HnewSuffix' : Expr.ForallTelescope
      (H.trace.opening.restoredBody.abstractList
        H.trace.opening.selection.fvars)
      suffixArity
      (concreteRecursorResult (recInfos.map (·.motive)).size
        (recInfos.flatMap (·.minors)).size
        recInfos[ownerIdx]!.indices.size ownerIdx) := by
    dsimp [suffixArity] at hresidual ⊢
    simp only [Nat.zero_add] at HnewSuffix
    rw [hresidual] at HnewSuffix
    exact HnewSuffix
  have Htotal := HnewPrefix.trans HnewSuffix'
  have HwholeType : newEnv.IsType Hentry.info.levelParams.length []
      (VExpr.wrapForalls parameterDomains suffixTarget) :=
    TrExprS.isType_of_forallTelescope Htotal (by
      dsimp [suffixArity]
      omega) Hwhole
  simpa [suffixArity] using
    Expr.ForallTelescopeTypeTranslation.ofTrExprS Htotal Hwhole HwholeType

/-- Transport the restored suffix from category-indexed provenance.  All
lookup inversion is discharged here, leaving callers with four source-facing
domain families rather than one callback over an unclassified position. -/
theorem GeneratedRecursorRestorationTelescopeAlignment.transportSuffixOfDomains
    {recInfos : Array AddInductive.RecInfo} {ownerIdx : Nat}
    {Hentry : GeneratedRecursorEntry safety venv lparams elimLevel c stats
      indTypes recInfos ownerIdx entry}
    (H : GeneratedRecursorRestorationTelescopeAlignment result prodEnv auxRec
      newInfo Hentry)
    (newEnv : VEnv) (newBase : VLCtx) (newPrefix : List VExpr)
    (HnewCtx : OnCtx (abstractForallContext newPrefix newBase).toCtx
      (newEnv.IsType Hentry.info.levelParams.length))
    (Hc : BindingContextWF c) (Hbindings : RecInfoBindings c recInfos)
    (Horigins : RecInfoTypeOrigins c recInfos)
    (howner : ownerIdx < recInfos.size)
    (Hdomains : GeneratedRecursorRestoredDomainTranslations H Horigins
      newEnv newBase)
    (Hresidual : ∀ {oldΔ oldResidualTarget}
        (accumulated : List VExpr),
      OnCtx (abstractForallContext accumulated newBase).toCtx
        (newEnv.IsType Hentry.info.levelParams.length) →
      ExprReplacement
          (result.restoreNestedNode prodEnv H.trace.opening.params auxRec)
          (concreteRecursorResult (recInfos.map (·.motive)).size
            (recInfos.flatMap (·.minors)).size
            recInfos[ownerIdx]!.indices.size ownerIdx)
          (concreteRecursorResult (recInfos.map (·.motive)).size
            (recInfos.flatMap (·.minors)).size
            recInfos[ownerIdx]!.indices.size ownerIdx) →
      TrExprS venv Hentry.info.levelParams oldΔ
        ((concreteRecursorResult (recInfos.map (·.motive)).size
          (recInfos.flatMap (·.minors)).size
          recInfos[ownerIdx]!.indices.size ownerIdx).abstractList
          H.trace.opening.selection.fvars
          ((recInfos.map (·.motive)).size +
            (recInfos.flatMap (·.minors)).size +
            recInfos[ownerIdx]!.indices.size + 1))
        oldResidualTarget →
      venv.IsType Hentry.info.levelParams.length oldΔ.toCtx
        oldResidualTarget →
      Expr.AbstractTypeTranslation newEnv Hentry.info.levelParams
        (abstractForallContext accumulated newBase)
        ((concreteRecursorResult (recInfos.map (·.motive)).size
          (recInfos.flatMap (·.minors)).size
          recInfos[ownerIdx]!.indices.size ownerIdx).abstractList
          H.trace.opening.selection.fvars
          ((recInfos.map (·.motive)).size +
            (recInfos.flatMap (·.minors)).size +
            recInfos[ownerIdx]!.indices.size + 1))) :
    ∃ target,
      Expr.ForallTelescopeTypeTranslation newEnv Hentry.info.levelParams
        (abstractForallContext newPrefix newBase)
        (H.trace.opening.restoredBody.abstractList
          H.trace.opening.selection.fvars)
        ((recInfos.map (·.motive)).size +
          (recInfos.flatMap (·.minors)).size +
          recInfos[ownerIdx]!.indices.size + 1)
        target := by
  apply H.transportSuffix newEnv newBase newPrefix HnewCtx
  · intro oldΔ oldDomain newDomain oldDomainTarget position binderDepth
      accumulated slot hlookup Hctx Hreplacement Htr Htype
    cases GeneratedRecursorDomainPosition.of_lookup hlookup with
    | motive =>
        rcases Hbindings.motives.declarationAt Hc _ (by omega) with
          ⟨Hdeclaration⟩
        exact Hdomains.motive _ (by omega) Hdeclaration
          (Horigins.motives.type_eq Hdeclaration) binderDepth
          accumulated Hctx Hreplacement Htr Htype
    | minor =>
        rcases Hbindings.flatMinors.declarationAt Hc _ (by omega) with
          ⟨Hdeclaration⟩
        rcases Horigins.flatMinorOrigin Hdeclaration with ⟨Horigin⟩
        exact Hdomains.minor _ (by omega) Hdeclaration Horigin
          binderDepth accumulated Hctx Hreplacement Htr Htype
    | index =>
        rcases (Hbindings.indices ownerIdx howner).declarationAt Hc _
            (by omega) with ⟨Hdeclaration⟩
        exact Hdomains.index _ (by omega) Hdeclaration
          ((Horigins.indices ownerIdx howner).type_eq Hdeclaration)
          binderDepth accumulated Hctx Hreplacement Htr Htype
    | major =>
        rcases (Hbindings.major ownerIdx howner).declarationAt Hc 0
            (by simp) with ⟨Hdeclaration⟩
        rcases Horigins.majors.declaration ownerIdx (by simpa using howner) with
          ⟨Horigin, horiginType⟩
        have hmapped : ownerIdx < (recInfos.map (·.major)).size := by
          simpa using howner
        have hexpression :
            (#[recInfos[ownerIdx]!.major] : Array Expr)[0]'(by simp) =
              (recInfos.map (·.major))[ownerIdx]'hmapped := by
          simp [Array.getElem!_eq_getD, Array.getD, howner]
        have htypeEq := Hdeclaration.type_eq_of_expression Horigin hexpression
        exact Hdomains.major Hdeclaration (htypeEq.trans horiginType)
          binderDepth accumulated Hctx Hreplacement Htr Htype
  · exact Hresidual

/-- Transport a restored suffix from the packaged source-facing semantic
certificate. -/
theorem GeneratedRecursorRestorationTelescopeAlignment.transportSuffixOfSemantics
    {recInfos : Array AddInductive.RecInfo} {ownerIdx : Nat}
    {Hentry : GeneratedRecursorEntry safety venv lparams elimLevel c stats
      indTypes recInfos ownerIdx entry}
    (H : GeneratedRecursorRestorationTelescopeAlignment result prodEnv auxRec
      newInfo Hentry)
    (newEnv : VEnv) (newBase : VLCtx) (newPrefix : List VExpr)
    (HnewCtx : OnCtx (abstractForallContext newPrefix newBase).toCtx
      (newEnv.IsType Hentry.info.levelParams.length))
    (Hc : BindingContextWF c) (Hbindings : RecInfoBindings c recInfos)
    (Horigins : RecInfoTypeOrigins c recInfos)
    (howner : ownerIdx < recInfos.size)
    (Hsemantics : GeneratedRecursorRestoredSuffixTranslations H Horigins
      newEnv newBase) :
    ∃ target,
      Expr.ForallTelescopeTypeTranslation newEnv Hentry.info.levelParams
        (abstractForallContext newPrefix newBase)
        (H.trace.opening.restoredBody.abstractList
          H.trace.opening.selection.fvars)
        ((recInfos.map (·.motive)).size +
          (recInfos.flatMap (·.minors)).size +
          recInfos[ownerIdx]!.indices.size + 1)
        target :=
  H.transportSuffixOfDomains newEnv newBase newPrefix HnewCtx Hc Hbindings
    Horigins howner Hsemantics.domains Hsemantics.residual

/-- Transport a restored suffix while threading its exact semantic prefix
invariant through motive, minor, index, and major slots. -/
theorem GeneratedRecursorRestorationTelescopeAlignment.transportSuffixOfInvariantSemantics
    {recInfos : Array AddInductive.RecInfo} {ownerIdx : Nat}
    {Hentry : GeneratedRecursorEntry safety venv lparams elimLevel c stats
      indTypes recInfos ownerIdx entry}
    (H : GeneratedRecursorRestorationTelescopeAlignment result prodEnv auxRec
      newInfo Hentry)
    (newEnv : VEnv) (newBase : VLCtx) (newPrefix : List VExpr)
    (HnewCtx : OnCtx (abstractForallContext newPrefix newBase).toCtx
      (newEnv.IsType Hentry.info.levelParams.length))
    (Hc : BindingContextWF c) (Hbindings : RecInfoBindings c recInfos)
    (Horigins : RecInfoTypeOrigins c recInfos)
    (howner : ownerIdx < recInfos.size)
    (Hsemantics : GeneratedRecursorRestoredSuffixTranslationsInvariant H
      Horigins newEnv newBase newPrefix) :
    exists target,
      Expr.ForallTelescopeTypeTranslation newEnv Hentry.info.levelParams
        (abstractForallContext newPrefix newBase)
        (H.trace.opening.restoredBody.abstractList
          H.trace.opening.selection.fvars)
        ((recInfos.map (·.motive)).size +
          (recInfos.flatMap (·.minors)).size +
          recInfos[ownerIdx]!.indices.size + 1) target := by
  apply H.trace.suffix.transportAbstractedAtFromInvariant
    (oldParams := H.trace.opening.selection.fvars)
    (newParams := H.trace.opening.selection.fvars)
    (rootInput := H.trace.opening.body)
    (depth := 0)
    (limit := (recInfos.map (·.motive)).size +
      (recInfos.flatMap (·.minors)).size +
      recInfos[ownerIdx]!.indices.size + 1)
    (position := 0) (hspan := by omega)
    (hdepth := rfl)
    (Hprefix := .nil H.trace.opening.body)
    (newPrefix := newPrefix) (newBase := newBase)
    H.oldSuffix Hsemantics.State Hsemantics.initial HnewCtx
  · intro oldDelta oldDomain newDomain oldDomainTarget position binderDepth
      accumulated hposition Hstate Hctx HdomainAt Hreplacement Htr Htype
    have hslot : position <
        (generatedRecursorDomainSlots recInfos ownerIdx).length := by
      simpa using hposition
    generalize hslotEq :
      (generatedRecursorDomainSlots recInfos ownerIdx)[position]'hslot = slot
    have hlookup :
        (generatedRecursorDomainSlots recInfos ownerIdx)[position]? =
          some slot := by
      rw [List.getElem?_eq_getElem hslot, hslotEq]
    have Hposition := GeneratedRecursorDomainPosition.of_lookup hlookup
    clear hlookup hslotEq
    cases Hposition with
    | motive =>
        rcases Hbindings.motives.declarationAt Hc _ (by omega) with
          ⟨Hdeclaration⟩
        exact Hsemantics.domains.motive _ (by omega) Hdeclaration
          (Horigins.motives.type_eq Hdeclaration) binderDepth accumulated
          Hstate Hctx HdomainAt Hreplacement Htr Htype
    | minor =>
        rcases Hbindings.flatMinors.declarationAt Hc _ (by omega) with
          ⟨Hdeclaration⟩
        rcases Horigins.flatMinorOrigin Hdeclaration with ⟨Horigin⟩
        exact Hsemantics.domains.minor _ (by omega) Hdeclaration Horigin
          binderDepth accumulated Hstate Hctx HdomainAt Hreplacement Htr Htype
    | index =>
        rcases (Hbindings.indices ownerIdx howner).declarationAt Hc _
            (by omega) with ⟨Hdeclaration⟩
        exact Hsemantics.domains.index _ (by omega) Hdeclaration
          ((Horigins.indices ownerIdx howner).type_eq Hdeclaration)
          binderDepth accumulated Hstate Hctx HdomainAt Hreplacement Htr Htype
    | major =>
        rcases (Hbindings.major ownerIdx howner).declarationAt Hc 0
            (by simp) with ⟨Hdeclaration⟩
        rcases Horigins.majors.declaration ownerIdx (by simpa using howner) with
          ⟨Horigin, horiginType⟩
        have hmapped : ownerIdx < (recInfos.map (·.major)).size := by
          simpa using howner
        have hexpression :
            (#[recInfos[ownerIdx]!.major] : Array Expr)[0]'(by simp) =
              (recInfos.map (·.major))[ownerIdx]'hmapped := by
          simp [Array.getElem!_eq_getD, Array.getD, howner]
        have htypeEq := Hdeclaration.type_eq_of_expression Horigin hexpression
        exact Hsemantics.domains.major Hdeclaration
          (htypeEq.trans horiginType) binderDepth accumulated Hstate Hctx
          HdomainAt Hreplacement Htr Htype
  · intro oldDelta oldResidualTarget accumulated Hstate Hctx Hreplacement
      Htr Htype
    simpa using Hsemantics.residual accumulated Hstate Hctx Hreplacement
      (by simpa using Htr) Htype

/-- A canonical translation of the restored recursor telescope is already a
well-formed abstract type.  The final major-premise binder makes the telescope
nonempty, so no separate abstract-WF callback is necessary. -/
theorem RecursorRestoration.translatedTypeIsType
    (Hentry : GeneratedRecursorEntry safety venv lparams elimLevel c stats
      indTypes recInfos ownerIdx entry)
    (Hrestore : RecursorRestoration result prodEnv auxRec allIndNames
      oldRecName newRecName Hentry.info newInfo)
    (Hselections : RecursorLocalSelections c stats recInfos ownerIdx)
    (howner : ownerIdx < recInfos.size)
    (hnoalias : Hselections.NoAlias)
    (hparams : result.nparams = stats.params.size)
    (Htranslation : TrExprS canonicalEnv Hentry.info.levelParams []
      newInfo.type targetType) :
    canonicalEnv.IsType Hentry.info.levelParams.length [] targetType := by
  have Htelescope := Hrestore.typeConcreteRecursorResultForallTelescope
    Hentry Hselections howner hnoalias hparams
  exact TrExprS.isType_of_forallTelescope Htelescope (by omega) Htranslation

/-- Translation into the canonical source environment preserves the complete
restored recursor arity.  This is deliberately stated about the target of the
restored type translation, never about the lowered abstract recursor type. -/
theorem RecursorRestoration.translatedTypeForallArity
    (Hentry : GeneratedRecursorEntry safety venv lparams elimLevel c stats
      indTypes recInfos ownerIdx entry)
    (Hrestore : RecursorRestoration result prodEnv auxRec allIndNames
      oldRecName newRecName Hentry.info newInfo)
    (Hselections : RecursorLocalSelections c stats recInfos ownerIdx)
    (hparams : result.nparams = stats.params.size)
    (Htranslation : TrExprS canonicalEnv Hentry.info.levelParams []
      newInfo.type targetType) :
    ∃ domains translatedResidual,
      targetType.takeForalls
        (result.nparams + ((recInfos.map (·.motive)).size +
          (recInfos.flatMap (·.minors)).size +
          recInfos[ownerIdx]!.indices.size + 1)) =
          some (domains, translatedResidual) ∧
      domains.length =
        result.nparams + ((recInfos.map (·.motive)).size +
          (recInfos.flatMap (·.minors)).size +
          recInfos[ownerIdx]!.indices.size + 1) := by
  rcases Hrestore.typeForallTelescope Hentry Hselections hparams with
    ⟨residual, Htelescope⟩
  exact Htelescope.translatedTakeForalls Htranslation

/-- Construct the independent source nested-recursor specification directly
from the restored production telescope translated in the canonical source
environment.  No lowered abstract recursor is reused: its auxiliary-bearing
type need not even be well-formed in `canonicalEnv`. -/
theorem RecursorRestoration.nestedRecursorShape
    (Hentry : GeneratedRecursorEntry safety venv lparams elimLevel c stats
      indTypes recInfos ownerIdx entry)
    (Hrestore : RecursorRestoration result prodEnv auxRec allIndNames
      oldRecName newRecName Hentry.info newInfo)
    (Hselections : RecursorLocalSelections c stats recInfos ownerIdx)
    (howner : ownerIdx < recInfos.size)
    (hnoalias : Hselections.NoAlias)
    (hparams : result.nparams = stats.params.size)
    (sourceDecl : VInductDecl) (owner : VInductiveType)
    (hdeclOwner : ownerIdx < sourceDecl.types.length)
    (hownerEq : sourceDecl.types[ownerIdx] = owner)
    (recursor : VConstVal)
    (hname : recursor.name = sourceDecl.recursorName owner)
    (huvars : recursor.uvars = sourceDecl.uvars ∨
      recursor.uvars = sourceDecl.uvars + 1)
    (hnparams : sourceDecl.nparams = result.nparams)
    (hmotives : sourceDecl.types.length ≤
      (recInfos.map (·.motive)).size)
    (hminors : sourceDecl.ownedConstructors.length ≤
      (recInfos.flatMap (·.minors)).size)
    (hindices : owner.numIndices = recInfos[ownerIdx]!.indices.size)
    (Htranslation : TrExprS canonicalEnv Hentry.info.levelParams []
      newInfo.type recursor.type) :
    Nonempty (sourceDecl.NestedRecursorShape owner recursor) := by
  have Htelescope := Hrestore.typeConcreteRecursorResultForallTelescope
    Hentry Hselections howner hnoalias hparams
  rcases TrExprS.forallTelescope_shape_with_context Htelescope Htranslation with
    ⟨domains, abstractResult, hdomainsLength, htype, Hresult⟩
  have htotal : result.nparams + (recInfos.map (·.motive)).size +
      (recInfos.flatMap (·.minors)).size +
      recInfos[ownerIdx]!.indices.size + 1 ≤ domains.length := by
    rw [hdomainsLength]
    simp only [Nat.add_assoc, Nat.le_refl]
  have hownerMotive : ownerIdx < (recInfos.map (·.motive)).size := by
    simpa using howner
  have hresultConcrete := TrExprS.concreteRecursorResult_eq
    (numParams := result.nparams) hownerMotive htotal Hresult
  have hdomainsSpec : domains.length =
      sourceDecl.nparams + (recInfos.map (·.motive)).size +
        (recInfos.flatMap (·.minors)).size + owner.numIndices + 1 := by
    rw [hdomainsLength, hnparams, hindices]
    simp only [Nat.add_assoc]
  rcases List.exists_append_five_of_length_eq domains sourceDecl.nparams
      (recInfos.map (·.motive)).size
      (recInfos.flatMap (·.minors)).size owner.numIndices 1
      hdomainsSpec with
    ⟨params, motives, minors, indices, major, hdomains,
      hparamsLength, hmotivesLength, hminorsLength, hindicesLength,
      hmajorLength⟩
  have hresult : abstractResult = sourceDecl.recursorResultWithCounts
      ownerIdx motives.length minors.length owner := by
    simpa [VInductDecl.recursorResultWithCounts, List.map_reverse,
      hmotivesLength, hminorsLength, hindices] using hresultConcrete
  refine ⟨VInductDecl.NestedRecursorShape.ofWrapped hdeclOwner hownerEq
    hname huvars hparamsLength ?_ ?_ hindicesLength hmajorLength ?_ hresult⟩
  · simpa [hmotivesLength] using hmotives
  · simpa [hminorsLength] using hminors
  · simpa [hdomains] using htype

/-- Recursor restoration changes the production name and concrete type while
preserving the metadata observed by `TrConstVal`.  Translation of that new
type is the sole semantic premise; the old translated recursor may be renamed
on the abstract side to match `newRecName`. -/
theorem RecursorRestoration.translated
    (H : RecursorRestoration result prodEnv auxRec allIndNames
      oldRecName newRecName oldInfo newInfo)
    (Hold : TrConstVal safety venv (.recInfo oldInfo)
      { recursor with name := oldRecName })
    (Htype : TrExprS venv oldInfo.levelParams [] newInfo.type recursor.type)
    (hname : recursor.name = newRecName) :
    TrConstVal safety venv (.recInfo newInfo) recursor := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · simpa [ConstantInfo.safety, ConstantInfo.isUnsafe,
      ConstantInfo.isPartial, H.isUnsafe] using Hold.1.1
  · rw [ConstantInfo.levelParams, ConstantInfo.toConstantVal,
      H.levelParams]
    exact Hold.1.2.1
  · change TrExprS venv newInfo.levelParams [] newInfo.type recursor.type
    rw [H.levelParams]
    exact Htype
  · rw [ConstantInfo.name, ConstantInfo.toConstantVal, H.name, ← hname]

/-- Translate a restored recursor without requiring the lowered recursor type
to translate in the restored environment.  In a nested block the lowered type
may mention auxiliary constants which are intentionally not installed there;
only its safety and universe-count metadata survive restoration. -/
theorem RecursorRestoration.translatedOfMetadata
    (H : RecursorRestoration result prodEnv auxRec allIndNames
      oldRecName newRecName oldInfo newInfo)
    (Hsafety : safety ≤ (ConstantInfo.recInfo oldInfo).safety)
    (Huvars : oldInfo.levelParams.length = recursor.uvars)
    (Htype : TrExprS venv oldInfo.levelParams [] newInfo.type recursor.type)
    (hname : recursor.name = newRecName) :
    TrConstVal safety venv (.recInfo newInfo) recursor := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · simpa [ConstantInfo.safety, ConstantInfo.isUnsafe,
      ConstantInfo.isPartial, H.isUnsafe] using Hsafety
  · rw [ConstantInfo.levelParams, ConstantInfo.toConstantVal,
      H.levelParams]
    exact Huvars
  · change TrExprS venv newInfo.levelParams [] newInfo.type recursor.type
    rw [H.levelParams]
    exact Htype
  · rw [ConstantInfo.name, ConstantInfo.toConstantVal, H.name, ← hname]

theorem restoreRecursor_refines
    (result : Lean4Lean.ElimNestedInductive.Result)
    (env : Environment) (auxRec : NameMap Name)
    (allIndNames : List Name) (oldRecName newRecName : Name)
    (info : RecursorVal)
    (Htype : RestoreTelescope info.type result.nparams)
    (Hrules : ∀ rule ∈ info.rules,
      RestoreTelescope rule.rhs result.nparams) :
    RecursorRestoration result env auxRec allIndNames oldRecName newRecName
      info (result.restoreRecursor env auxRec allIndNames
        oldRecName newRecName info) where
  name := rfl
  levelParams := rfl
  type := restoreNested_refines result env auxRec info.type Htype
  all := rfl
  numParams := rfl
  numIndices := rfl
  numMotives := rfl
  numMinors := rfl
  rules := restoreRules_refines result env auxRec oldRecName newRecName
    info.rules Hrules
  k := rfl
  isUnsafe := rfl

/-- Exact state transition of the production family-header restoration step. -/
structure RestoredInductiveHeaderDeclResult
    (loweredEnv sourceEnv : Environment) (allIndNames : List Name)
    (indName : Name) (oldInfo : InductiveVal)
    (out : Unit × Environment) where
  newInfo : InductiveVal
  restored : newInfo = { oldInfo with all := allIndNames }
  fresh : sourceEnv.contains newInfo.name = false
  output : out = ((), sourceEnv.add (.inductInfo newInfo))

/-- Changing the mutual-family metadata list does not affect translation of
an inductive header: `TrConstVal` observes only safety, universes, name, and
type. -/
theorem TrConstVal.inductInfo_setAll
    (H : TrConstVal safety venv (.inductInfo oldInfo) header) :
    TrConstVal safety venv
      (.inductInfo { oldInfo with all := allIndNames }) header := by
  cases oldInfo
  simpa [TrConstVal, TrConstant, ConstantInfo.safety,
    ConstantInfo.isUnsafe, ConstantInfo.isPartial,
    ConstantInfo.levelParams, ConstantInfo.type, ConstantInfo.name,
    ConstantInfo.toConstantVal] using H

theorem RestoredInductiveHeaderDeclResult.translated
    (H : RestoredInductiveHeaderDeclResult loweredEnv sourceProdEnv
      allIndNames indName oldInfo out)
    (Htr : TrConstVal safety venv (.inductInfo oldInfo) header) :
    TrConstVal safety venv (.inductInfo H.newInfo) header := by
  rw [H.restored]
  exact TrConstVal.inductInfo_setAll Htr

theorem restoreInductiveHeaderDecl_refines
    (loweredEnv sourceEnv : Environment) (allIndNames : List Name)
    (allowPrimitive : Bool) (indName : Name) (oldInfo : InductiveVal)
    (hlookup : loweredEnv.find? indName = some (.inductInfo oldInfo)) :
    (Lean4Lean.restoreInductiveHeaderDecl loweredEnv allIndNames
      allowPrimitive indName sourceEnv).WF fun out =>
        Nonempty (RestoredInductiveHeaderDeclResult loweredEnv sourceEnv
          allIndNames indName oldInfo out) := by
  intro out hout
  unfold Lean4Lean.restoreInductiveHeaderDecl at hout
  simp only [hlookup] at hout
  change (sourceEnv.checkName oldInfo.name allowPrimitive).bind (fun _ =>
    Except.ok ((), sourceEnv.add (.inductInfo
      { oldInfo with all := allIndNames }))) = Except.ok out at hout
  cases hcheck : sourceEnv.checkName oldInfo.name allowPrimitive with
  | error err =>
    simp only [hcheck, Except.bind] at hout
    cases hout
  | ok checked =>
    simp only [hcheck, Except.bind, Except.ok.injEq] at hout
    subst out
    have hfresh : sourceEnv.contains oldInfo.name = false := by
      cases hcontains : sourceEnv.contains oldInfo.name
      · rfl
      · simp [Environment.checkName, hcontains, (· >>= ·), Except.bind]
          at hcheck
    exact ⟨{
      newInfo := { oldInfo with all := allIndNames }
      restored := rfl
      fresh := hfresh
      output := rfl }⟩

/-- Generic compositional trace for the stateful list folds used by nested
declaration restoration. -/
inductive StateForMTrace (P : α → σ → σ → Type) :
    List α → σ → σ → Type
  | nil : StateForMTrace P [] source source
  | cons : P head source middle →
      StateForMTrace P tail middle target →
      StateForMTrace P (head :: tail) source target

/-- Environment additions whose names were checked immediately before each
installation.  This forgetful trace is shared by all three nested-restoration
folds and exposes the freshness invariant without importing any semantic
typing assumptions. -/
inductive FreshConstantTrace :
    Environment → List ConstantInfo → Environment → Prop
  | nil : FreshConstantTrace env [] env
  | cons : env.find? ci.name = none →
      FreshConstantTrace (env.add ci) cis outEnv →
      FreshConstantTrace env (ci :: cis) outEnv

theorem FreshConstantTrace.append
    (H₁ : FreshConstantTrace env entries middleEnv)
    (H₂ : FreshConstantTrace middleEnv rest outEnv) :
    FreshConstantTrace env (entries ++ rest) outEnv := by
  induction H₁ with
  | nil => exact H₂
  | cons hfresh _Htail ih => exact .cons hfresh (ih H₂)

private theorem find?_none_of_add_none
    {env : Environment} {head : ConstantInfo} {name : Name}
    (hwf : env.constants.WF) (hfresh : env.find? head.name = none)
    (hnext : (env.add head).find? name = none) : env.find? name = none := by
  have hfreshMap : env.constants.find? head.name = none := by
    change env.constants.find?' head.name = none at hfresh
    rwa [hwf.find?'_eq_find?] at hfresh
  have hnextWF := hwf.insert head.name head hfreshMap
  change SMap.find?' (env.constants.insert head.name head) name = none at hnext
  rw [hnextWF.find?'_eq_find?, hwf.find?_insert] at hnext
  split at hnext
  · contradiction
  · change env.constants.find?' name = none
    rwa [hwf.find?'_eq_find?]

private theorem find?_add_self
    {env : Environment} {ci : ConstantInfo}
    (hwf : env.constants.WF) (hfresh : env.find? ci.name = none) :
    (env.add ci).find? ci.name = some ci := by
  have hfreshMap : env.constants.find? ci.name = none := by
    change env.constants.find?' ci.name = none at hfresh
    rwa [hwf.find?'_eq_find?] at hfresh
  have hnextWF := hwf.insert ci.name ci hfreshMap
  change SMap.find?' (env.constants.insert ci.name ci) ci.name = some ci
  rw [hnextWF.find?'_eq_find?, hwf.find?_insert]
  simp

theorem constantsWF_add_checked
    {env : Environment} {ci : ConstantInfo} (hwf : env.constants.WF)
    (hfresh : env.find? ci.name = none) : (env.add ci).constants.WF := by
  have hfreshMap : env.constants.find? ci.name = none := by
    change env.constants.find?' ci.name = none at hfresh
    rwa [hwf.find?'_eq_find?] at hfresh
  exact hwf.insert ci.name ci hfreshMap

theorem FreshConstantTrace.sourceFresh
    (H : FreshConstantTrace env entries outEnv)
    (hwf : env.constants.WF) (hentry : ci ∈ entries) :
    env.find? ci.name = none := by
  induction H with
  | nil => simp at hentry
  | cons hfresh Htail ih =>
    simp only [List.mem_cons] at hentry
    rcases hentry with rfl | htail
    · exact hfresh
    · have hnextWF := constantsWF_add_checked hwf hfresh
      exact find?_none_of_add_none hwf hfresh
        (ih hnextWF htail)

theorem FreshConstantTrace.namesNodup
    (H : FreshConstantTrace env entries outEnv) (hwf : env.constants.WF) :
    (entries.map (·.name)).Nodup := by
  induction H with
  | nil => simp
  | cons hfresh Htail ih =>
    have hnextWF := constantsWF_add_checked hwf hfresh
    simp only [List.map_cons, List.nodup_cons]
    refine ⟨?_, ih hnextWF⟩
    intro hname
    rcases List.mem_map.mp hname with ⟨ci, hci, heq⟩
    have htailFresh := Htail.sourceFresh hnextWF hci
    have hheadPresent := find?_add_self hwf hfresh
    rw [← heq, htailFresh] at hheadPresent
    contradiction

theorem FreshConstantTrace.targetWF
    (H : FreshConstantTrace env entries outEnv) (hwf : env.constants.WF) :
    outEnv.constants.WF := by
  induction H with
  | nil => exact hwf
  | cons hfresh _Htail ih => exact ih (constantsWF_add_checked hwf hfresh)

/-- Semantic interpretation of an exact production freshness trace.  Each
restored production constant is paired with its translated abstract constant
in the abstract environment current at that same step. -/
inductive TranslatedFreshConstantTrace (safety : DefinitionSafety) :
    ∀ {prodEnv entries outProd},
      FreshConstantTrace prodEnv entries outProd →
      VEnv → List VConstVal → VEnv → Prop
  | nil (prodEnv : Environment) (venv : VEnv) :
      TranslatedFreshConstantTrace safety
        (FreshConstantTrace.nil (env := prodEnv)) venv [] venv
  | cons
      {prodEnv outProd : Environment} {ci : ConstantInfo}
      {entries : List ConstantInfo} {venv nextVEnv outVEnv : VEnv}
      {ci' : VConstVal} {constants : List VConstVal}
      (hfresh : prodEnv.find? ci.name = none)
      (Hfresh : FreshConstantTrace (prodEnv.add ci) entries outProd)
      (Htr : TrConstVal safety venv ci ci')
      (Hwf : ci'.toVConstant.WF venv)
      (Hadd : venv.addConst ci'.name ci'.toVConstant = some nextVEnv)
      (Htail : TranslatedFreshConstantTrace safety Hfresh nextVEnv
        constants outVEnv) :
      TranslatedFreshConstantTrace safety (.cons hfresh Hfresh) venv
        (ci' :: constants) outVEnv

theorem TranslatedFreshConstantTrace.abstract
    (H : TranslatedFreshConstantTrace safety Hfresh venv constants outVEnv) :
    venv.addConstVals constants = some outVEnv := by
  induction H with
  | nil => rfl
  | cons _hfresh _Hfresh _Htr _Hwf Hadd _Htail ih =>
    simp only [VEnv.addConstVals]
    rw [Hadd]
    exact ih

theorem TranslatedFreshConstantTrace.names
    {prodEnv outProd : Environment} {entries : List ConstantInfo}
    {Hfresh : FreshConstantTrace prodEnv entries outProd}
    (H : TranslatedFreshConstantTrace safety Hfresh venv constants outVEnv) :
    constants.map (·.name) = entries.map (·.name) := by
  induction H with
  | nil => rfl
  | cons _hfresh _Hfresh Htr _Hwf _Hadd _Htail ih =>
    simp [← Htr.2, ih]

theorem TranslatedFreshConstantTrace.append
    {prodEnv middleProd outProd : Environment}
    {entries rest : List ConstantInfo}
    {Hfresh₁ : FreshConstantTrace prodEnv entries middleProd}
    {Hfresh₂ : FreshConstantTrace middleProd rest outProd}
    {sourceVEnv middleVEnv outVEnv : VEnv}
    {constants restConstants : List VConstVal}
    (H₁ : TranslatedFreshConstantTrace safety Hfresh₁ sourceVEnv
      constants middleVEnv)
    (H₂ : TranslatedFreshConstantTrace safety Hfresh₂ middleVEnv
      restConstants outVEnv) :
    TranslatedFreshConstantTrace safety (Hfresh₁.append Hfresh₂)
      sourceVEnv (constants ++ restConstants) outVEnv := by
  induction H₁ with
  | nil => exact H₂
  | cons hfresh Hfresh Htr Hwf Hadd _Htail ih =>
    exact .cons hfresh (Hfresh.append Hfresh₂) Htr Hwf Hadd (ih H₂)

theorem stateForM_refines
    (step : α → StateT σ (Except Exception) Unit)
    (P : α → σ → σ → Type) :
    ∀ (items : List α),
      (∀ item, item ∈ items → ∀ source,
        (step item source).WF fun out =>
          out.1 = () ∧ Nonempty (P item source out.2)) →
      ∀ (source : σ),
      (List.forM items step source).WF fun out =>
        out.1 = () ∧ Nonempty (StateForMTrace P items source out.2) := by
  intro items
  induction items with
  | nil =>
    intro _Hstep
    intro source
    exact Except.WF.pure ⟨rfl, ⟨StateForMTrace.nil⟩⟩
  | cons head tail ih =>
    intro Hstep
    intro source
    rw [List.forM]
    exact (Hstep head (by simp) source).bind fun out Hout => by
      rcases out with ⟨unit, middle⟩
      rcases unit with ⟨⟩
      rcases Hout with ⟨_, ⟨Hhead⟩⟩
      have Htail : ∀ item, item ∈ tail → ∀ source,
          (step item source).WF fun out =>
            out.1 = () ∧ Nonempty (P item source out.2) := by
        intro item hitem
        exact Hstep item (by simp [hitem])
      exact (ih Htail middle).mono fun final Hfinal => by
        rcases Hfinal with ⟨hunit, ⟨Htail⟩⟩
        exact ⟨hunit, ⟨StateForMTrace.cons Hhead Htail⟩⟩

/-- Constructor-level restoration records that the production step changes
only the type, using the verified nested-expression traversal. -/
structure ConstructorRestoration
    (result : Lean4Lean.ElimNestedInductive.Result)
    (env : Environment) (oldInfo newInfo : ConstructorVal) : Prop where
  name : newInfo.name = oldInfo.name
  levelParams : newInfo.levelParams = oldInfo.levelParams
  type : NestedRestoration result env {} oldInfo.type newInfo.type
  induct : newInfo.induct = oldInfo.induct
  cidx : newInfo.cidx = oldInfo.cidx
  numParams : newInfo.numParams = oldInfo.numParams
  numFields : newInfo.numFields = oldInfo.numFields
  isUnsafe : newInfo.isUnsafe = oldInfo.isUnsafe

/-- Constructor restoration preserves every `TrConstVal` field except the
concrete type expression.  Thus the semantic inverse of nested-expression
lowering is isolated as the single `Htype` premise below. -/
theorem ConstructorRestoration.translated
    (H : ConstructorRestoration result prodEnv oldInfo newInfo)
    (Hold : TrConstVal safety venv (.ctorInfo oldInfo) constructor)
    (Htype : TrExprS venv oldInfo.levelParams [] newInfo.type
      constructor.type) :
    TrConstVal safety venv (.ctorInfo newInfo) constructor := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · simpa [ConstantInfo.safety, ConstantInfo.isUnsafe,
      ConstantInfo.isPartial, H.isUnsafe] using Hold.1.1
  · rw [ConstantInfo.levelParams, ConstantInfo.toConstantVal,
      H.levelParams]
    exact Hold.1.2.1
  · change TrExprS venv newInfo.levelParams [] newInfo.type constructor.type
    rw [H.levelParams]
    exact Htype
  · rw [ConstantInfo.name, ConstantInfo.toConstantVal, H.name]
    exact Hold.2

/-- Translate a restored constructor from the metadata that restoration
actually preserves.  The old lowered constructor type need not translate in
the restored source environment, where generated auxiliary families are
intentionally absent. -/
theorem ConstructorRestoration.translatedOfMetadata
    (H : ConstructorRestoration result prodEnv oldInfo newInfo)
    (Hsafety : safety ≤ (ConstantInfo.ctorInfo oldInfo).safety)
    (Huvars : oldInfo.levelParams.length = constructor.uvars)
    (Hname : oldInfo.name = constructor.name)
    (Htype : TrExprS venv oldInfo.levelParams [] newInfo.type
      constructor.type) :
    TrConstVal safety venv (.ctorInfo newInfo) constructor := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · simpa [ConstantInfo.safety, ConstantInfo.isUnsafe,
      ConstantInfo.isPartial, H.isUnsafe] using Hsafety
  · rw [ConstantInfo.levelParams, ConstantInfo.toConstantVal,
      H.levelParams]
    exact Huvars
  · change TrExprS venv newInfo.levelParams [] newInfo.type constructor.type
    rw [H.levelParams]
    exact Htype
  · rw [ConstantInfo.name, ConstantInfo.toConstantVal, H.name]
    exact Hname

theorem restoreConstructor_refines
    (result : Lean4Lean.ElimNestedInductive.Result)
    (env : Environment) (info : ConstructorVal)
    (Htelescope : RestoreTelescope info.type result.nparams) :
    ConstructorRestoration result env info
      { info with type := result.restoreNested env info.type } where
  name := rfl
  levelParams := rfl
  type := restoreNested_refines result env {} info.type Htelescope
  induct := rfl
  cidx := rfl
  numParams := rfl
  numFields := rfl
  isUnsafe := rfl

/-- Exact state transition of one production constructor-restoration step. -/
structure RestoredConstructorDeclResult
    (result : Lean4Lean.ElimNestedInductive.Result)
    (loweredEnv sourceEnv : Environment) (ctorName : Name)
    (oldInfo : ConstructorVal) (out : Unit × Environment) where
  newInfo : ConstructorVal
  newInfo_eq : newInfo =
    { oldInfo with type := result.restoreNested loweredEnv oldInfo.type }
  restoration : ConstructorRestoration result loweredEnv oldInfo newInfo
  fresh : sourceEnv.contains newInfo.name = false
  output : out = ((), sourceEnv.add (.ctorInfo newInfo))

theorem restoreConstructorDecl_refines
    (result : Lean4Lean.ElimNestedInductive.Result)
    (loweredEnv sourceEnv : Environment) (allowPrimitive : Bool)
    (ctorName : Name) (oldInfo : ConstructorVal)
    (hlookup : loweredEnv.find? ctorName = some (.ctorInfo oldInfo))
    (Htelescope : RestoreTelescope oldInfo.type result.nparams) :
    (Lean4Lean.restoreConstructorDecl result loweredEnv allowPrimitive ctorName
      sourceEnv).WF fun out =>
        Nonempty (RestoredConstructorDeclResult result loweredEnv sourceEnv
          ctorName oldInfo out) := by
  intro out hout
  unfold Lean4Lean.restoreConstructorDecl at hout
  simp only [hlookup] at hout
  change (sourceEnv.checkName oldInfo.name allowPrimitive).bind (fun _ =>
    Except.ok ((), sourceEnv.add (.ctorInfo
      { oldInfo with type := result.restoreNested loweredEnv oldInfo.type }))) =
        Except.ok out at hout
  cases hcheck : sourceEnv.checkName oldInfo.name allowPrimitive with
  | error err =>
    simp only [hcheck, Except.bind] at hout
    cases hout
  | ok checked =>
    simp only [hcheck, Except.bind, Except.ok.injEq] at hout
    subst out
    have hfresh : sourceEnv.contains oldInfo.name = false := by
      cases hcontains : sourceEnv.contains oldInfo.name
      · rfl
      · simp [Environment.checkName, hcontains, (· >>= ·), Except.bind]
          at hcheck
    exact ⟨{
      newInfo := { oldInfo with
        type := result.restoreNested loweredEnv oldInfo.type }
      newInfo_eq := rfl
      restoration := restoreConstructor_refines result loweredEnv oldInfo
        Htelescope
      fresh := hfresh
      output := rfl }⟩

/-- One element of the executable constructor-restoration fold, retaining the
lowered lookup and telescope premise used to justify restoration. -/
structure RestoredConstructorStep
    (result : Lean4Lean.ElimNestedInductive.Result)
    (loweredEnv : Environment) (ctorName : Name)
    (sourceEnv targetEnv : Environment) where
  oldInfo : ConstructorVal
  lookup : loweredEnv.find? ctorName = some (.ctorInfo oldInfo)
  telescope : RestoreTelescope oldInfo.type result.nparams
  restored : RestoredConstructorDeclResult result loweredEnv sourceEnv
    ctorName oldInfo ((), targetEnv)

theorem restoreConstructorDecls_refines
    (result : Lean4Lean.ElimNestedInductive.Result)
    (loweredEnv : Environment) (allowPrimitive : Bool)
    (ctorNames : List Name)
    (Hsources : ∀ ctorName, ctorName ∈ ctorNames →
      ∃ oldInfo : ConstructorVal,
        loweredEnv.find? ctorName = some (.ctorInfo oldInfo) ∧
        RestoreTelescope oldInfo.type result.nparams) :
    ∀ sourceEnv,
      (ctorNames.forM fun ctorName =>
        Lean4Lean.restoreConstructorDecl result loweredEnv allowPrimitive
          ctorName) sourceEnv |>.WF fun out =>
            out.1 = () ∧ Nonempty (StateForMTrace
              (RestoredConstructorStep result loweredEnv)
              ctorNames sourceEnv out.2) := by
  apply stateForM_refines
  intro ctorName hctor sourceEnv
  rcases Hsources ctorName hctor with ⟨oldInfo, hlookup, Htelescope⟩
  exact (restoreConstructorDecl_refines result loweredEnv sourceEnv
    allowPrimitive ctorName oldInfo hlookup Htelescope).mono fun out Hout => by
      rcases out with ⟨unit, targetEnv⟩
      rcases unit with ⟨⟩
      rcases Hout with ⟨Hrestored⟩
      exact ⟨rfl, ⟨{
        oldInfo := oldInfo
        lookup := hlookup
        telescope := Htelescope
        restored := Hrestored }⟩⟩

/-- Exact state transition of one production recursor-restoration step. The
semantic use of the restored metadata remains factored through
`RecursorRestoration`. -/
structure RestoredRecursorDeclResult
    (result : Lean4Lean.ElimNestedInductive.Result)
    (loweredEnv sourceEnv : Environment) (auxRec : NameMap Name)
    (allIndNames : List Name) (oldRecName : Name)
    (oldInfo : RecursorVal) (out : Unit × Environment) where
  newRecName : Name
  newInfo : RecursorVal
  mappedName : newRecName = auxRec.getD oldRecName oldRecName
  restoration : RecursorRestoration result loweredEnv auxRec allIndNames
    oldRecName newRecName oldInfo newInfo
  fresh : sourceEnv.contains newInfo.name = false
  output : out = ((), sourceEnv.add (.recInfo newInfo))

theorem restoreRecursorDecl_refines
    (result : Lean4Lean.ElimNestedInductive.Result)
    (loweredEnv sourceEnv : Environment) (auxRec : NameMap Name)
    (allIndNames : List Name) (allowPrimitive : Bool) (oldRecName : Name)
    (oldInfo : RecursorVal)
    (hlookup : loweredEnv.find? oldRecName = some (.recInfo oldInfo))
    (Htype : RestoreTelescope oldInfo.type result.nparams)
    (Hrules : ∀ rule ∈ oldInfo.rules,
      RestoreTelescope rule.rhs result.nparams) :
    (Lean4Lean.restoreRecursorDecl result loweredEnv auxRec allIndNames
      allowPrimitive oldRecName sourceEnv).WF fun out =>
        Nonempty (RestoredRecursorDeclResult result loweredEnv sourceEnv auxRec
          allIndNames oldRecName oldInfo out) := by
  intro out hout
  unfold Lean4Lean.restoreRecursorDecl at hout
  simp only [hlookup] at hout
  change (sourceEnv.checkName (auxRec.getD oldRecName oldRecName)
    allowPrimitive).bind (fun _ => Except.ok ((), sourceEnv.add (.recInfo
      (result.restoreRecursor loweredEnv auxRec allIndNames oldRecName
        (auxRec.getD oldRecName oldRecName) oldInfo)))) = Except.ok out at hout
  cases hcheck : sourceEnv.checkName (auxRec.getD oldRecName oldRecName)
      allowPrimitive with
  | error err =>
    simp only [hcheck, Except.bind] at hout
    cases hout
  | ok checked =>
    simp only [hcheck, Except.bind, Except.ok.injEq] at hout
    subst out
    let newRecName := auxRec.getD oldRecName oldRecName
    let newInfo := result.restoreRecursor loweredEnv auxRec allIndNames
      oldRecName newRecName oldInfo
    have hfresh : sourceEnv.contains newRecName = false := by
      cases hcontains : sourceEnv.contains newRecName
      · rfl
      · simp [Environment.checkName, hcontains, (· >>= ·), Except.bind,
          newRecName] at hcheck
    exact ⟨{
      newRecName := newRecName
      newInfo := newInfo
      mappedName := rfl
      restoration := restoreRecursor_refines result loweredEnv auxRec
        allIndNames oldRecName newRecName oldInfo Htype Hrules
      fresh := by
        change sourceEnv.contains newRecName = false
        exact hfresh
      output := rfl }⟩

/-- One element of an executable recursor-restoration fold. -/
structure RestoredRecursorStep
    (result : Lean4Lean.ElimNestedInductive.Result)
    (loweredEnv : Environment) (auxRec : NameMap Name)
    (allIndNames : List Name) (oldRecName : Name)
    (sourceEnv targetEnv : Environment) where
  oldInfo : RecursorVal
  lookup : loweredEnv.find? oldRecName = some (.recInfo oldInfo)
  typeTelescope : RestoreTelescope oldInfo.type result.nparams
  ruleTelescopes : ∀ rule ∈ oldInfo.rules,
    RestoreTelescope rule.rhs result.nparams
  restored : RestoredRecursorDeclResult result loweredEnv sourceEnv auxRec
    allIndNames oldRecName oldInfo ((), targetEnv)

theorem restoreRecursorDecls_refines
    (result : Lean4Lean.ElimNestedInductive.Result)
    (loweredEnv : Environment) (auxRec : NameMap Name)
    (allIndNames : List Name) (allowPrimitive : Bool)
    (recNames : List Name)
    (Hsources : ∀ recName, recName ∈ recNames →
      ∃ oldInfo : RecursorVal,
        loweredEnv.find? recName = some (.recInfo oldInfo) ∧
        RestoreTelescope oldInfo.type result.nparams ∧
        ∀ rule ∈ oldInfo.rules,
          RestoreTelescope rule.rhs result.nparams) :
    ∀ sourceEnv,
      (recNames.forM fun recName =>
        Lean4Lean.restoreRecursorDecl result loweredEnv auxRec allIndNames
          allowPrimitive recName) sourceEnv |>.WF fun out =>
            out.1 = () ∧ Nonempty (StateForMTrace
              (RestoredRecursorStep result loweredEnv auxRec allIndNames)
              recNames sourceEnv out.2) := by
  apply stateForM_refines
  intro recName hrec sourceEnv
  rcases Hsources recName hrec with
    ⟨oldInfo, hlookup, Htype, Hrules⟩
  exact (restoreRecursorDecl_refines result loweredEnv sourceEnv auxRec
    allIndNames allowPrimitive recName oldInfo hlookup Htype Hrules).mono
      fun out Hout => by
        rcases out with ⟨unit, targetEnv⟩
        rcases unit with ⟨⟩
        rcases Hout with ⟨Hrestored⟩
        exact ⟨rfl, ⟨{
          oldInfo := oldInfo
          lookup := hlookup
          typeTelescope := Htype
          ruleTelescopes := Hrules
          restored := Hrestored }⟩⟩

/-- Complete operational trace for restoring one source family member: its
header, constructor list, and primary recursor. -/
structure RestoredInductiveDeclResult
    (result : Lean4Lean.ElimNestedInductive.Result)
    (loweredEnv sourceEnv : Environment) (auxRec : NameMap Name)
    (allIndNames : List Name) (indType : InductiveType)
    (oldInfo : InductiveVal) (out : Unit × Environment) where
  headerEnv : Environment
  constructorEnv : Environment
  header : RestoredInductiveHeaderDeclResult loweredEnv sourceEnv allIndNames
    indType.name oldInfo ((), headerEnv)
  constructors : StateForMTrace
    (RestoredConstructorStep result loweredEnv) oldInfo.ctors headerEnv
      constructorEnv
  recursor : RestoredRecursorStep result loweredEnv auxRec allIndNames
    (Lean.mkRecName indType.name) constructorEnv out.2
  outputUnit : out.1 = ()

theorem restoreInductiveDecl_refines
    (result : Lean4Lean.ElimNestedInductive.Result)
    (loweredEnv sourceEnv : Environment) (auxRec : NameMap Name)
    (allIndNames : List Name) (allowPrimitive : Bool)
    (indType : InductiveType) (oldInfo : InductiveVal)
    (hlookup : loweredEnv.find? indType.name = some (.inductInfo oldInfo))
    (Hctors : ∀ ctorName, ctorName ∈ oldInfo.ctors →
      ∃ ctorInfo : ConstructorVal,
        loweredEnv.find? ctorName = some (.ctorInfo ctorInfo) ∧
        RestoreTelescope ctorInfo.type result.nparams)
    (recInfo : RecursorVal)
    (hrecLookup : loweredEnv.find? (Lean.mkRecName indType.name) =
      some (.recInfo recInfo))
    (HrecType : RestoreTelescope recInfo.type result.nparams)
    (HrecRules : ∀ rule ∈ recInfo.rules,
      RestoreTelescope rule.rhs result.nparams) :
    (Lean4Lean.restoreInductiveDecl result loweredEnv auxRec allIndNames
      allowPrimitive indType sourceEnv).WF fun out =>
        Nonempty (RestoredInductiveDeclResult result loweredEnv sourceEnv
          auxRec allIndNames indType oldInfo out) := by
  have Hheader := restoreInductiveHeaderDecl_refines loweredEnv sourceEnv
    allIndNames allowPrimitive indType.name oldInfo hlookup
  have Hcombined :
      ((Lean4Lean.restoreInductiveHeaderDecl loweredEnv allIndNames
          allowPrimitive indType.name sourceEnv).bind fun headerOut =>
        ((oldInfo.ctors.forM fun ctorName =>
          Lean4Lean.restoreConstructorDecl result loweredEnv allowPrimitive
            ctorName) headerOut.2).bind fun constructorOut =>
          Lean4Lean.restoreRecursorDecl result loweredEnv auxRec allIndNames
            allowPrimitive (Lean.mkRecName indType.name) constructorOut.2).WF
        fun out => Nonempty (RestoredInductiveDeclResult result loweredEnv
          sourceEnv auxRec allIndNames indType oldInfo out) :=
    Hheader.bind fun headerOut HheaderOut => by
    rcases headerOut with ⟨unit, headerEnv⟩
    rcases unit with ⟨⟩
    rcases HheaderOut with ⟨HheaderResult⟩
    have HconstructorFold := restoreConstructorDecls_refines result loweredEnv
      allowPrimitive oldInfo.ctors Hctors headerEnv
    exact HconstructorFold.bind fun constructorOut HconstructorOut => by
      rcases constructorOut with ⟨unit, constructorEnv⟩
      rcases unit with ⟨⟩
      rcases HconstructorOut with ⟨_, ⟨HconstructorTrace⟩⟩
      have Hrecursor := restoreRecursorDecl_refines result loweredEnv
        constructorEnv auxRec allIndNames allowPrimitive
        (Lean.mkRecName indType.name) recInfo hrecLookup HrecType HrecRules
      exact Hrecursor.mono fun recursorOut HrecursorOut => by
        rcases recursorOut with ⟨unit, targetEnv⟩
        rcases unit with ⟨⟩
        rcases HrecursorOut with ⟨HrecursorResult⟩
        exact ⟨{
          headerEnv := headerEnv
          constructorEnv := constructorEnv
          header := HheaderResult
          constructors := HconstructorTrace
          recursor := {
            oldInfo := recInfo
            lookup := hrecLookup
            typeTelescope := HrecType
            ruleTelescopes := HrecRules
            restored := HrecursorResult }
          outputUnit := rfl }⟩
  simpa [Lean4Lean.restoreInductiveDecl, hlookup, bind, StateT.bind] using
    Hcombined

/-- One family member in the outer source-inductive restoration fold. -/
structure RestoredInductiveStep
    (result : Lean4Lean.ElimNestedInductive.Result)
    (loweredEnv : Environment) (auxRec : NameMap Name)
    (allIndNames : List Name) (indType : InductiveType)
    (sourceEnv targetEnv : Environment) where
  oldInfo : InductiveVal
  lookup : loweredEnv.find? indType.name = some (.inductInfo oldInfo)
  restored : RestoredInductiveDeclResult result loweredEnv sourceEnv auxRec
    allIndNames indType oldInfo ((), targetEnv)

theorem restoreInductiveDecls_refines
    (result : Lean4Lean.ElimNestedInductive.Result)
    (loweredEnv : Environment) (auxRec : NameMap Name)
    (allIndNames : List Name) (allowPrimitive : Bool)
    (types : List InductiveType)
    (Hsources : ∀ indType, indType ∈ types →
      ∃ oldInfo : InductiveVal,
        loweredEnv.find? indType.name = some (.inductInfo oldInfo) ∧
        (∀ ctorName, ctorName ∈ oldInfo.ctors →
          ∃ ctorInfo : ConstructorVal,
            loweredEnv.find? ctorName = some (.ctorInfo ctorInfo) ∧
            RestoreTelescope ctorInfo.type result.nparams) ∧
        ∃ recInfo : RecursorVal,
          loweredEnv.find? (Lean.mkRecName indType.name) =
            some (.recInfo recInfo) ∧
          RestoreTelescope recInfo.type result.nparams ∧
          ∀ rule ∈ recInfo.rules,
            RestoreTelescope rule.rhs result.nparams) :
    ∀ sourceEnv,
      (types.forM fun indType =>
        Lean4Lean.restoreInductiveDecl result loweredEnv auxRec allIndNames
          allowPrimitive indType) sourceEnv |>.WF fun out =>
            out.1 = () ∧ Nonempty (StateForMTrace
              (RestoredInductiveStep result loweredEnv auxRec allIndNames)
              types sourceEnv out.2) := by
  apply stateForM_refines
  intro indType hind sourceEnv
  rcases Hsources indType hind with
    ⟨oldInfo, hlookup, Hctors, recInfo, hrecLookup, HrecType, HrecRules⟩
  exact (restoreInductiveDecl_refines result loweredEnv sourceEnv auxRec
    allIndNames allowPrimitive indType oldInfo hlookup Hctors recInfo
    hrecLookup HrecType HrecRules).mono fun out Hout => by
      rcases out with ⟨unit, targetEnv⟩
      rcases unit with ⟨⟩
      rcases Hout with ⟨Hrestored⟩
      exact ⟨rfl, ⟨{
        oldInfo := oldInfo
        lookup := hlookup
        restored := Hrestored }⟩⟩

/-- Exact operational certificate for the two folds comprising nested
declaration restoration: source families first, then auxiliary recursors. -/
structure RestoredNestedDeclarationsResult
    (result : Lean4Lean.ElimNestedInductive.Result)
    (loweredEnv sourceEnv : Environment) (auxRec : NameMap Name)
    (allIndNames : List Name) (types : List InductiveType)
    (auxRecNames : List Name) (out : Unit × Environment) where
  primaryEnv : Environment
  inductives : StateForMTrace
    (RestoredInductiveStep result loweredEnv auxRec allIndNames)
    types sourceEnv primaryEnv
  auxiliaries : StateForMTrace
    (RestoredRecursorStep result loweredEnv auxRec allIndNames)
    auxRecNames primaryEnv out.2
  outputUnit : out.1 = ()

theorem find?_none_of_contains_false
    {env : Environment} {name : Name} (hwf : env.constants.WF)
    (hfresh : env.contains name = false) : env.find? name = none := by
  change env.constants.contains name = false at hfresh
  rw [SMap.find?_isSome] at hfresh
  rw [Lean.Kernel.Environment.find?, hwf.find?'_eq_find?]
  cases hfind : env.constants.find? name <;> simp_all

theorem StateForMTrace.constructorFreshTrace
    (H : StateForMTrace (RestoredConstructorStep result loweredEnv)
      names sourceEnv targetEnv)
    (hwf : sourceEnv.constants.WF) :
    ∃ entries, FreshConstantTrace sourceEnv entries targetEnv := by
  induction H with
  | nil => exact ⟨[], .nil⟩
  | cons Hstep Htail ih =>
    let ci : ConstantInfo := .ctorInfo Hstep.restored.newInfo
    have hfresh :=
      find?_none_of_contains_false hwf Hstep.restored.fresh
    have htarget := congrArg Prod.snd Hstep.restored.output
    simp only at htarget
    rw [htarget] at Htail ih
    rcases ih (constantsWF_add_checked hwf hfresh) with ⟨entries, Hentries⟩
    exact ⟨ci :: entries, .cons hfresh Hentries⟩

theorem StateForMTrace.recursorFreshTrace
    (H : StateForMTrace
      (RestoredRecursorStep result loweredEnv auxRec allIndNames)
      names sourceEnv targetEnv)
    (hwf : sourceEnv.constants.WF) :
    ∃ entries, FreshConstantTrace sourceEnv entries targetEnv := by
  induction H with
  | nil => exact ⟨[], .nil⟩
  | cons Hstep Htail ih =>
    let ci : ConstantInfo := .recInfo Hstep.restored.newInfo
    have hfresh :=
      find?_none_of_contains_false hwf Hstep.restored.fresh
    have htarget := congrArg Prod.snd Hstep.restored.output
    simp only at htarget
    rw [htarget] at Htail ih
    rcases ih (constantsWF_add_checked hwf hfresh) with ⟨entries, Hentries⟩
    exact ⟨ci :: entries, .cons hfresh Hentries⟩

theorem RestoredInductiveDeclResult.freshTrace
    (H : RestoredInductiveDeclResult result loweredEnv sourceEnv auxRec
      allIndNames indType oldInfo ((), targetEnv))
    (hwf : sourceEnv.constants.WF) :
    ∃ entries, FreshConstantTrace sourceEnv entries targetEnv := by
  let header : ConstantInfo := .inductInfo H.header.newInfo
  have hheaderEnv : H.headerEnv = sourceEnv.add header :=
    congrArg Prod.snd H.header.output
  have hheaderFresh : sourceEnv.find? header.name = none :=
    find?_none_of_contains_false hwf H.header.fresh
  have hwfHeader := constantsWF_add_checked hwf hheaderFresh
  have Hconstructors' : StateForMTrace
      (RestoredConstructorStep result loweredEnv) oldInfo.ctors
      (sourceEnv.add header) H.constructorEnv := by
    rw [← hheaderEnv]
    exact H.constructors
  rcases Hconstructors'.constructorFreshTrace hwfHeader with
    ⟨constructors, Hconstructors⟩
  have hwfConstructors : H.constructorEnv.constants.WF :=
    Hconstructors.targetWF hwfHeader
  let recursor : ConstantInfo := .recInfo H.recursor.restored.newInfo
  have htarget : targetEnv = H.constructorEnv.add recursor :=
    congrArg Prod.snd H.recursor.restored.output
  have hrecFresh : H.constructorEnv.find? recursor.name = none :=
    find?_none_of_contains_false hwfConstructors H.recursor.restored.fresh
  rw [htarget]
  exact ⟨header :: constructors ++ [recursor],
    FreshConstantTrace.cons hheaderFresh
      (Hconstructors.append (.cons hrecFresh .nil))⟩

theorem StateForMTrace.inductiveFreshTrace
    (H : StateForMTrace
      (RestoredInductiveStep result loweredEnv auxRec allIndNames)
      types sourceEnv targetEnv)
    (hwf : sourceEnv.constants.WF) :
    ∃ entries, FreshConstantTrace sourceEnv entries targetEnv := by
  induction H with
  | nil => exact ⟨[], .nil⟩
  | cons Hstep _Htail ih =>
    rcases Hstep.restored.freshTrace hwf with ⟨headEntries, Hhead⟩
    rcases ih (Hhead.targetWF hwf) with ⟨tailEntries, Htail⟩
    exact ⟨headEntries ++ tailEntries, Hhead.append Htail⟩

theorem RestoredNestedDeclarationsResult.freshTrace
    (H : RestoredNestedDeclarationsResult result loweredEnv sourceEnv auxRec
      allIndNames types auxRecNames out)
    (hwf : sourceEnv.constants.WF) :
    ∃ entries, FreshConstantTrace sourceEnv entries out.2 := by
  rcases H.inductives.inductiveFreshTrace hwf with
    ⟨primaryEntries, Hprimary⟩
  rcases H.auxiliaries.recursorFreshTrace (Hprimary.targetWF hwf) with
    ⟨auxiliaryEntries, Hauxiliary⟩
  exact ⟨primaryEntries ++ auxiliaryEntries,
    Hprimary.append Hauxiliary⟩

/-- The complete restored declaration order is globally name-unique.  This
is derived solely from the successful production `checkName` calls and the
two exact restoration folds. -/
theorem RestoredNestedDeclarationsResult.namesNodup
    (H : RestoredNestedDeclarationsResult result loweredEnv sourceEnv auxRec
      allIndNames types auxRecNames out)
    (hwf : sourceEnv.constants.WF) :
    ∃ entries,
      FreshConstantTrace sourceEnv entries out.2 ∧
      (entries.map (·.name)).Nodup := by
  rcases H.freshTrace hwf with ⟨entries, Hentries⟩
  exact ⟨entries, Hentries, Hentries.namesNodup hwf⟩

/-- Interpret the exact production restoration trace as a semantically typed
abstract block.  The only semantic callback is pointwise translation of that
exact trace; installation and its restoration/canonical order reconciliation
are derived here. -/
theorem RestoredNestedDeclarationsResult.restoredBlockCertificate
    (H : RestoredNestedDeclarationsResult result loweredEnv sourceProdEnv
      auxRec allIndNames types auxRecNames out)
    (hsourceWF : sourceProdEnv.constants.WF)
    (Hsemantics : ∀ entries
      (Hentries : FreshConstantTrace sourceProdEnv entries out.2),
      ∃ constants outVEnv,
        TranslatedFreshConstantTrace safety Hentries sourceVEnv constants
          outVEnv ∧
        block.types ++ block.ctors ++ block.recursors ~ constants)
    (HtypesWF : ∀ ci ∈ block.types, ci.toVConstant.WF sourceVEnv)
    (HctorsWF : ∀ envTypes,
      sourceVEnv.addConstVals block.types = some envTypes →
      ∀ ci ∈ block.ctors, ci.toVConstant.WF envTypes)
    (HrecursorsWF : ∀ envTypes envCtors,
      sourceVEnv.addConstVals block.types = some envTypes →
      envTypes.addConstVals block.ctors = some envCtors →
      ∀ ci ∈ block.recursors, ci.toVConstant.WF envCtors)
    (HrulesWF : ∀ entries
      (Hentries : FreshConstantTrace sourceProdEnv entries out.2)
      constants outVEnv,
      TranslatedFreshConstantTrace safety Hentries sourceVEnv constants
        outVEnv →
      ∀ df ∈ block.rules, df.WF outVEnv) :
    Nonempty (RestoredBlockCertificate sourceVEnv block) := by
  rcases H.freshTrace hsourceWF with ⟨entries, Hentries⟩
  rcases Hsemantics entries Hentries with
    ⟨constants, outVEnv, Htranslated, Horder⟩
  exact ⟨{
    constants := constants
    outVEnv := outVEnv
    order := Horder
    installed := Htranslated.abstract
    typesWF := HtypesWF
    ctorsWF := HctorsWF
    recursorsWF := HrecursorsWF
    rulesWF := HrulesWF entries Hentries constants outVEnv Htranslated }⟩

theorem restoreNestedDeclarations_refines
    (result : Lean4Lean.ElimNestedInductive.Result)
    (loweredEnv sourceEnv : Environment) (auxRec : NameMap Name)
    (allIndNames : List Name) (allowPrimitive : Bool)
    (types : List InductiveType) (auxRecNames : List Name)
    (Htypes : ∀ indType, indType ∈ types →
      ∃ oldInfo : InductiveVal,
        loweredEnv.find? indType.name = some (.inductInfo oldInfo) ∧
        (∀ ctorName, ctorName ∈ oldInfo.ctors →
          ∃ ctorInfo : ConstructorVal,
            loweredEnv.find? ctorName = some (.ctorInfo ctorInfo) ∧
            RestoreTelescope ctorInfo.type result.nparams) ∧
        ∃ recInfo : RecursorVal,
          loweredEnv.find? (Lean.mkRecName indType.name) =
            some (.recInfo recInfo) ∧
          RestoreTelescope recInfo.type result.nparams ∧
          ∀ rule ∈ recInfo.rules,
            RestoreTelescope rule.rhs result.nparams)
    (Haux : ∀ recName, recName ∈ auxRecNames →
      ∃ oldInfo : RecursorVal,
        loweredEnv.find? recName = some (.recInfo oldInfo) ∧
        RestoreTelescope oldInfo.type result.nparams ∧
        ∀ rule ∈ oldInfo.rules,
          RestoreTelescope rule.rhs result.nparams) :
    (Lean4Lean.restoreNestedDeclarations result loweredEnv auxRec allIndNames
      allowPrimitive types auxRecNames sourceEnv).WF fun out =>
        Nonempty (RestoredNestedDeclarationsResult result loweredEnv sourceEnv
          auxRec allIndNames types auxRecNames out) := by
  have Hinductives := restoreInductiveDecls_refines result loweredEnv auxRec
    allIndNames allowPrimitive types Htypes sourceEnv
  have Hcombined :
      (((types.forM fun indType => Lean4Lean.restoreInductiveDecl result
          loweredEnv auxRec allIndNames allowPrimitive indType) sourceEnv).bind
        fun primaryOut =>
          (auxRecNames.forM fun recName => Lean4Lean.restoreRecursorDecl result
            loweredEnv auxRec allIndNames allowPrimitive recName)
            primaryOut.2).WF fun out =>
              Nonempty (RestoredNestedDeclarationsResult result loweredEnv
                sourceEnv auxRec allIndNames types auxRecNames out) :=
    Hinductives.bind fun primaryOut Hprimary => by
      rcases primaryOut with ⟨unit, primaryEnv⟩
      rcases unit with ⟨⟩
      rcases Hprimary with ⟨_, ⟨HinductiveTrace⟩⟩
      have Hauxiliaries := restoreRecursorDecls_refines result loweredEnv
        auxRec allIndNames allowPrimitive auxRecNames Haux primaryEnv
      exact Hauxiliaries.mono fun out Hout => by
        rcases Hout with ⟨hunit, ⟨HauxTrace⟩⟩
        exact ⟨{
          primaryEnv := primaryEnv
          inductives := HinductiveTrace
          auxiliaries := HauxTrace
          outputUnit := hunit }⟩
  simpa [Lean4Lean.restoreNestedDeclarations, bind, StateT.bind] using Hcombined


end VerifyInductive
end Lean4Lean
