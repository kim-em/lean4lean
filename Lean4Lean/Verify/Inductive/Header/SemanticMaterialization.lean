import Lean4Lean.Verify.Inductive.Header.MaterializedFold

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive
namespace checkInductiveTypes.loopType

def headerSkeleton (target : VConstVal) : VInductiveTypeSkeleton where
  toVConstVal := target
  ctors := []

/-- Constructor payloads are irrelevant to header formation.  A synthesized
header can therefore be attached to the final skeleton once its constructor
targets have been recovered. -/
theorem SynthesizedHeader.retarget
    (H : SynthesizedHeader env Us uvars nparams params source
      nindices resultLevel)
    (htarget : target.toVConstVal = source.toVConstVal) :
    SynthesizedHeader env Us uvars nparams params target
      nindices resultLevel where
  parameterCount := H.parameterCount
  levelCount := H.levelCount
  normalizedSource := H.normalizedSource
  typeShape decl huvars hnparams := by
    have Hshape := H.typeShape decl huvars hnparams
    rcases source with ⟨sourceVal, sourceCtors⟩
    rcases target with ⟨targetVal, targetCtors⟩
    simp only at htarget
    subst targetVal
    exact Hshape

def SynthesizedHeader.mono {env env' : VEnv}
    (henv : env ≤ env')
    (H : SynthesizedHeader env Us uvars nparams params source
      nindices resultLevel) :
    SynthesizedHeader env' Us uvars nparams params source
      nindices resultLevel where
  parameterCount := H.parameterCount
  levelCount := H.levelCount
  normalizedSource :=
    ⟨(Classical.choice H.normalizedSource).mono henv⟩
  typeShape decl huvars hnparams :=
    (H.typeShape decl huvars hnparams).mono henv

/-- One source-aligned semantic header payload.  Its constructor list is
deliberately empty; `retarget` attaches the same proof to the final
constructor-bearing skeleton. -/
structure MaterializedSourceHeaderSemantics
    (env : VEnv) (Us : List Name) (nparams : Nat)
    (params : List VExpr) (commonLevel : VLevel)
    (source : InductiveType) where
  target : VConstVal
  numIndices : Nat
  resultLevel : VLevel
  translation : TrSourceConst env Us source.name source.type target
  synthesized : SynthesizedHeader env Us Us.length nparams params
    (headerSkeleton target) numIndices resultLevel
  commonLevel : resultLevel ≈ commonLevel

def MaterializedSourceHeaderSemantics.headerType
    (H : MaterializedSourceHeaderSemantics env Us nparams params
      commonResultLevel source) : VInductiveType :=
  (headerSkeleton H.target).toVInductiveType H.numIndices H.resultLevel

def MaterializedSourceHeaderSemantics.mono {env env' : VEnv}
    (henv : env ≤ env')
    (H : MaterializedSourceHeaderSemantics env Us nparams params
      commonResultLevel source) :
    MaterializedSourceHeaderSemantics env' Us nparams params
      commonResultLevel source where
  target := H.target
  numIndices := H.numIndices
  resultLevel := H.resultLevel
  translation := H.translation.mono henv
  synthesized := H.synthesized.mono henv
  commonLevel := H.commonLevel

/-- Ordered semantic outputs of the skeleton-free mutual-header traversal. -/
structure MaterializedSourceHeaderSemanticAccumulator
    (env : VEnv) (Us : List Name) (nparams : Nat)
    (params : List VExpr) (commonLevel : VLevel)
    (sources : List InductiveType) where
  payloads : List (Sigma fun source =>
    MaterializedSourceHeaderSemantics env Us nparams params commonLevel source)
  sourceOrder : payloads.map Sigma.fst = sources

namespace MaterializedSourceHeaderSemanticAccumulator

/-- Retarget only the source-list index along an exact ordering equality.
The semantic payloads themselves are copied definitionally, so projections
such as `metadata` remain reducible across the reindexing. -/
def reindexSources
    (H : MaterializedSourceHeaderSemanticAccumulator env Us nparams params
      commonLevel sources)
    (h : sources = sources') :
    MaterializedSourceHeaderSemanticAccumulator env Us nparams params
      commonLevel sources' where
  payloads := H.payloads
  sourceOrder := H.sourceOrder.trans h

/-- Retarget universe-parameter names along equality without changing any
recovered semantic data. -/
def reindexUs
    (H : MaterializedSourceHeaderSemanticAccumulator env Us nparams params
      commonLevel sources)
    (h : Us = Us') :
    MaterializedSourceHeaderSemanticAccumulator env Us' nparams params
      commonLevel sources := by
  cases h
  exact H

def mono {env env' : VEnv} (henv : env ≤ env')
    (H : MaterializedSourceHeaderSemanticAccumulator env Us nparams params
      commonLevel sources) :
    MaterializedSourceHeaderSemanticAccumulator env' Us nparams params
      commonLevel sources where
  payloads := H.payloads.map fun payload =>
    ⟨payload.1, payload.2.mono henv⟩
  sourceOrder := by
    rw [List.map_map]
    exact H.sourceOrder

def first (source : InductiveType) (target : VConstVal)
    (numIndices : Nat) (resultLevel : VLevel)
    (Htranslation : TrSourceConst env Us source.name source.type target)
    (Hsynthesized : SynthesizedHeader env Us Us.length nparams params
      (headerSkeleton target) numIndices resultLevel) :
    MaterializedSourceHeaderSemanticAccumulator env Us nparams params
      resultLevel [source] where
  payloads := [⟨source, target, numIndices, resultLevel, Htranslation,
    Hsynthesized, by rfl⟩]
  sourceOrder := rfl

def snoc
    (H : MaterializedSourceHeaderSemanticAccumulator env Us nparams params
      commonLevel sources)
    (source : InductiveType) (target : VConstVal)
    (numIndices : Nat) (resultLevel : VLevel)
    (Htranslation : TrSourceConst env Us source.name source.type target)
    (Hsynthesized : SynthesizedHeader env Us Us.length nparams params
      (headerSkeleton target) numIndices resultLevel)
    (hlevel : resultLevel ≈ commonLevel) :
    MaterializedSourceHeaderSemanticAccumulator env Us nparams params
      commonLevel (sources ++ [source]) where
  payloads := H.payloads ++ [⟨source, target, numIndices, resultLevel,
    Htranslation, Hsynthesized, hlevel⟩]
  sourceOrder := by simp [H.sourceOrder]

def headers
    (H : MaterializedSourceHeaderSemanticAccumulator env Us nparams params
      commonLevel sources) :
    MaterializedSourceHeaderAccumulator env Us sources := by
  have go : ∀ payloads : List (Sigma fun source =>
      MaterializedSourceHeaderSemantics env Us nparams params commonLevel
        source),
      List.Forall₂
        (fun source target =>
          TrSourceConst env Us source.name source.type target)
        (payloads.map Sigma.fst)
        (payloads.map fun payload => payload.2.target) := by
    intro payloads
    induction payloads with
    | nil => exact .nil
    | cons payload payloads ih =>
      rcases payload with ⟨source, payload⟩
      exact .cons payload.translation ih
  refine {
    targets := H.payloads.map fun payload => payload.2.target
    translations := ?_ }
  exact Eq.mp (congrArg (fun orderedSources =>
    List.Forall₂
      (fun source target =>
        TrSourceConst env Us source.name source.type target)
      orderedSources (H.payloads.map fun payload => payload.2.target))
    H.sourceOrder) (go H.payloads)

def metadata
    (H : MaterializedSourceHeaderSemanticAccumulator env Us nparams params
      commonLevel sources) : List (Nat × VLevel) :=
  H.payloads.map fun payload =>
    (payload.2.numIndices, payload.2.resultLevel)

@[simp] theorem metadata_reindexSources
    (H : MaterializedSourceHeaderSemanticAccumulator env Us nparams params
      commonLevel sources) (h : sources = sources') :
    (H.reindexSources h).metadata = H.metadata := rfl

@[simp] theorem metadata_reindexUs
    (H : MaterializedSourceHeaderSemanticAccumulator env Us nparams params
      commonLevel sources) (h : Us = Us') :
    (H.reindexUs h).metadata = H.metadata := by cases h; rfl

@[simp] theorem metadata_snoc
    (H : MaterializedSourceHeaderSemanticAccumulator env Us nparams params
      commonLevel sources)
    (source : InductiveType) (target : VConstVal)
    (nindices : Nat) (resultLevel : VLevel)
    (Htranslation : TrSourceConst env Us source.name source.type target)
    (Hsynthesized : SynthesizedHeader env Us Us.length nparams params
      (headerSkeleton target) nindices resultLevel)
    (hlevel : resultLevel ≈ commonLevel) :
    (H.snoc source target nindices resultLevel Htranslation Hsynthesized
      hlevel).metadata = H.metadata ++ [(nindices, resultLevel)] := by
  simp [snoc, metadata]

/-- The header-phase declaration has the final family constants and semantic
metadata, but deliberately no constructor constants yet. -/
def headerDecl
    (H : MaterializedSourceHeaderSemanticAccumulator env Us nparams params
      commonLevel sources)
    (isUnsafe : Bool) : VInductDecl where
  uvars := Us.length
  nparams := nparams
  types := H.payloads.map fun payload => payload.2.headerType
  isUnsafe := isUnsafe

@[simp] theorem headerDecl_typeConstants
    (H : MaterializedSourceHeaderSemanticAccumulator env Us nparams params
      commonLevel sources) :
    (H.headerDecl isUnsafe).typeConstants = H.headers.targets := by
  simp [headerDecl, VInductDecl.typeConstants,
    MaterializedSourceHeaderSemantics.headerType, headerSkeleton, headers]
  intro payload _hpayload
  rcases payload with ⟨source, payload⟩
  rfl

/-- The retained per-family synthesis proofs assemble directly into the
abstract header certificate for the header-only declaration.  In particular
each `normalizedSource` remains available through the originating payload. -/
def headerCertificate
    (H : MaterializedSourceHeaderSemanticAccumulator env Us nparams params
      commonLevel sources)
    (isUnsafe : Bool) : HeaderCertificate env (H.headerDecl isUnsafe) where
  params := params
  resultLevel := commonLevel
  commonLevels type htype := by
    simp only [headerDecl, List.mem_map] at htype
    rcases htype with ⟨payload, _hpayload, rfl⟩
    exact payload.2.commonLevel
  typeShapes type htype := by
    simp only [headerDecl, List.mem_map] at htype
    rcases htype with ⟨payload, _hpayload, rfl⟩
    exact payload.2.synthesized.typeShape (H.headerDecl isUnsafe) rfl rfl

/-- Attach the semantic payloads to any constructor-bearing skeleton with
the same ordered header constants. -/
theorem toSynthesizedPrefix
    (H : MaterializedSourceHeaderSemanticAccumulator env Us nparams params
      commonLevel sources)
    (skeleton : VInductDeclSkeleton)
    (huvars : skeleton.uvars = Us.length)
    (hnparams : skeleton.nparams = nparams)
    (hparams : params.length = skeleton.nparams)
    (htypes : skeleton.typeConstants = H.headers.targets) :
    SynthesizedHeaderPrefix env Us skeleton params commonLevel H.metadata
      skeleton.types.length := by
  have hpayloadLength : H.payloads.length = skeleton.types.length := by
    have hlength := congrArg List.length htypes
    simpa [VInductDeclSkeleton.typeConstants, headers] using hlength.symm
  refine {
    parameterCount := hparams
    covered := Nat.le_refl _
    checked := ?_ }
  apply List.forall₂_of_getElem
  · simp [metadata, hpayloadLength]
  · intro i hiType hiData
    have hiSkeleton : i < skeleton.types.length := by simpa using hiType
    have hiPayload : i < H.payloads.length := by
      simpa [hpayloadLength] using hiSkeleton
    let payload := H.payloads[i]
    have htarget : skeleton.types[i].toVConstVal = payload.2.target := by
      have hget := congrArg (fun values => values[i]?) htypes
      simp [VInductDeclSkeleton.typeConstants, headers, payload,
        hiPayload] at hget
      rcases hget with ⟨target, htarget, hvalue⟩
      rw [List.getElem?_eq_getElem hiSkeleton] at htarget
      have := Option.some.inj htarget
      subst target
      simpa [payload] using hvalue
    have hmetadata : H.metadata[i] =
        (payload.2.numIndices, payload.2.resultLevel) := by
      simp [metadata, payload, hiPayload]
    have Hheader := payload.2.synthesized.retarget htarget
    rw [hmetadata]
    exact {
      header := by simpa [huvars, hnparams] using Hheader
      commonLevel := payload.2.commonLevel }

end MaterializedSourceHeaderSemanticAccumulator

end checkInductiveTypes.loopType
end VerifyInductive
end Lean4Lean
