import Lean4Lean.Verify.Inductive.Header.Translation
import Lean4Lean.Verify.Inductive.Header.Block

/-!
# The checked headers of a mutual block

`CheckedHeaders` is the ordered accumulator of the header phase: for each source family its
checked translation and its `HeaderFormation`, independent of any declaration skeleton.
-/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive
namespace checkInductiveTypes.loopType

def headerSkeleton (target : VConstVal) : VInductiveTypeSkeleton where
  toVConstVal := target
  ctors := []

/-- One source-aligned semantic header payload.  Its constructor list is
deliberately empty; `retarget` attaches the same proof to the final
constructor-bearing skeleton. -/
structure CheckedHeader
    (env : VEnv) (Us : List Name) (nparams : Nat)
    (params : List VExpr) (commonLevel : VLevel)
    (source : InductiveType) where
  target : VConstVal
  numIndices : Nat
  resultLevel : VLevel
  translation : TrSourceConst env Us source.name source.type target
  formation : HeaderFormation env Us Us.length nparams params
    (headerSkeleton target) numIndices resultLevel
  commonLevel : resultLevel ≈ commonLevel

/-- Ordered semantic outputs of the skeleton-free mutual-header traversal. -/
structure CheckedHeaders
    (env : VEnv) (Us : List Name) (nparams : Nat)
    (params : List VExpr) (commonLevel : VLevel)
    (sources : List InductiveType) where
  payloads : List (Sigma fun source =>
    CheckedHeader env Us nparams params commonLevel source)
  sourceOrder : payloads.map Sigma.fst = sources

namespace CheckedHeaders

/-- Retarget only the source-list index along an exact ordering equality.
The semantic payloads themselves are copied definitionally, so projections
such as `metadata` remain reducible across the reindexing. -/
def reindexSources
    (H : CheckedHeaders env Us nparams params
      commonLevel sources)
    (h : sources = sources') :
    CheckedHeaders env Us nparams params
      commonLevel sources' where
  payloads := H.payloads
  sourceOrder := H.sourceOrder.trans h

/-- Retarget universe-parameter names along equality without changing any
recovered semantic data. -/
def reindexUs
    (H : CheckedHeaders env Us nparams params
      commonLevel sources)
    (h : Us = Us') :
    CheckedHeaders env Us' nparams params
      commonLevel sources := by
  cases h
  exact H

def first (source : InductiveType) (target : VConstVal)
    (numIndices : Nat) (resultLevel : VLevel)
    (Htranslation : TrSourceConst env Us source.name source.type target)
    (Hsynthesized : HeaderFormation env Us Us.length nparams params
      (headerSkeleton target) numIndices resultLevel) :
    CheckedHeaders env Us nparams params
      resultLevel [source] where
  payloads := [⟨source, target, numIndices, resultLevel, Htranslation,
    Hsynthesized, by rfl⟩]
  sourceOrder := rfl

def snoc
    (H : CheckedHeaders env Us nparams params
      commonLevel sources)
    (source : InductiveType) (target : VConstVal)
    (numIndices : Nat) (resultLevel : VLevel)
    (Htranslation : TrSourceConst env Us source.name source.type target)
    (Hsynthesized : HeaderFormation env Us Us.length nparams params
      (headerSkeleton target) numIndices resultLevel)
    (hlevel : resultLevel ≈ commonLevel) :
    CheckedHeaders env Us nparams params
      commonLevel (sources ++ [source]) where
  payloads := H.payloads ++ [⟨source, target, numIndices, resultLevel,
    Htranslation, Hsynthesized, hlevel⟩]
  sourceOrder := by simp [H.sourceOrder]

def headers
    (H : CheckedHeaders env Us nparams params
      commonLevel sources) :
    HeaderTranslations env Us sources := by
  have go : ∀ payloads : List (Sigma fun source =>
      CheckedHeader env Us nparams params commonLevel
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
    (H : CheckedHeaders env Us nparams params
      commonLevel sources) : List (Nat × VLevel) :=
  H.payloads.map fun payload =>
    (payload.2.numIndices, payload.2.resultLevel)

@[simp] theorem metadata_reindexSources
    (H : CheckedHeaders env Us nparams params
      commonLevel sources) (h : sources = sources') :
    (H.reindexSources h).metadata = H.metadata := rfl

@[simp] theorem metadata_reindexUs
    (H : CheckedHeaders env Us nparams params
      commonLevel sources) (h : Us = Us') :
    (H.reindexUs h).metadata = H.metadata := by cases h; rfl

@[simp] theorem metadata_snoc
    (H : CheckedHeaders env Us nparams params
      commonLevel sources)
    (source : InductiveType) (target : VConstVal)
    (nindices : Nat) (resultLevel : VLevel)
    (Htranslation : TrSourceConst env Us source.name source.type target)
    (Hsynthesized : HeaderFormation env Us Us.length nparams params
      (headerSkeleton target) nindices resultLevel)
    (hlevel : resultLevel ≈ commonLevel) :
    (H.snoc source target nindices resultLevel Htranslation Hsynthesized
      hlevel).metadata = H.metadata ++ [(nindices, resultLevel)] := by
  simp [snoc, metadata]

end CheckedHeaders

end checkInductiveTypes.loopType
end VerifyInductive
end Lean4Lean

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

namespace checkInductiveTypes.loopInd

/-- Retarget the runtime scope of a header result (`HeaderStatsWF`) along exact
scope equality.  Data projections are preserved definitionally after
eliminating the equality, which avoids opaque dependent casts at installed
environment boundaries. -/
def HeaderStatsWF.retargetScope
    (H : HeaderStatsWF env Us Δ stats decl depth)
    (h : Δ = Δ') : HeaderStatsWF env Us Δ' stats decl depth := by
  cases h
  exact H

@[simp] theorem HeaderStatsWF.retargetScope_headers_params
    (H : HeaderStatsWF env Us Δ stats decl depth)
    (h : Δ = Δ') :
    (H.retargetScope h).headers.params = H.headers.params := by
  cases h
  rfl

@[simp] theorem HeaderStatsWF.retargetScope_parameterScope
    (H : HeaderStatsWF env Us Δ stats decl depth)
    (h : Δ = Δ') :
    (H.retargetScope h).parameterScope = H.parameterScope := by
  cases h
  rfl

@[simp] theorem HeaderStatsWF.mono_parameterScope
    (H : HeaderStatsWF env Us Δ stats decl depth)
    (henv : env ≤ env') :
    (H.mono henv).parameterScope = H.parameterScope := rfl

@[simp] theorem HeaderStatsWF.mono_headers_params
    (H : HeaderStatsWF env Us Δ stats decl depth)
    (henv : env ≤ env') :
    (H.mono henv).headers.params = H.headers.params := rfl

end checkInductiveTypes.loopInd

namespace checkInductiveTypes.loopType

end checkInductiveTypes.loopType
end VerifyInductive
end Lean4Lean
