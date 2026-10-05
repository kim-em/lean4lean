import Lean4Lean.Theory.Typing.AnchoredSourceCodeCert
import Lean4Lean.Theory.Typing.SourcePiFormation

/-! The joint source contract and its concrete variable-lookup producer.
These are definitions of the intended original-derivation induction motive,
not a claim that the fundamental theorem has been proved. A fitting valuation
retains source type-certificate provenance as well as target relatedness.
Raw typed substitutions are a separate hypothesis of the joint contract. -/

namespace Lean4Lean.AnchoredSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

/-- Evidence for one actually available variable demand. `sourceType` is the
full type returned by source-context lookup, including its de Bruijn lifts.
Its certificate uses the same external valuation as the demanded variable. -/
structure ValuationEntry (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (locals : List Nat) (left right : Subst)
    (available : Valuation) (index : Nat) (need : Need) (sourceType : VExpr) where
  support : Profile need.rank
  footprint : Footprint
  certificate : CodeCert env U registry target locals left sourceType support footprint
  available : footprint.Available available
  typed : need.profile.HasType support
  related : Related env U registry target (left index) (right index)
    (sourceType.subst left) need.profile support

/-- Every available lookup demand has an actual source type certificate.
There is no universal semantic producer stored in an entry. -/
structure Fits (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (source target : List VExpr) (locals : List Nat) (left right : Subst)
    (available : Valuation) : Prop where
  entry : ∀ index need, need ∈ available index → ∀ sourceType,
    Lookup source index sourceType →
      Nonempty (ValuationEntry env U registry target locals left right
        available index need sourceType)

/-- Transfer one computational observation while retaining support provenance
for its ACTUAL assigned source type. The returned footprints need only be
available in the fixed valuation; they need not equal the input footprint. -/
structure TransferResult (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (locals : List Nat) (leftSubst rightSubst : Subst)
    (available : Valuation) (left right sourceType : VExpr) (demand : Profile n) where
  resultFootprint : Footprint
  observation : Obs env U registry target locals rightSubst right demand resultFootprint
  resultAvailable : resultFootprint.Available available
  support : Profile n
  typeFootprint : Footprint
  certificate : CodeCert env U registry target locals leftSubst sourceType support typeFootprint
  typeAvailable : typeFootprint.Available available
  typed : demand.HasType support
  related : Related env U registry target (left.subst leftSubst) (right.subst rightSubst)
    (sourceType.subst leftSubst) demand support

def Transfer (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (locals : List Nat) (leftSubst rightSubst : Subst)
    (available : Valuation) (left right sourceType : VExpr) : Prop :=
  ∀ {n : Nat} {demand : Profile n} {footprint : Footprint},
    Obs env U registry target locals leftSubst left demand footprint →
    footprint.Available available →
      Nonempty (TransferResult env U registry target locals leftSubst rightSubst
        available left right sourceType demand)

/-- Original formation children must also enforce the actual universe's
relevance. The intrinsic `CodeCert.formed` invariant alone does not do this. -/
def SortCorrect (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (locals : List Nat) (realization : Subst)
    (available : Valuation) (expression sourceType : VExpr) : Prop :=
  ∀ level relevant, sourceType = .sort level → Relevant level relevant →
    ∀ {n : Nat} {demand : Profile n} {footprint : Footprint},
      Obs env U registry target locals realization expression demand footprint →
      footprint.Available available → demand.HasType (.sort relevant)

/-- Both endpoint directions use the same paired valuation. Equality symmetry
exchanges these clauses; transitivity can first use a diagonal left valuation.
The predicate is the intended induction result, not an available theorem. -/
def Joint (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (source : List VExpr) (left right sourceType : VExpr) : Prop :=
  ∀ (target : List VExpr) (locals : List Nat) (leftSubst rightSubst : Subst)
    (available : Valuation), OnCtx target (env.IsType U) →
    Ctx.SubstEq env U target leftSubst rightSubst source →
    Fits env U registry source target locals leftSubst rightSubst available →
      Transfer env U registry target locals leftSubst rightSubst available left right sourceType ∧
      Transfer env U registry target locals leftSubst rightSubst available right left sourceType ∧
      SortCorrect env U registry target locals leftSubst available left sourceType ∧
      SortCorrect env U registry target locals leftSubst available right sourceType

/-- Source Pi components retain the joint results of original formation
children. They must be populated during strong-derivation induction; the
returned raw proofs are not recursively interpreted as fresh children. -/
def FundamentalMotive (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    {source : List VExpr} {left right sourceType : VExpr}
    (_original : env.IsDefEqStrong U source left right sourceType) : Prop :=
  Joint env U registry source left right sourceType ∧
  SourcePiFormation (fun Γ e A => Joint env U registry Γ e e A) source left ∧
  SourcePiFormation (fun Γ e A => Joint env U registry Γ e e A) source right

/-- The lookup leaf of the original strong bvar case is supplied entirely by
the fitting entry. Transformations of a variable observation still require
separate structural cases; this is not the full bvar joint theorem. -/
theorem Fits.bvar
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {source target : List VExpr} {locals : List Nat} {leftSubst rightSubst : Subst}
    {available : Valuation} {index : Nat} {sourceType : VExpr} {demand : Profile n}
    (fits : Fits env U registry source target locals leftSubst rightSubst available)
    (lookup : Lookup source index sourceType)
    (required : Footprint.Available [(index, ⟨n, demand⟩)] available) :
    Nonempty (TransferResult env U registry target locals leftSubst rightSubst
      available (.bvar index) (.bvar index) sourceType demand) := by
  obtain ⟨entry⟩ := fits.entry index ⟨n, demand⟩
    (required index ⟨n, demand⟩ (List.mem_singleton_self _)) sourceType lookup
  exact ⟨{
    resultFootprint := [(index, ⟨n, demand⟩)]
    observation := .var locals rightSubst index demand
    resultAvailable := required
    support := entry.support
    typeFootprint := entry.footprint
    certificate := entry.certificate
    typeAvailable := entry.available
    typed := entry.typed
    related := entry.related }⟩

end Lean4Lean.AnchoredSource
