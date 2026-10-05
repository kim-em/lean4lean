import Lean4Lean.Theory.Typing.AnchoredSortableCert
import Lean4Lean.Theory.Typing.AnchoredOriginalSortableTail
import Lean4Lean.Theory.Typing.AnchoredOriginalCoherenceContract
import Lean4Lean.Theory.Typing.AnchoredOriginalSortableRetraction
import Lean4Lean.Theory.Typing.AnchoredSortableCodeIntroduction

/-! Separate formation-query induction contracts. They neither replace nor
follow from the old fundamental/coherence clauses. Native sortable Pi rows
and their whole argument cuts require this additional mutually produced
output; all source states and contexts remain actual original occurrences. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
open OriginalClosureMeasure OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false

structure SortableTransferResult (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (locals : List Nat) (σ τ : Subst) (valuation : Valuation)
    (left right : VExpr) (relevant : Bool) (profile : Profile n) where
  footprint : Footprint
  certificate : SortableCert env U registry target locals τ right relevant profile footprint
  available : footprint.Available valuation
  related : TypeRelated env U registry target (left.subst σ) (right.subst τ) profile

/-- Whole sortable cuts remain typed at the original argument's actual
assigned type. The outgoing query is not coerced to a legacy observation. -/
structure SortableTermTransferResult (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (locals : List Nat) (σ τ : Subst) (valuation : Valuation)
    (left right assigned : VExpr) (relevant : Bool) (profile : Profile n)
    extends SortableTransferResult env U registry target locals σ τ valuation left right relevant profile where
  support : Profile n
  typeFootprint : Footprint
  typeCertificate : SortableCert env U registry target locals σ assigned true support typeFootprint
  typeAvailable : typeFootprint.Available valuation
  typed : profile.HasType support
  typeCode : TypeRelated env U registry target (assigned.subst σ) (assigned.subst σ) support
  termRelated : Related env U registry target (left.subst σ) (right.subst τ)
    (assigned.subst σ) profile support

def SortableTransfer (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (locals : List Nat) (σ τ : Subst) (available : Valuation)
    (left right assigned : VExpr) : Prop :=
  ∀ {relevant : Bool} {n : Nat} {profile : Profile n} {footprint : Footprint},
    SortableCert env U registry target locals σ left relevant profile footprint →
    footprint.Available available →
    Nonempty (SortableTermTransferResult env U registry target locals σ τ available
      left right assigned relevant profile)

/-- This is an additional original F motive, not an upgrade of StateFundamental. -/
def OriginalTail.StateSortableFundamental
    (env : VEnv) (registry : CanonicalHead.Registry)
    (context : ContextDerivation sourceEnv U source)
    (node : EndpointState sourceEnv U source expression assigned) : Prop :=
  ∀ (target : List VExpr) (locals : List Nat) (σ τ : Subst) (available : Valuation),
    available.AtomClosed → OnCtx target (env.IsType U) →
    Ctx.SubstEq env U target σ τ source →
    SortableTailPairedFits env registry target context locals σ τ available →
    SortableTransfer env U registry target locals σ τ available expression expression assigned

def OriginalTail.DerivationSortableFundamental
    (env : VEnv) (registry : CanonicalHead.Registry)
    (context : ContextDerivation sourceEnv U source)
    (original : Derivation sourceEnv U source left right assigned) : Prop :=
  ∀ (target : List VExpr) (locals : List Nat) (σ τ : Subst) (available : Valuation),
    available.AtomClosed → OnCtx target (env.IsType U) →
    Ctx.SubstEq env U target σ τ source →
    SortableTailPairedFits env registry target context locals σ τ available →
    SortableTransfer env U registry target locals σ τ available left right assigned ∧
      SortableTransfer env U registry target locals σ τ available right left assigned

structure OriginalEndpointFactor.SortableDisplayFits
    (env : VEnv) (registry : CanonicalHead.Registry) (target : List VExpr)
    {sourceEnv : VEnv} {U : Nat} {Γ : List VExpr} {expression assigned : VExpr}
    (display : EndpointDisplay sourceEnv U Γ expression assigned)
    (common : Subst) (available : Valuation) (locals : List Nat) where
  fits : SortableTailFits sourceEnv env U registry target display.source locals
    (display.sourceSubst common) (display.sourceSubst common) (display.sourceValuation available)
  original : fits.contextDerivation = display.context
  substitutions : Ctx.SubstEq env U target
    (display.sourceSubst common) (display.sourceSubst common) display.source

/-- The added C channel answers formation queries at either sort flag.
Raw paths and legacy CodeCert queries stay in their existing contract. -/
def OriginalEndpointFactor.DisplaySortableCoherence
    (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    {leftEnv rightEnv : VEnv} {Γ : List VExpr} {expression leftType rightType : VExpr}
    (left : EndpointDisplay leftEnv U Γ expression leftType)
    (right : EndpointDisplay rightEnv U Γ expression rightType) : Prop :=
  ∀ (target : List VExpr) (common : Subst) (available : Valuation)
    (leftLocals rightLocals : List Nat), available.AtomClosed → OnCtx target (env.IsType U) →
    SortableDisplayFits env registry target left common available leftLocals →
    SortableDisplayFits env registry target right common available rightLocals →
    ∀ {relevant : Bool} {n : Nat} {profile : Profile n} {footprint : Footprint},
      SortableCert env U registry target leftLocals (left.sourceSubst common)
        left.sourceType relevant profile footprint →
      footprint.Available (left.sourceValuation available) →
      Nonempty (SortableTransferResult env U registry target rightLocals
        (left.sourceSubst common) (right.sourceSubst common) (right.sourceValuation available)
        left.sourceType right.sourceType relevant profile)

/-- Actual old F suffices for seeds, including false families. It is not
claimed to interpret the new native Pi constructor. -/
theorem SortableTermTransferResult.ofObservation
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (closed : available.AtomClosed) (formed : OnCtx target (env.IsType U))
    (observation : Obs env U registry target locals σ left profile footprint)
    (sortable : profile.HasType (.sort relevant))
    (resources : footprint.Available available)
    (transfer : GradedTransfer env U registry target locals σ τ available left right assigned) :
    Nonempty (SortableTermTransferResult env U registry target locals σ τ available
      left right assigned relevant profile) := by
  obtain ⟨answer⟩ := transfer observation resources
  have relation := answer.requestedRelated henv formed
  have code := relation.code_of_sortable henv hscoped formed sortable
  let intermediate : SortableQueryResult env U registry target locals σ τ available left right profile := {
    result := {
      rank := answer.rank, bound := answer.bound, raw := answer.rawDemand
      footprint := answer.resultFootprint, observation := answer.observation
      adapter := answer.adapter, resources := answer.resultAvailable
      live := answer.rawRelated.live henv hscoped formed }
    related := code }
  obtain ⟨nextFootprint, ⟨next⟩, nextAvailable⟩ := intermediate.exactObservation henv closed sortable
  exact ⟨{
    footprint := nextFootprint, certificate := .seed next sortable
    available := nextAvailable, related := code
    support := lowerProfile _ answer.bound answer.support
    typeFootprint := answer.typeFootprint, typeCertificate := .ofCode answer.requestedCertificate answer.requestedCertificate.formed
    typeAvailable := answer.typeAvailable, typed := answer.requestedTyped
    typeCode := answer.typeCode.lower henv answer.bound
    termRelated := relation }⟩

end Lean4Lean.AnchoredSource.Adapted
