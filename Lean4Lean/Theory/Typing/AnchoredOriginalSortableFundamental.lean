import Lean4Lean.Theory.Typing.AnchoredOriginalSortableContract
import Lean4Lean.Theory.Typing.AnchoredSortableGradedResult

/-! The genuinely hereditary computational F output. Its source observer,
assigned-type support, and source-tail frames all use the richer grammar.
The formation-only output is a checked consequence of this output, not an
upgrade of the legacy fundamental theorem. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
open OriginalClosureMeasure OriginalTail
set_option backward.isDefEq.respectTransparency false

structure SortableComputationalTransferResult (env : VEnv) (U : Nat)
    (registry : CanonicalHead.Registry) (target : List VExpr) (locals : List Nat)
    (σ τ : Subst) (available : Valuation) (left right assigned : VExpr) (demand : Profile n)
    extends SortableGradedResult env U registry target locals τ available right demand where
  support : Profile rank
  typeFootprint : Footprint
  typeCertificate : SortableCert env U registry target locals σ assigned true support typeFootprint
  typeAvailable : typeFootprint.Available available
  typed : (raiseProfile rank bound demand).HasType support
  rawTyped : raw.HasType support
  typeCode : TypeRelated env U registry target (assigned.subst σ) (assigned.subst σ) support
  related : Related env U registry target (left.subst σ) (right.subst τ)
    (assigned.subst σ) (raiseProfile rank bound demand) support
  rawRelated : Related env U registry target (right.subst τ) (right.subst τ)
    (assigned.subst σ) raw support

def SortableComputationalTransfer (env : VEnv) (U : Nat)
    (registry : CanonicalHead.Registry) (target : List VExpr) (locals : List Nat)
    (σ τ : Subst) (available : Valuation) (left right assigned : VExpr) : Prop :=
  ∀ {n : Nat} {demand : Profile n} {footprint : Footprint},
    SortableObs env U registry target locals σ left demand footprint →
    footprint.Available available →
    Nonempty (SortableComputationalTransferResult env U registry target locals σ τ available
      left right assigned demand)

/-- Source-sortable queries are interpreted by the stronger actual observer
clause, including native Pi rows and new whole-expression cuts. -/
theorem SortableComputationalTransfer.sortable
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (closed : available.AtomClosed) (formed : OnCtx target (env.IsType U))
    (transfer : SortableComputationalTransfer env U registry target locals σ τ available
      left right assigned) :
    SortableTransfer env U registry target locals σ τ available left right assigned := by
  intro relevant n profile footprint certificate resources
  obtain ⟨answer⟩ := transfer (.code relevant certificate) resources
  obtain ⟨nextFootprint, ⟨next⟩, nextAvailable⟩ :=
    answer.toSortableGradedResult.code henv closed certificate.formed
  have relation := lowerProfile.related answer.bound henv formed answer.related
  exact ⟨{
    footprint := nextFootprint, certificate := next, available := nextAvailable
    related := relation.code_of_sortable henv hscoped formed certificate.formed
    support := lowerProfile n answer.bound answer.support
    typeFootprint := answer.typeFootprint
    typeCertificate := answer.typeCertificate.lower n answer.bound
    typeAvailable := answer.typeAvailable
    typed := lowerProfile.hasType answer.bound answer.typed
    typeCode := answer.typeCode.lower henv answer.bound
    termRelated := relation }⟩

/-- A finite legacy answer embeds soundly. This does not turn richer source
frames into legacy source frames. -/
noncomputable def SortableComputationalTransferResult.ofLegacy
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (formed : OnCtx target (env.IsType U))
    (answer : GradedTransferResult env U registry target locals σ τ available
      left right assigned demand) :
    SortableComputationalTransferResult env U registry target locals σ τ available
      left right assigned demand where
  rank := answer.rank
  bound := answer.bound
  raw := answer.rawDemand
  footprint := answer.resultFootprint
  observation := .legacy answer.observation
  adapter := answer.adapter.toGeneral
  resources := answer.resultAvailable
  live := answer.rawRelated.live henv hscoped formed
  support := answer.support
  typeFootprint := answer.typeFootprint
  typeCertificate := .ofCode answer.certificate answer.certificate.formed
  typeAvailable := answer.typeAvailable
  typed := answer.typed
  rawTyped := answer.rawTyped
  typeCode := answer.typeCode
  related := answer.related
  rawRelated := answer.rawRelated

def OriginalTail.StateHereditaryFundamental
    (env : VEnv) (registry : CanonicalHead.Registry)
    (context : ContextDerivation sourceEnv U source)
    (node : EndpointState sourceEnv U source expression assigned) : Prop :=
  ∀ (target : List VExpr) (locals : List Nat) (σ τ : Subst) (available : Valuation),
    available.AtomClosed → OnCtx target (env.IsType U) →
    Ctx.SubstEq env U target σ τ source →
    SortableTailPairedFits env registry target context locals σ τ available →
    SortableComputationalTransfer env U registry target locals σ τ available expression expression assigned

def OriginalTail.DerivationHereditaryFundamental
    (env : VEnv) (registry : CanonicalHead.Registry)
    (context : ContextDerivation sourceEnv U source)
    (original : Derivation sourceEnv U source left right assigned) : Prop :=
  ∀ (target : List VExpr) (locals : List Nat) (σ τ : Subst) (available : Valuation),
    available.AtomClosed → OnCtx target (env.IsType U) →
    Ctx.SubstEq env U target σ τ source →
    SortableTailPairedFits env registry target context locals σ τ available →
    SortableComputationalTransfer env U registry target locals σ τ available left right assigned ∧
      SortableComputationalTransfer env U registry target locals σ τ available right left assigned

theorem OriginalTail.StateHereditaryFundamental.sortable
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (fundamental : StateHereditaryFundamental env registry context node) :
    StateSortableFundamental env registry context node := by
  intro target locals σ τ available closed formed substitutions frame
  exact SortableComputationalTransfer.sortable henv hscoped closed formed
    (fundamental target locals σ τ available closed formed substitutions frame)

end Lean4Lean.AnchoredSource.Adapted
