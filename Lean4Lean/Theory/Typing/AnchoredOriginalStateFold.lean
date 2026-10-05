import Lean4Lean.Theory.Typing.AnchoredOriginalStateFundamental
import Lean4Lean.Theory.Typing.AnchoredOriginalDisplay

/-! Structural endpoint interpretation consumes only lower scheduled
original derivation calls. Endpoint states add no mutual recursive motive.
Projection observations currently contain only empty demands and their
wrappers; this leaf must change when source projection observations are added. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure OriginalTail
set_option backward.isDefEq.respectTransparency false

private theorem Obs.projectionEmpty
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (hTarget : OnCtx target (env.IsType U))
    (observation : Obs env U registry target locals σ (.proj name index major) demand footprint)
    (resources : footprint.Available available) :
    Nonempty (GradedTransferResult env U registry target locals σ τ available
      (.proj name index major) (.proj name index major) type demand) := by
  match observation with
  | .empty => exact ⟨.empty⟩
  | .union left right =>
    obtain ⟨a⟩ := left.projectionEmpty henv hscoped hTarget
      (fun i need member => resources i need (List.mem_append_left _ member))
    obtain ⟨b⟩ := right.projectionEmpty henv hscoped hTarget
      (fun i need member => resources i need (List.mem_append_right _ member))
    exact ⟨a.union henv hscoped hTarget b⟩
  | .view child change =>
    obtain ⟨result⟩ := child.projectionEmpty henv hscoped hTarget resources
    exact ⟨result.view henv hscoped hTarget change⟩
  | .pad child =>
    obtain ⟨result⟩ := child.projectionEmpty henv hscoped hTarget resources
    exact ⟨result.pad henv hscoped hTarget⟩
  | .unpad child =>
    obtain ⟨result⟩ := child.projectionEmpty henv hscoped hTarget resources
    exact ⟨result.unpad⟩
  | .rowShift child =>
    obtain ⟨result⟩ := child.projectionEmpty henv hscoped hTarget resources
    exact ⟨(result.pad henv hscoped hTarget).view henv hscoped hTarget (.commutePadFn _ _)⟩
termination_by sizeOf observation

/-- This current-grammar leaf makes no claim about the separate typed
projection observation pilot. Such observations are not constructors of Obs. -/
theorem OriginalTail.StateFundamental.projection
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (context : ContextDerivation sourceEnv U source)
    (node : EndpointState sourceEnv U source (.proj name index major) type) :
    StateFundamental env registry context node := by
  intro target locals σ τ available _closed hTarget _substitutions _frame
  have transfer : GradedTransfer env U registry target locals σ τ available
      (.proj name index major) (.proj name index major) type := by
    intro n demand footprint observation resources
    exact observation.projectionEmpty henv hscoped hTarget resources
  exact ⟨transfer, transfer.sortCorrect henv hTarget⟩

/-- The ordinary lower-cost F hypothesis of the combined original F/C
recursion, with the actual source context closure in its measure. -/
def OriginalTail.FundamentalBelow (sourceEnv env : VEnv) (U : Nat)
    (registry : CanonicalHead.Registry) (bound : Nat) : Prop :=
  ∀ {source left right type} (context : ContextDerivation sourceEnv U source)
    (original : Derivation sourceEnv U source left right type),
    schedule .fundamental (Closure.close original.origin context.closures).cost < bound →
    DerivationFundamental env registry context original

/-- A finite structural fold, not another global recursive theorem. Every
reference is answered by the supplied strictly lower original F hypothesis;
all structural children remain under the caller's same scheduled bound. -/
theorem OriginalTail.StateFundamental.ofBelow
    (henv : env.Ordered) (hscoped : registry.Scoped) (hle : sourceEnv ≤ env)
    (earlier : FundamentalBelow sourceEnv env U registry bound)
    (node : EndpointState sourceEnv U source expression type)
    (context : ContextDerivation sourceEnv U source)
    (domains : node.OriginalDomains)
    (smaller : schedule .fundamental (Closure.close node.origin context.closures).cost < bound) :
    StateFundamental env registry context node := by
  induction node with
  | ref reference =>
    cases reference with
    | left original => exact (earlier context original smaller).left henv hscoped
    | right original => exact (earlier context original smaller).right henv hscoped
  | sort levelWF => exact StateFundamental.sort henv hscoped context levelWF
  | bvar lookup levelWF formation ih =>
    exact StateFundamental.bvar henv hscoped context lookup levelWF formation
      (ih context domains (Nat.lt_trans (state_bvar_schedule context lookup levelWF formation) smaller))
  | app hu hv domain codomain function argument result ihDomain ihCodomain ihFunction ihArgument ihResult =>
    obtain ⟨domainRef, equal⟩ := domains.1
    subst domain
    have bounds := state_app_schedule context hu hv domainRef codomain function argument result
    exact StateFundamental.app henv hscoped hle context hu hv domainRef codomain function argument result
      (ihDomain context trivial (Nat.lt_trans bounds.1 smaller))
      (ihCodomain (.cons context domainRef) domains.2.2.1 (Nat.lt_trans bounds.2.1 smaller))
      (ihFunction context domains.2.2.2.1 (Nat.lt_trans bounds.2.2.1 smaller))
      (ihArgument context domains.2.2.2.2.1 (Nat.lt_trans bounds.2.2.2.1 smaller))
      (ihResult context domains.2.2.2.2.2 (Nat.lt_trans bounds.2.2.2.2 smaller))
  | lam hu hv domain codomain body ihDomain ihCodomain ihBody =>
    obtain ⟨domainRef, equal⟩ := domains.1
    subst domain
    have bounds := state_lam_schedule context hu hv domainRef codomain body
    exact StateFundamental.lam henv hscoped hle context hu hv domainRef codomain body
      (ihDomain context trivial (Nat.lt_trans bounds.1 smaller))
      (ihCodomain (.cons context domainRef) domains.2.2.1 (Nat.lt_trans bounds.2.1 smaller))
      (ihBody (.cons context domainRef) domains.2.2.2 (Nat.lt_trans bounds.2.2 smaller))
  | pi hu hv domain body ihDomain ihBody =>
    obtain ⟨domainRef, equal⟩ := domains.1
    subst domain
    have bounds := state_pi_schedule context hu hv domainRef body
    exact StateFundamental.pi henv hscoped hle context hu hv domainRef body
      (ihDomain context trivial (Nat.lt_trans bounds.1 smaller))
      (ihBody (.cons context domainRef) domains.2.2 (Nat.lt_trans bounds.2 smaller))
  | proj registered levelsWF levelCount parameterCount indexCount selected fieldWF field major closed relevance _ih =>
    exact StateFundamental.projection henv hscoped context
      (.proj registered levelsWF levelCount parameterCount indexCount selected fieldWF field major closed relevance)
  | convert plan term ih =>
    have bounds := state_convert_schedule context plan term
    apply StateFundamental.convert henv hscoped hle context plan term
    · intro source left right type original call
      exact earlier (call.contextDerivation context) original (Nat.lt_trans (bounds.2 call) smaller)
    · exact ih context domains (Nat.lt_trans bounds.1 smaller)

/-- A retained original location supplies the hereditary domain-reference
invariant itself; callers provide no provenance or typing reconstruction. -/
theorem OriginalTail.StateFundamental.locatedOfBelow
    (henv : env.Ordered) (hscoped : registry.Scoped) (hle : sourceEnv ≤ env)
    (earlier : FundamentalBelow sourceEnv env U registry bound)
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {node : EndpointState sourceEnv U source expression type}
    (location : OriginalEndpointFactor.Located root node)
    (initial : ContextDerivation sourceEnv U rootSource)
    (smaller : schedule .fundamental
      (Closure.close node.origin (location.environment initial.closures)).cost < bound) :
    StateFundamental env registry (location.contextDerivation initial) node := by
  apply StateFundamental.ofBelow henv hscoped hle earlier node _ location.originalDomains
  simpa only [OriginalEndpointFactor.Located.contextDerivation_closures] using smaller

/-- Display weakening does not alter the retained source closure. -/
theorem OriginalEndpointFactor.EndpointDisplay.fundamentalOfBelow
    {displayed : List VExpr}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hle : sourceEnv ≤ env)
    (earlier : FundamentalBelow sourceEnv env U registry bound)
    (display : OriginalEndpointFactor.EndpointDisplay sourceEnv U displayed expression type)
    (smaller : schedule .fundamental display.cost < bound) :
    StateFundamental env registry display.context display.node := by
  rw [display.provenance.context_eq]
  apply StateFundamental.locatedOfBelow henv hscoped hle earlier display.provenance.location display.provenance.initial
  rw [← OriginalEndpointFactor.Located.contextDerivation_closures, ← display.provenance.context_eq]
  exact smaller

end Lean4Lean.AnchoredSource.Adapted
