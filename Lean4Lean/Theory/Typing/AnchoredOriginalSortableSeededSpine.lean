import Lean4Lean.Theory.Typing.AnchoredSortableSeededSpine
import Lean4Lean.Theory.Typing.AnchoredOriginalSortableConstantReplay
import Lean4Lean.Theory.Typing.AnchoredOriginalSeededSpine

/-! Rich backward family requests retain actual original spine locations,
finite conversion ledgers, and the complete merged source argument seeds. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalEndpointFactor
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure OriginalTail
open OriginalFactorCut
set_option backward.isDefEq.respectTransparency false

noncomputable def SortableSpineSeeds.originalSpine
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {node : EndpointState sourceEnv U source expression assigned}
    (seeds : SortableSpineSeeds env U registry target locals σ available expression)
    (start : Located root node)
    (head : expression.getAppFnArgs.1 = .const name levels) :
    OriginalConstantSpine root name levels start := by
  induction seeds generalizing assigned with
  | constant =>
    simp only [getAppFnArgs_const] at head
    cases head
    exact .constant (constantPrefix node)
  | app function argument ih =>
    let packet := applicationPrefix start
    exact .application packet (ih (.appFunction packet.view.location)
      (by simpa only [getAppFnArgs_app] using head))

/-- A finite family of callbacks at the spine's actual original children.
Each context is computed from the retained location or conversion ledger. -/
def OriginalConstantSpine.HereditaryFundamentals
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {node : EndpointState sourceEnv U source expression assigned}
    {start : Located root node}
    (spine : OriginalConstantSpine root name levels start)
    (env : VEnv) (registry : CanonicalHead.Registry)
    (initial : ContextDerivation sourceEnv U rootSource) : Prop :=
  match spine with
  | .constant packet =>
      ConstantPrefixCall.HereditaryFundamentals env registry packet (start.contextDerivation initial)
  | .application packet function =>
      PrefixCall.HereditaryFundamentals env registry packet.route (start.contextDerivation initial) ∧
      StateHereditaryFundamental env registry
        ((Located.appArgument packet.view.location).contextDerivation initial) packet.view.argument ∧
      function.HereditaryFundamentals env registry initial

theorem OriginalConstantSpine.hereditaryFundamentalsOfCalls
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {node : EndpointState sourceEnv U source expression assigned} {start : Located root node}
    (spine : OriginalConstantSpine root name levels start)
    (initial : ContextDerivation sourceEnv U rootSource)
    (equalities : ∀ {context left right type} {original : Derivation sourceEnv U context left right type}
      (call : spine.EqualityCall original),
      DerivationHereditaryFundamental env registry (call.contextDerivation initial) original)
    (arguments : ∀ {context argument type} {original : EndpointState sourceEnv U context argument type}
      (call : spine.ArgumentCall original),
      StateHereditaryFundamental env registry (call.location.contextDerivation initial) original) :
    spine.HereditaryFundamentals env registry initial := by
  revert equalities arguments
  induction spine with
  | constant packet =>
    intro equalities _
    exact fun call => equalities (.constant call)
  | application packet function ih =>
    intro equalities arguments
    exact ⟨fun call => equalities (.conversion call), arguments .here,
      ih (fun call => equalities (.function call)) (fun call => arguments (.function call))⟩

/-- The backward result keeps actual application frames and code changes.
Unlike the legacy tree, its constant and conversion nodes contain no
unrestricted OriginalPayload or SourcePiFormation semantics. -/
inductive OriginalSortableSeededSpine (sourceEnv env : VEnv) (U : Nat)
    (registry : CanonicalHead.Registry) (source target : List VExpr)
    (locals : List Nat) (σ : Subst) (available : Valuation) (name : Name) (levels : List VLevel) :
    (expression assigned : VExpr) → {n : Nat} → Profile n → Footprint → Type where
  | constant
      (replay : SortableConstantReplayResult sourceEnv env U registry target locals σ available
        name levels assigned true profile) :
      OriginalSortableSeededSpine sourceEnv env U registry source target locals σ available name levels
        (.const name levels) assigned profile footprint
  | application
      (frame : SortableSeededApplicationInput env U registry target locals σ available A B a result before)
      (function : OriginalSortableSeededSpine sourceEnv env U registry source target locals σ available name levels
        f (.forallE A B) frame.profile frame.footprint) :
      OriginalSortableSeededSpine sourceEnv env U registry source target locals σ available name levels
        (.app f a) (B.inst a) result before
  | conversion
      (plan : EndpointConversion sourceEnv U source A B)
      (certificate : SortableCert env U registry target locals σ B true profile footprint)
      (transfer : SortableTransferResult env U registry target locals σ σ available B A true profile)
      (term : OriginalSortableSeededSpine sourceEnv env U registry source target locals σ available name levels
        expression A profile transfer.footprint) :
      OriginalSortableSeededSpine sourceEnv env U registry source target locals σ available name levels
        expression B profile footprint

def OriginalSortableSeededSpine.seeds
    (spine : OriginalSortableSeededSpine sourceEnv env U registry source target locals σ available name levels
      expression assigned profile footprint) :
    SortableSpineSeeds env U registry target locals σ available expression :=
  match spine with
  | .constant .. => .constant
  | .application frame function => .app function.seeds frame.seed
  | .conversion _ _ _ term => term.seeds

private theorem PrefixRoute.seededSortableOriginal
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (below : sourceEnv ≤ env)
    {source target : List VExpr} {locals : List Nat} {σ : Subst} {available : Valuation}
    (initial : ContextDerivation sourceEnv U source)
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (fits : SortableTailFits sourceEnv env U registry target source locals σ σ available)
    {first : EndpointState sourceEnv U source expression assigned}
    {last : EndpointState sourceEnv U source expression natural}
    (route : PrefixRoute sourceEnv U source expression first last)
    (calls : PrefixCall.HereditaryFundamentals env registry route initial)
    {name : Name} {levels : List VLevel} {profile : Profile n}
    (seeds : SortableSpineSeeds env U registry target locals σ available expression)
    (finish : ∀ {footprint}, SortableCert env U registry target locals σ natural true profile footprint →
      footprint.Available available →
      ∃ spine : OriginalSortableSeededSpine sourceEnv env U registry source target locals σ available
        name levels expression natural profile footprint, spine.seeds = seeds)
    {footprint : Footprint}
    (certificate : SortableCert env U registry target locals σ assigned true profile footprint)
    (resources : footprint.Available available) :
    ∃ spine : OriginalSortableSeededSpine sourceEnv env U registry source target locals σ available
      name levels expression assigned profile footprint, spine.seeds = seeds := by
  induction route generalizing footprint with
  | done => exact finish certificate resources
  | expose reference rest ih => exact ih (fun call => calls (.expose call)) finish certificate resources
  | convert plan term rest ih =>
    obtain ⟨level, backward, _⟩ := conversionSortableTailTransfers henv hscoped below plan initial
      (fun call => calls (.conversion call)) closed hTarget substitutions
      (SortableTailPairedFits.diagonal initial fits)
    obtain ⟨changed⟩ := SortableComputationalTransfer.sortable henv hscoped closed hTarget backward certificate resources
    obtain ⟨spine, same⟩ := ih (fun call => calls (.tail call)) finish changed.certificate changed.available
    exact ⟨.conversion plan certificate changed.toSortableTransferResult spine, same⟩

/-- One complete backward producer over the computed original spine.
The argument is queried once, after its original seed and all result-type
cuts have been merged. Conversion callbacks keep their exact source tails. -/
theorem OriginalConstantSpine.prepareSortable
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {rootSource source target : List VExpr} {rootExpression rootType expression assigned : VExpr}
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {node : EndpointState sourceEnv U source expression assigned} {start : Located root node}
    {name : Name} {levels : List VLevel}
    (spine : OriginalConstantSpine root name levels start)
    (henv : env.Ordered) (hscoped : registry.Scoped) (below : sourceEnv ≤ env)
    (initial : ContextDerivation sourceEnv U rootSource)
    (calls : spine.HereditaryFundamentals env registry initial)
    {locals : List Nat} {σ : Subst} {available : Valuation}
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (fits : SortableTailFits sourceEnv env U registry target source locals σ σ available)
    (seeds : SortableSpineSeeds env U registry target locals σ available expression)
    {profile : Profile n} {footprint : Footprint}
    (certificate : SortableCert env U registry target locals σ assigned true profile footprint)
    (resources : footprint.Available available) :
    ∃ result : OriginalSortableSeededSpine sourceEnv env U registry source target locals σ available
      name levels expression assigned profile footprint, result.seeds = seeds := by
  induction spine generalizing n footprint with
  | @constant _ _ current packet =>
    cases seeds
    obtain ⟨replay⟩ := packet.replaySortableOriginal henv hscoped below (current.contextDerivation initial)
      closed hTarget substitutions fits calls certificate resources
    exact ⟨.constant replay, rfl⟩
  | @application f a assigned node start packet function ih =>
    cases seeds with
    | app functionSeeds argumentSeed =>
      apply packet.route.seededSortableOriginal henv hscoped below (start.contextDerivation initial)
        closed hTarget substitutions fits calls.1 (.app functionSeeds argumentSeed) ?_ certificate resources
      intro footprint current present
      obtain ⟨frame, seedEq⟩ := SortableCert.prepareSeededApplication packet.view initial henv below
        closed hTarget substitutions
        (SortableTailPairedFits.diagonal (packet.view.location.contextDerivation initial) fits)
        calls.2.1 argumentSeed current present
      obtain ⟨previous, same⟩ := ih calls.2.2 functionSeeds frame.certificate frame.resources
      exact ⟨.application frame previous, by
        simp only [OriginalSortableSeededSpine.seeds, same]
        exact congrArg (SortableSpineSeeds.app functionSeeds) seedEq⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalEndpointFactor
