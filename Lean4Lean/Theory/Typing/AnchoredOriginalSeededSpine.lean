import Lean4Lean.Theory.Typing.AnchoredOriginalApplicationPrefix
import Lean4Lean.Theory.Typing.AnchoredOriginalTailConstant

/-! Backward family requests follow the actual original function spine.
Only finite conversion ledgers and the actual argument endpoints are used;
there is no supplier for arbitrary Strong proofs or declaration-domain
typing of an argument. Declaration-row replay is a separate forward pass.
-/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalEndpointFactor
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure OriginalTail
open OriginalFactorCut
set_option backward.isDefEq.respectTransparency false

/-- Query-independent original application and constant locations. -/
inductive OriginalConstantSpine
    (root : EndpointRef sourceEnv U rootSource rootExpression rootType)
    (name : Name) (levels : List VLevel) :
    {source : List VExpr} → {expression assigned : VExpr} →
    {node : EndpointState sourceEnv U source expression assigned} → Located root node → Type where
  | constant {node : EndpointState sourceEnv U source (.const name levels) assigned}
      {start : Located root node} (packet : ConstantPrefix node) :
      OriginalConstantSpine root name levels start
  | application {node : EndpointState sourceEnv U source (.app f a) assigned}
      {start : Located root node} (packet : ApplicationPrefix start)
      (function : OriginalConstantSpine root name levels (.appFunction packet.view.location)) :
      OriginalConstantSpine root name levels start

noncomputable def NativeSpineSeeds.originalSpine
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {node : EndpointState sourceEnv U source expression assigned}
    (seeds : NativeSpineSeeds env U registry target locals σ available expression)
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
def OriginalConstantSpine.Fundamentals
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {node : EndpointState sourceEnv U source expression assigned}
    {start : Located root node}
    (spine : OriginalConstantSpine root name levels start)
    (env : VEnv) (registry : CanonicalHead.Registry)
    (initial : ContextDerivation sourceEnv U rootSource) : Prop :=
  match spine with
  | .constant packet =>
      ConstantPrefixCall.Fundamentals env registry packet (start.contextDerivation initial)
  | .application packet function =>
      PrefixCall.Fundamentals env registry packet.route (start.contextDerivation initial) ∧
      StateFundamental env registry
        ((Located.appArgument packet.view.location).contextDerivation initial) packet.view.argument ∧
      function.Fundamentals env registry initial

inductive OriginalConstantSpine.EqualityCall
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {name : Name} {levels : List VLevel} :
    {source : List VExpr} → {expression assigned : VExpr} →
    {node : EndpointState sourceEnv U source expression assigned} → {start : Located root node} →
    OriginalConstantSpine root name levels start →
    {context : List VExpr} → {left right type : VExpr} →
    Derivation sourceEnv U context left right type → Type where
  | constant {node : EndpointState sourceEnv U source (.const name levels) assigned}
      {start : Located root node} {packet : ConstantPrefix node}
      (call : ConstantPrefixCall packet original) : EqualityCall (.constant (start := start) packet) original
  | conversion {node : EndpointState sourceEnv U source (.app f a) assigned}
      {start : Located root node} {packet : ApplicationPrefix start}
      {function : OriginalConstantSpine root name levels (.appFunction packet.view.location)}
      (call : PrefixCall packet.route original) :
      EqualityCall (.application packet function) original
  | function {node : EndpointState sourceEnv U source (.app f a) assigned}
      {start : Located root node} {packet : ApplicationPrefix start}
      {function : OriginalConstantSpine root name levels (.appFunction packet.view.location)}
      (call : EqualityCall function original) :
      EqualityCall (.application packet function) original

noncomputable def OriginalConstantSpine.EqualityCall.contextDerivation
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {node : EndpointState sourceEnv U source expression assigned} {start : Located root node}
    {spine : OriginalConstantSpine root name levels start}
    {original : Derivation sourceEnv U context left right type}
    (call : OriginalConstantSpine.EqualityCall spine original)
    (initial : ContextDerivation sourceEnv U rootSource) :
    ContextDerivation sourceEnv U context :=
  match call with
  | .constant (packet := _) (start := start) call =>
      call.contextDerivation (start.contextDerivation initial)
  | .conversion (packet := _) (start := start) call =>
      call.contextDerivation (start.contextDerivation initial)
  | .function call => call.contextDerivation initial

theorem OriginalConstantSpine.EqualityCall.cost_lt
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {node : EndpointState sourceEnv U source expression assigned} {start : Located root node}
    {spine : OriginalConstantSpine root name levels start}
    {original : Derivation sourceEnv U context left right type}
    (call : OriginalConstantSpine.EqualityCall spine original)
    (initial : ContextDerivation sourceEnv U rootSource) :
    (Closure.close original.origin (call.contextDerivation initial).closures).cost <
      (Closure.close root.origin initial.closures).cost := by
  match call with
  | .constant (start := start) call =>
    change (Closure.close _
      (call.contextDerivation (start.contextDerivation initial)).closures).cost < _
    rw [ConstantPrefixCall.contextDerivation_closures, Located.contextDerivation_closures]
    exact call.cost_lt_root start initial.closures
  | .conversion (start := start) call =>
    change (Closure.close _
      (call.contextDerivation (start.contextDerivation initial)).closures).cost < _
    rw [PrefixCall.contextDerivation_closures, Located.contextDerivation_closures]
    exact Nat.lt_of_lt_of_le (call.cost_lt (start.environment initial.closures))
      (start.cost_le initial.closures)
  | .function call => exact call.cost_lt initial
termination_by sizeOf call

inductive OriginalConstantSpine.ArgumentCall
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {name : Name} {levels : List VLevel} :
    {source : List VExpr} → {expression assigned : VExpr} →
    {node : EndpointState sourceEnv U source expression assigned} → {start : Located root node} →
    OriginalConstantSpine root name levels start →
    {context : List VExpr} → {argument type : VExpr} →
    EndpointState sourceEnv U context argument type → Type where
  | here {node : EndpointState sourceEnv U source (.app f a) assigned}
      {start : Located root node} {packet : ApplicationPrefix start}
      {function : OriginalConstantSpine root name levels (.appFunction packet.view.location)} :
      ArgumentCall (.application packet function) packet.view.argument
  | function {node : EndpointState sourceEnv U source (.app f a) assigned}
      {start : Located root node} {packet : ApplicationPrefix start}
      {function : OriginalConstantSpine root name levels (.appFunction packet.view.location)}
      (call : ArgumentCall function argument) :
      ArgumentCall (.application packet function) argument

def OriginalConstantSpine.ArgumentCall.location
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {node : EndpointState sourceEnv U source expression assigned} {start : Located root node}
    {spine : OriginalConstantSpine root name levels start}
    {argument : EndpointState sourceEnv U context argumentExpression type}
    (call : OriginalConstantSpine.ArgumentCall spine argument) : Located root argument :=
  match call with
  | .here (packet := packet) => .appArgument packet.view.location
  | .function call => call.location

theorem OriginalConstantSpine.ArgumentCall.cost_lt
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {node : EndpointState sourceEnv U source expression assigned} {start : Located root node}
    {spine : OriginalConstantSpine root name levels start}
    {argument : EndpointState sourceEnv U context argumentExpression type}
    (call : OriginalConstantSpine.ArgumentCall spine argument)
    (initial : ContextDerivation sourceEnv U rootSource) :
    (Closure.close argument.origin (call.location.contextDerivation initial).closures).cost <
      (Closure.close root.origin initial.closures).cost := by
  induction call with
  | @here _ _ _ _ start packet function =>
    rw [Located.contextDerivation_closures]
    have smaller := binder_other_cost (domain := packet.view.domain.origin)
      (bodies := [packet.view.codomain.origin])
      (children := [packet.view.function.origin, packet.view.argument.origin, packet.view.result.origin])
      (child := packet.view.argument.origin) (by simp)
      (packet.view.location.environment initial.closures)
    exact Nat.lt_of_lt_of_le smaller
      (Nat.le_trans (packet.view.cost_le initial.closures) (start.cost_le initial.closures))
  | function call ih => exact ih

theorem OriginalConstantSpine.fundamentalsOfCalls
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {node : EndpointState sourceEnv U source expression assigned} {start : Located root node}
    (spine : OriginalConstantSpine root name levels start)
    (initial : ContextDerivation sourceEnv U rootSource)
    (equalities : ∀ {context left right type} {original : Derivation sourceEnv U context left right type}
      (call : spine.EqualityCall original),
      DerivationFundamental env registry (call.contextDerivation initial) original)
    (arguments : ∀ {context argument type} {original : EndpointState sourceEnv U context argument type}
      (call : spine.ArgumentCall original),
      StateFundamental env registry (call.location.contextDerivation initial) original) :
    spine.Fundamentals env registry initial := by
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
inductive OriginalSeededSpine (sourceEnv env : VEnv) (U : Nat)
    (registry : CanonicalHead.Registry) (source target : List VExpr)
    (locals : List Nat) (σ : Subst) (available : Valuation) (name : Name) (levels : List VLevel) :
    (expression assigned : VExpr) → {n : Nat} → Profile n → Footprint → Type where
  | constant
      (replay : ConstantReplayResult sourceEnv env U registry target locals σ available
        name levels assigned profile) :
      OriginalSeededSpine sourceEnv env U registry source target locals σ available name levels
        (.const name levels) assigned profile footprint
  | application
      (frame : SeededApplicationCodeInput env U registry target locals σ available A B a result before)
      (function : OriginalSeededSpine sourceEnv env U registry source target locals σ available name levels
        f (.forallE A B) frame.profile frame.footprint) :
      OriginalSeededSpine sourceEnv env U registry source target locals σ available name levels
        (.app f a) (B.inst a) result before
  | conversion
      (plan : EndpointConversion sourceEnv U source A B)
      (certificate : CodeCert env U registry target locals σ B profile footprint)
      (transfer : CodeTransferResult env U registry target locals σ σ available B A profile)
      (term : OriginalSeededSpine sourceEnv env U registry source target locals σ available name levels
        expression A profile transfer.footprint) :
      OriginalSeededSpine sourceEnv env U registry source target locals σ available name levels
        expression B profile footprint

def OriginalSeededSpine.seeds
    (spine : OriginalSeededSpine sourceEnv env U registry source target locals σ available name levels
      expression assigned profile footprint) :
    NativeSpineSeeds env U registry target locals σ available expression :=
  match spine with
  | .constant .. => .constant
  | .application frame function => .app function.seeds frame.seed
  | .conversion _ _ _ term => term.seeds

private theorem PrefixRoute.seededOriginal
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (below : sourceEnv ≤ env)
    {source target : List VExpr} {locals : List Nat} {σ : Subst} {available : Valuation}
    (initial : ContextDerivation sourceEnv U source)
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (fits : TailFits sourceEnv env U registry target source locals σ σ available)
    {first : EndpointState sourceEnv U source expression assigned}
    {last : EndpointState sourceEnv U source expression natural}
    (route : PrefixRoute sourceEnv U source expression first last)
    (calls : PrefixCall.Fundamentals env registry route initial)
    {name : Name} {levels : List VLevel} {profile : Profile n}
    (seeds : NativeSpineSeeds env U registry target locals σ available expression)
    (finish : ∀ {footprint}, CodeCert env U registry target locals σ natural profile footprint →
      footprint.Available available →
      ∃ spine : OriginalSeededSpine sourceEnv env U registry source target locals σ available
        name levels expression natural profile footprint, spine.seeds = seeds)
    {footprint : Footprint}
    (certificate : CodeCert env U registry target locals σ assigned profile footprint)
    (resources : footprint.Available available) :
    ∃ spine : OriginalSeededSpine sourceEnv env U registry source target locals σ available
      name levels expression assigned profile footprint, spine.seeds = seeds := by
  induction route generalizing footprint with
  | done => exact finish certificate resources
  | expose reference rest ih => exact ih (fun call => calls (.expose call)) finish certificate resources
  | convert plan term rest ih =>
    obtain ⟨level, backward, _⟩ := conversionTailTransfers henv hscoped below plan initial
      (fun call => calls (.conversion call)) closed hTarget substitutions
      (TailPairedFits.diagonal initial fits)
    obtain ⟨changed⟩ := certificate.transfer_graded henv hscoped hTarget closed backward resources
    obtain ⟨spine, same⟩ := ih (fun call => calls (.tail call)) finish changed.certificate changed.available
    exact ⟨.conversion plan certificate changed spine, same⟩

/-- One complete backward producer over the computed original spine.
The argument is queried once, after its original seed and all result-type
cuts have been merged. Conversion callbacks keep their exact source tails. -/
theorem OriginalConstantSpine.prepare
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {rootSource source target : List VExpr} {rootExpression rootType expression assigned : VExpr}
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {node : EndpointState sourceEnv U source expression assigned} {start : Located root node}
    {name : Name} {levels : List VLevel}
    (spine : OriginalConstantSpine root name levels start)
    (henv : env.Ordered) (hscoped : registry.Scoped) (below : sourceEnv ≤ env)
    (initial : ContextDerivation sourceEnv U rootSource)
    (calls : spine.Fundamentals env registry initial)
    {locals : List Nat} {σ : Subst} {available : Valuation}
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (fits : TailFits sourceEnv env U registry target source locals σ σ available)
    (seeds : NativeSpineSeeds env U registry target locals σ available expression)
    {profile : Profile n} {footprint : Footprint}
    (certificate : CodeCert env U registry target locals σ assigned profile footprint)
    (resources : footprint.Available available) :
    ∃ result : OriginalSeededSpine sourceEnv env U registry source target locals σ available
      name levels expression assigned profile footprint, result.seeds = seeds := by
  induction spine generalizing n footprint with
  | @constant _ _ current packet =>
    cases seeds
    obtain ⟨replay⟩ := packet.replayOriginal henv hscoped below (current.contextDerivation initial)
      closed hTarget substitutions fits calls certificate resources
    exact ⟨.constant replay, rfl⟩
  | @application f a assigned node start packet function ih =>
    cases seeds with
    | app functionSeeds argumentSeed =>
      apply packet.route.seededOriginal henv hscoped below (start.contextDerivation initial)
        closed hTarget substitutions fits calls.1 (.app functionSeeds argumentSeed) ?_ certificate resources
      intro footprint current present
      obtain ⟨request, seedEq⟩ := CodeCert.prepareOriginalApplication packet.view argumentSeed current present
      have child := calls.2.1 target locals σ σ available closed hTarget substitutions
        (TailPairedFits.diagonal ((Located.appArgument packet.view.location).contextDerivation initial) fits)
      obtain ⟨answer⟩ := child.1 request.observation request.resources
      let frame := request.complete henv below hTarget substitutions answer
      obtain ⟨previous, same⟩ := ih calls.2.2 functionSeeds frame.certificate frame.resources
      exact ⟨.application frame previous, by
        simp only [OriginalSeededSpine.seeds, same]
        exact congrArg (NativeSpineSeeds.app functionSeeds) seedEq⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalEndpointFactor
