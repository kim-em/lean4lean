import Lean4Lean.Theory.Typing.AnchoredOriginalProjectionAdapter
import Lean4Lean.Theory.Typing.AnchoredOriginalSeededSpine

/-! Backward requests through an actual constructor spine retain projected
argument seeds. Legacy parameters and projected fields have distinct finite
original-child call lists; neither branch calls an arbitrary Strong supplier.
The forward declaration-row alignment is a separate pass over these frames. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalEndpointFactor
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure OriginalTail
open OriginalFactorCut
open private transportSeedAdapter from Lean4Lean.Theory.Typing.AnchoredOriginalProjectionAdapter
set_option backward.isDefEq.respectTransparency false

inductive ProjectionSpineSeeds
    (env : VEnv) (registry : CanonicalHead.Registry) (target : List VExpr)
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    (locals : List Nat) (σ : Subst) (available : Valuation) :
    {source : List VExpr} → {expression assigned : VExpr} →
    {node : EndpointState sourceEnv U source expression assigned} → {start : Located root node} →
    OriginalConstantSpine root name levels start → Type where
  | constant {node : EndpointState sourceEnv U source (.const name levels) assigned}
      {start : Located root node} {packet : ConstantPrefix node} :
      ProjectionSpineSeeds env registry target locals σ available (.constant (start := start) packet)
  | legacy
      {node : EndpointState sourceEnv U source (.app f a) assigned}
      {start : Located root node} {packet : ApplicationPrefix start}
      {function : OriginalConstantSpine root name levels (.appFunction packet.view.location)}
      (functionSeeds : ProjectionSpineSeeds env registry target locals σ available function)
      (argument : NativeArgumentSeed env U registry target locals σ available a) :
      ProjectionSpineSeeds env registry target locals σ available
        (.application (f := f) (a := a) packet function)
  | projected
      {node : EndpointState sourceEnv U source (.app f (.proj fieldName index major)) assigned}
      {start : Located root node} {packet : ApplicationPrefix start}
      {function : OriginalConstantSpine root name levels (.appFunction packet.view.location)}
      (functionSeeds : ProjectionSpineSeeds env registry target locals σ available function)
      (argument : ProjectedApplicationSeed (env := env) registry target locals σ available packet.view key) :
      ProjectionSpineSeeds env registry target locals σ available (.application packet function)

def ProjectionSpineSeeds.Fundamentals
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {node : EndpointState sourceEnv U source expression assigned} {start : Located root node}
    {spine : OriginalConstantSpine root name levels start}
    (seeds : ProjectionSpineSeeds env registry target locals σ available spine)
    (initial : ContextDerivation sourceEnv U rootSource) : Prop :=
  match seeds with
  | .constant (start := start) (packet := packet) =>
      ConstantPrefixCall.Fundamentals env registry packet (start.contextDerivation initial)
  | .legacy (packet := packet) function argument =>
      PrefixCall.Fundamentals env registry packet.route (start.contextDerivation initial) ∧
      StateFundamental env registry
        ((Located.appArgument packet.view.location).contextDerivation initial) packet.view.argument ∧
      function.Fundamentals initial
  | .projected (packet := packet) function argument =>
      PrefixCall.Fundamentals env registry packet.route (start.contextDerivation initial) ∧
      PrefixCall.Fundamentals env registry (projectionHead packet.view.argument).route
        ((Located.appArgument packet.view.location).contextDerivation initial) ∧
      StateFundamental env registry
        ((Located.appArgument packet.view.location).contextDerivation initial)
        (projectionHead packet.view.argument).field ∧
      DerivationFundamental env registry
        ((Located.appArgument packet.view.location).contextDerivation initial)
        (projectionHead packet.view.argument).major ∧
      function.Fundamentals initial

inductive OriginalProjectionSpine (sourceEnv env : VEnv) (U : Nat)
    (registry : CanonicalHead.Registry) (source target : List VExpr)
    (locals : List Nat) (σ : Subst) (available : Valuation) (name : Name) (levels : List VLevel) :
    (expression assigned : VExpr) → {n : Nat} → Profile n → Footprint → Type where
  | constant
      (replay : ConstantReplayResult sourceEnv env U registry target locals σ available
        name levels assigned profile) :
      OriginalProjectionSpine sourceEnv env U registry source target locals σ available name levels
        (.const name levels) assigned profile footprint
  | legacy
      (frame : SeededApplicationCodeInput env U registry target locals σ available A B a result before)
      (function : OriginalProjectionSpine sourceEnv env U registry source target locals σ available name levels
        f (.forallE A B) frame.profile frame.footprint) :
      OriginalProjectionSpine sourceEnv env U registry source target locals σ available name levels
        (.app f a) (B.inst a) result before
  | projected
      {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
      {node : EndpointState sourceEnv U source (.app f (.proj fieldName index major)) assigned}
      {start : Located root node} (view : AppView start)
      (result : ProjectionApplicationResult (env := env) registry target locals σ available view key profile)
      (certificate : CodeCert env U registry target locals σ
        (view.codomainExpression.inst (.proj fieldName index major)) profile before)
      (function : OriginalProjectionSpine sourceEnv env U registry source target locals σ available name levels
        f (.forallE view.domainExpression view.codomainExpression) result.frame.profile
        (result.frame.domainFootprint ++ result.frame.outside)) :
      OriginalProjectionSpine sourceEnv env U registry source target locals σ available name levels
        (.app f (.proj fieldName index major))
        (view.codomainExpression.inst (.proj fieldName index major)) profile before
  | conversion
      (plan : EndpointConversion sourceEnv U source A B)
      (certificate : CodeCert env U registry target locals σ B profile footprint)
      (transfer : CodeTransferResult env U registry target locals σ σ available B A profile)
      (term : OriginalProjectionSpine sourceEnv env U registry source target locals σ available name levels
        expression A profile transfer.footprint) :
      OriginalProjectionSpine sourceEnv env U registry source target locals σ available name levels
        expression B profile footprint

private theorem PrefixRoute.projectionSpine
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (below : sourceEnv ≤ env)
    {source target : List VExpr} {locals : List Nat} {σ : Subst} {available : Valuation}
    (initial : ContextDerivation sourceEnv U source)
    (closed : available.AtomClosed) (formed : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (fits : TailFits sourceEnv env U registry target source locals σ σ available)
    {first : EndpointState sourceEnv U source expression assigned}
    {last : EndpointState sourceEnv U source expression natural}
    (route : PrefixRoute sourceEnv U source expression first last)
    (calls : PrefixCall.Fundamentals env registry route initial)
    {name : Name} {levels : List VLevel} {profile : Profile n}
    (finish : ∀ {footprint}, CodeCert env U registry target locals σ natural profile footprint →
      footprint.Available available → Nonempty
        (OriginalProjectionSpine sourceEnv env U registry source target locals σ available
          name levels expression natural profile footprint))
    {footprint : Footprint}
    (certificate : CodeCert env U registry target locals σ assigned profile footprint)
    (resources : footprint.Available available) :
    Nonempty (OriginalProjectionSpine sourceEnv env U registry source target locals σ available
      name levels expression assigned profile footprint) := by
  induction route generalizing footprint with
  | done => exact finish certificate resources
  | expose reference rest ih => exact ih (fun call => calls (.expose call)) finish certificate resources
  | convert plan term rest ih =>
    obtain ⟨level, backward, _⟩ := conversionTailTransfers henv hscoped below plan initial
      (fun call => calls (.conversion call)) closed formed substitutions
      (TailPairedFits.diagonal initial fits)
    obtain ⟨changed⟩ := certificate.transfer_graded henv hscoped formed closed backward resources
    obtain ⟨spine⟩ := ih (fun call => calls (.tail call)) finish changed.certificate changed.available
    exact ⟨.conversion plan certificate changed spine⟩

/-- The complete backward producer includes every typed projected seed and
its incoming adapter; the result stores each constructed frame for the
subsequent original-header row walk. -/
theorem ProjectionSpineSeeds.prepare
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {rootSource source target : List VExpr} {rootExpression rootType expression assigned : VExpr}
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {node : EndpointState sourceEnv U source expression assigned} {start : Located root node}
    {name : Name} {levels : List VLevel}
    {spine : OriginalConstantSpine root name levels start}
    (seeds : ProjectionSpineSeeds env registry target locals σ available spine)
    (henv : env.Ordered) (hscoped : registry.Scoped) (below : sourceEnv ≤ env)
    (initial : ContextDerivation sourceEnv U rootSource)
    (calls : seeds.Fundamentals initial)
    (closed : available.AtomClosed) (formed : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (fits : TailFits sourceEnv env U registry target source locals σ σ available)
    {profile : Profile n} {footprint : Footprint}
    (certificate : CodeCert env U registry target locals σ assigned profile footprint)
    (resources : footprint.Available available) :
    Nonempty (OriginalProjectionSpine sourceEnv env U registry source target locals σ available
      name levels expression assigned profile footprint) := by
  induction seeds generalizing n footprint with
  | @constant source name levels assigned node start packet =>
    obtain ⟨replay⟩ := packet.replayOriginal henv hscoped below (start.contextDerivation initial)
      closed formed substitutions fits calls certificate resources
    exact ⟨.constant replay⟩
  | @legacy source f a assigned name levels node start packet function functionSeeds argument ih =>
    apply packet.route.projectionSpine henv hscoped below (start.contextDerivation initial)
      closed formed substitutions fits calls.1 ?_ certificate resources
    intro footprint current present
    obtain ⟨request, _⟩ := CodeCert.prepareOriginalApplication packet.view argument current present
    have child := calls.2.1 target locals σ σ available closed formed substitutions
      (TailPairedFits.diagonal ((Located.appArgument packet.view.location).contextDerivation initial) fits)
    obtain ⟨answer⟩ := child.1 request.observation request.resources
    let frame := request.complete henv below formed substitutions answer
    obtain ⟨previous⟩ := ih calls.2.2 substitutions fits frame.certificate frame.resources
    exact ⟨.legacy frame previous⟩
  | @projected source f fieldName index major assigned name levels k key node start packet function functionSeeds argument ih =>
    apply packet.route.projectionSpine henv hscoped below (start.contextDerivation initial)
      closed formed substitutions fits calls.1 ?_ certificate resources
    intro footprint current present
    obtain ⟨request, seedEq⟩ := CodeCert.prepareProjectionApplication packet.view argument current present
    obtain ⟨frame, frameSeed, _, _, _⟩ := request.complete henv hscoped below
      ((Located.appArgument packet.view.location).contextDerivation initial)
      calls.2.1 calls.2.2.1 calls.2.2.2.1 closed formed substitutions
      (TailPairedFits.diagonal ((Located.appArgument packet.view.location).contextDerivation initial) fits)
    have exactSeed : frame.seed = argument.seed := frameSeed.trans (congrArg (fun x => x.seed) seedEq)
    have grade : frame.seed.rank = k := (congrArg (fun x => x.rank) exactSeed).trans argument.grade
    have seedAdapter : NormalProfileAdapter env U registry target frame.seed.demand
        (grade.symm ▸ key.input) := by
      exact transportSeedAdapter exactSeed grade argument.grade argument.adapter
    have resultAdapter := frame.seedAdapter henv hscoped formed seedAdapter
    have keyBound : k ≤ frame.collected.rank :=
      grade ▸ Nat.le_trans (Nat.le_max_right _ _) frame.collected.bound
    have adapter : NormalProfileAdapter env U registry target frame.input
        (raiseProfile frame.collected.rank keyBound key.input) := by
      cases grade
      exact resultAdapter
    let result : ProjectionApplicationResult (env := env) registry target locals σ available
        packet.view key profile := ⟨frame, keyBound, adapter⟩
    obtain ⟨previous⟩ := ih calls.2.2.2.2 substitutions fits frame.certificate frame.resources
    exact ⟨.projected packet.view result current previous⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalEndpointFactor
