import Lean4Lean.Theory.Typing.AnchoredOriginalProjectionObserverReindex

/-! Actual source frames for whole-cut coherence. Binder descent uses the
query's domain certificate and guard, retaining the original earlier-tail
formation. The destination is the original argument frame retained by the
caller, restricted from the common realization by the cut depth. No context
reorigin or semantic answer is assumed. The certificates still use the
current grammar; this does not assert enlarged-syntax traversal coverage.
-/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalFactorCut
open VExpr VEnv AnchoredProfiles AnchoredSemantics
open OriginalClosureMeasure OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false

/-- A query is evaluated in the exact original formation spine at its
occurrence. The finite tail also retains all certificates needed by lookup. -/
structure OriginalQueryFrame
    (env : VEnv) (registry : CanonicalHead.Registry) (target : List VExpr)
    (context : ContextDerivation sourceEnv U source)
    (locals : List Nat) (σ : Subst) (available : Valuation) where
  tail : TailFits sourceEnv env U registry target source locals σ σ available
  original : tail.contextDerivation = context
  substitutions : Ctx.SubstEq env U target σ σ source

namespace OriginalQueryFrame

/-- Both copies retain the same actual source spine. -/
def paired (frame : OriginalQueryFrame env registry target context locals σ available) :
    TailPairedFits env registry target context locals σ σ available :=
  ⟨frame.tail, frame.tail, frame.original, frame.original⟩

/-- At a queried binder, the stored guard already supplies admission at the
actual anchor. No interpretation of a synthesized typing is requested. -/
def pushGuard
    {sourceEnv env : VEnv} {U : Nat} {source target : List VExpr}
    {registry : CanonicalHead.Registry} {locals : List Nat} {σ : Subst}
    {available : Valuation} {context : ContextDerivation sourceEnv U source}
    (frame : OriginalQueryFrame env registry target context locals σ available)
    (henv : env.Ordered) (below : sourceEnv ≤ env)
    (originalDomain : EndpointRef sourceEnv U source A (.sort level))
    {n : Nat} {key : Key n} {support packed : Profile n}
    {domainFootprint bodyFootprint outside : Footprint}
    (domain : CodeCert env U registry target locals σ A support domainFootprint)
    (resources : domainFootprint.Available available)
    (guard : LambdaGuard env U registry target σ A key support)
    (pack : BinderPack n packed bodyFootprint outside)
    (covered : ∀ atom ∈ packed.atoms, atom ∈ key.input.atoms) :
    OriginalQueryFrame env registry target (.cons context originalDomain) (Locals.push locals)
      (σ.cons key.anchor)
      (Valuation.push (bodyFootprint.localNeeds ++ bodyFootprint.localNeeds.flatMap Need.singletons) available) := by
  have arguments : Related env U registry target key.anchor key.anchor
      (A.subst σ) key.input support := by
    obtain ⟨_, _, _, _, _, _, _, anchor⟩ := guard.anchor
    exact Related.convert henv guard.inputTyped guard.domains anchor
  exact {
    tail := frame.tail.push originalDomain domain resources guard.inputTyped arguments
      (bodyFootprint.localNeeds ++ bodyFootprint.localNeeds.flatMap Need.singletons)
      (fun need member => (pack.atomized_localNeeds need member).1)
      (fun need member atom present => covered atom
        ((pack.atomized_localNeeds need member).2 atom present))
    original := congrArg (fun tail => ContextDerivation.cons tail originalDomain) frame.original
    substitutions := .cons frame.substitutions (originalDomain.sound.defeq.mono below)
      (guard.path.cast guard.anchor.1) }

/-- An identity display uses this very frame, without changing its original
context annotations. -/
def display
    {sourceEnv env : VEnv} {U : Nat} {source target : List VExpr}
    {registry : CanonicalHead.Registry} {locals : List Nat} {σ : Subst}
    {available : Valuation} {context : ContextDerivation sourceEnv U source}
    (frame : OriginalQueryFrame env registry target context locals σ available)
    (node : EndpointState sourceEnv U source expression assigned)
    (provenance : EndpointProvenance context node) :
    DisplayFits env registry target (.identity context node provenance) σ available locals := by
  refine { fits := ?_, original := ?_, substitutions := ?_ }
  · change TailFits sourceEnv env U registry target source locals
      (Subst.lift_l .refl σ) (Subst.lift_l .refl σ) (fun index => available (Lift.refl.liftVar index))
    simpa only [Subst.lift_l_refl, Lift.liftVar] using frame.tail
  · exact frame.original
  · simpa only [EndpointDisplay.identity, EndpointDisplay.sourceSubst, Subst.lift_l_refl]
      using frame.substitutions

end OriginalQueryFrame

/-- Descending a literal lambda retains the actual domain reference chosen
by this original location. The caller's body resources use the same atomized
head ledger supplied by BinderPack.available_atomized_localNeeds. -/
noncomputable def lambdaBodyFrame
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {domain : EndpointState sourceEnv U source A (.sort u)}
    {codomain : EndpointState sourceEnv U (A :: source) B (.sort v)}
    {body : EndpointState sourceEnv U (A :: source) expression B}
    {hu : u.WF U} {hv : v.WF U}
    (location : Located root (.lam hu hv domain codomain body))
    (initial : ContextDerivation sourceEnv U rootSource)
    (frame : OriginalQueryFrame env registry target (location.contextDerivation initial)
      locals σ available)
    (henv : env.Ordered) (below : sourceEnv ≤ env)
    {n : Nat} {key : Key n} {support packed : Profile n}
    (certificate : CodeCert env U registry target locals σ A support domainFootprint)
    (resources : domainFootprint.Available available)
    (guard : LambdaGuard env U registry target σ A key support)
    (pack : BinderPack n packed bodyFootprint outside)
    (covered : ∀ atom ∈ packed.atoms, atom ∈ key.input.atoms) :
    OriginalQueryFrame env registry target
      ((Located.lamBody location).contextDerivation initial) (Locals.push locals)
      (σ.cons key.anchor)
      (Valuation.push (bodyFootprint.localNeeds ++ bodyFootprint.localNeeds.flatMap Need.singletons) available) :=
  frame.pushGuard henv below (Classical.choose location.originalDomains.1)
    certificate resources guard pack covered

/-- Each Pi row creates its own frame at its stored anchor; no common anchor
or inhabited finite input is required. -/
noncomputable def piBodyFrame
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {domain : EndpointState sourceEnv U source A (.sort u)}
    {body : EndpointState sourceEnv U (A :: source) B (.sort v)}
    {hu : u.WF U} {hv : v.WF U}
    (location : Located root (.pi hu hv domain body))
    (initial : ContextDerivation sourceEnv U rootSource)
    (frame : OriginalQueryFrame env registry target (location.contextDerivation initial)
      locals σ available)
    (henv : env.Ordered) (below : sourceEnv ≤ env)
    {n : Nat} {key : Key n} {support packed : Profile n}
    (certificate : CodeCert env U registry target locals σ A support domainFootprint)
    (resources : domainFootprint.Available available)
    (guard : LambdaGuard env U registry target σ A key support)
    (pack : BinderPack n packed bodyFootprint outside)
    (covered : ∀ atom ∈ packed.atoms, atom ∈ key.input.atoms) :
    OriginalQueryFrame env registry target
      ((Located.piBody location).contextDerivation initial) (Locals.push locals)
      (σ.cons key.anchor)
      (Valuation.push (bodyFootprint.localNeeds ++ bodyFootprint.localNeeds.flatMap Need.singletons) available) :=
  frame.pushGuard henv below (Classical.choose location.originalDomains.1)
    certificate resources guard pack covered

/-- Invoke the fixed original comparison at a whole cut. Both source
spines are retained exactly, even if their formation references differ.
The argument frame is the caller's original frame, not a reannotated suffix
of the occurrence frame. -/
theorem CutOriginAt.coherenceAt
    {sourceEnv env : VEnv} {U : Nat}
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    (origin : CutOriginAt root boundary argument 0)
    {registry : CanonicalHead.Registry} {target : List VExpr}
    {locals baseLocals : List Nat} {fullRealization σ : Subst}
    {fullAvailable available : Valuation}
    (rootContext : ContextDerivation sourceEnv U rootSource)
    (argumentContext : ContextDerivation sourceEnv U (boundary ++ rootSource))
    (argumentNode : EndpointState sourceEnv U (boundary ++ rootSource) argument argumentType)
    (argumentProvenance : EndpointProvenance argumentContext argumentNode)
    (frame : OriginalQueryFrame env registry target
      (origin.location.contextDerivation rootContext) locals fullRealization fullAvailable)
    (argumentFrame : OriginalQueryFrame env registry target
      argumentContext baseLocals σ available)
    (realizationTail : Subst.lift_l (.skipN .refl origin.depth) fullRealization = σ)
    (availableTail : ∀ index, fullAvailable (index + origin.depth) = available index)
    (closed : fullAvailable.AtomClosed) (formed : OnCtx target (env.IsType U))
    (comparison : DisplayCoherence env U registry
      (origin.sourceDisplay rootContext)
      (origin.argumentDisplay argumentContext argumentNode argumentProvenance)) :
    DisplayCoherenceAnswer env registry target (origin.sourceDisplay rootContext)
      (origin.argumentDisplay argumentContext argumentNode argumentProvenance)
      fullRealization fullAvailable locals baseLocals := by
  let leftFrame : DisplayFits env registry target (origin.sourceDisplay rootContext)
      fullRealization fullAvailable locals :=
    frame.display origin.view (.ofLocation origin.location rootContext)
  have exactArgument : OriginalQueryFrame env registry target argumentContext baseLocals
      (Subst.lift_l (.skipN .refl origin.depth) fullRealization)
      (fun index => fullAvailable ((Lift.skipN .refl origin.depth).liftVar index)) := by
    simpa only [realizationTail, Lift.liftVar_skipN, Lift.liftVar, availableTail] using argumentFrame
  let rightFrame : DisplayFits env registry target
      (origin.argumentDisplay argumentContext argumentNode argumentProvenance)
      fullRealization fullAvailable baseLocals :=
    ⟨exactArgument.tail, exactArgument.original, exactArgument.substitutions⟩
  exact comparison target fullRealization fullAvailable locals baseLocals
    closed formed leftFrame rightFrame

/-- A projected argument cut now constructs its comparison answer using
only the fixed original C obligation and actual finite frames. Every field
certificate is then reindexed at its exact requested support. -/
theorem ProjectionObs.reindexAt
    {sourceEnv env : VEnv} {U : Nat}
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {origin : CutOriginAt root boundary (.proj name index major) 0}
    {registry : CanonicalHead.Registry} {target : List VExpr}
    {locals baseLocals : List Nat} {fullRealization σ : Subst}
    {fullAvailable available : Valuation}
    (query : ProjectionObs env registry target
      (origin.view.cast origin.expression_eq rfl) locals fullRealization demand footprint)
    (rootContext : ContextDerivation sourceEnv U rootSource)
    (argumentContext : ContextDerivation sourceEnv U (boundary ++ rootSource))
    (argument : EndpointState sourceEnv U (boundary ++ rootSource)
      (.proj name index major) argumentType)
    (argumentProvenance : EndpointProvenance argumentContext argument)
    (frame : OriginalQueryFrame env registry target
      (origin.location.contextDerivation rootContext) locals fullRealization fullAvailable)
    (argumentFrame : OriginalQueryFrame env registry target
      argumentContext baseLocals σ available)
    (realizationTail : Subst.lift_l (.skipN .refl origin.depth) fullRealization = σ)
    (availableTail : ∀ index, fullAvailable (index + origin.depth) = available index)
    (closed : fullAvailable.AtomClosed) (formed : OnCtx target (env.IsType U))
    (resources : footprint.Available fullAvailable)
    (comparison : DisplayCoherence env U registry
      (origin.sourceDisplay rootContext)
      (origin.argumentDisplay argumentContext argument argumentProvenance)) :
    ∃ nextFootprint, Nonempty (ProjectionObs env registry target argument
      baseLocals σ demand nextFootprint) ∧ nextFootprint.Available available :=
  query.reindexFromCoherence rootContext argumentContext argument argumentProvenance
    realizationTail availableTail resources
    (CutOriginAt.coherenceAt origin rootContext argumentContext argument argumentProvenance
      frame argumentFrame realizationTail availableTail closed formed comparison)

end Lean4Lean.AnchoredSource.Adapted.OriginalFactorCut
