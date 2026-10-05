import Lean4Lean.Theory.Typing.AnchoredOriginalWorldGradedApplication
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldIndependentFamilyConsumption

/-! Consume the literal caller operands produced by graded application.
The actual directional output adapter is composed with the same retained
family cursor; no second application-origin selection or output-path premise
is needed. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder EquationStratifiedFuel
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

private theorem FamilyEndDemand.raise_iff (bound : n ≤ N) (atom : Atom n) :
    FamilyEndDemand (raiseAtom N bound atom) ↔ FamilyEndDemand atom := by
  induction N with
  | zero =>
    have same : n = 0 := by omega
    subst n
    rfl
  | succ N ih =>
    by_cases same : n = N + 1
    · subst n; rw [raiseAtom_self]
    · have small : n ≤ N := by omega
      rw [raiseAtom_step small]
      exact ih small

/-- The actual reconstructed application supplies the requested caller
parameter observers, including dependent P demands. Parsing uses its literal
operands, while the exact normal adapter carries the final family request. -/
theorem RichApplicationOperandFactor.familyRequestsAlongPathOfBank
    {strata : EquationStratification env} {P : VEnv → Prop}
    {root : EndpointRef sourceEnv U source rootExpression rootType}
    {functionNode : EndpointState sourceEnv U source f (.forallE A B)}
    {argumentNode : EndpointState sourceEnv U source a A}
    {domain : EndpointState sourceEnv U source A (.sort u)}
    {body : EndpointState sourceEnv U (A :: source) B (.sort v)}
    {result : EndpointState sourceEnv U source (B.inst a) (.sort v)}
    {hu : u.WF U} {hv : v.WF U}
    {requested : Atom n} {demand : FamilyData (Profile k)}
    (factor : RichApplicationOperandFactor env registry target functionNode argumentNode
      locals σ available requested)
    (location : Located root (.app hu hv domain body functionNode argumentNode result))
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (context : ContextDerivation sourceEnv U source)
    (controls : OriginalWorldControls strata sourceEnv) (below : sourceEnv ≤ env)
    (frame : OriginalRichFrame sourceEnv env U registry target context locals σ σ available)
    (captured : WorldEnvironmentProvenance strata U (frame.dependencyEnvironment controls.ordered))
    (frontier : List (World strata.rules.length))
    (data : WorldUnaryFrameData P controls frontier frame captured)
    (closed : available.AtomClosed) (formed : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (callerPaid : Sponsored frontier [originalCallWorld controls .fundamental (.ref root) captured])
    (notDefinition : registry.definitions name = none) (notNative : registry.natives name = none)
    (head : f.getAppFnArgs.1 = .const name levels)
    (ready : factor.Controlled controls frontier)
    (path : GeneralOutputPath env U registry target requested (show Atom (k+1) from .family demand))
    (bank : WorldBoundedUnaryCallBank env U registry strata P
      (frontier ++ [originalCallWorld controls .fundamental (.ref root) captured])) :
    WorldFamilyRequestProperty controls frontier root registry target locals σ available
      name levels (VExpr.app f a).getAppFnArgs.2 demand := by
  have ends : FamilyEndDemand factor.output :=
    FamilyEndDemand.normalAdapterBack factor.outputAdapter
      ((FamilyEndDemand.raise_iff factor.bound requested).mpr
        (FamilyEndDemand.outputBack henv hscoped formed path trivial))
  let origin := factor.origin location
  obtain ⟨cursor⟩ := origin.consumeIndependentFamilyOfBank
    henv hscoped context controls below frame captured frontier data closed formed substitutions
    callerPaid notDefinition notNative head ends .refl factor.resources
    ready.function ready.argument bank
  let requested := cursor.adaptRequest henv hscoped formed factor.bound factor.outputAdapter
  exact (requested.outputPath henv hscoped formed path).familyRequests henv hscoped formed

/-- The direct family case uses the literal identity continuation. -/
theorem RichApplicationOperandFactor.familyRequestsOfBank
    {strata : EquationStratification env} {P : VEnv → Prop}
    {root : EndpointRef sourceEnv U source rootExpression rootType}
    {functionNode : EndpointState sourceEnv U source f (.forallE A B)}
    {argumentNode : EndpointState sourceEnv U source a A}
    {domain : EndpointState sourceEnv U source A (.sort u)}
    {body : EndpointState sourceEnv U (A :: source) B (.sort v)}
    {result : EndpointState sourceEnv U source (B.inst a) (.sort v)}
    {hu : u.WF U} {hv : v.WF U}
    {demand : FamilyData (Profile n)}
    (factor : RichApplicationOperandFactor env registry target functionNode argumentNode
      locals σ available (show Atom (n+1) from .family demand))
    (location : Located root (.app hu hv domain body functionNode argumentNode result))
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (context : ContextDerivation sourceEnv U source)
    (controls : OriginalWorldControls strata sourceEnv) (below : sourceEnv ≤ env)
    (frame : OriginalRichFrame sourceEnv env U registry target context locals σ σ available)
    (captured : WorldEnvironmentProvenance strata U (frame.dependencyEnvironment controls.ordered))
    (frontier : List (World strata.rules.length))
    (data : WorldUnaryFrameData P controls frontier frame captured)
    (closed : available.AtomClosed) (formed : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (callerPaid : Sponsored frontier [originalCallWorld controls .fundamental (.ref root) captured])
    (notDefinition : registry.definitions name = none) (notNative : registry.natives name = none)
    (head : f.getAppFnArgs.1 = .const name levels)
    (ready : factor.Controlled controls frontier)
    (bank : WorldBoundedUnaryCallBank env U registry strata P
      (frontier ++ [originalCallWorld controls .fundamental (.ref root) captured])) :
    WorldFamilyRequestProperty controls frontier root registry target locals σ available
      name levels (VExpr.app f a).getAppFnArgs.2 demand := by
  exact factor.familyRequestsAlongPathOfBank location henv hscoped context controls below
    frame captured frontier data closed formed substitutions callerPaid notDefinition notNative head
    ready .refl bank

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
