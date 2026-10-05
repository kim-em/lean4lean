import Lean4Lean.Theory.Typing.AnchoredOriginalRichFamilySeedConsumption
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldQueryOperations
import Lean4Lean.Theory.Typing.AnchoredOriginalCanonicalConstSharedReturn

/-! A native family below a canonical constant keeps its own original
header. The existing consumption cursor already separates that header from
the caller root, so its actual plan can consume caller arguments directly.
No caller-source header origin or replacement telescope is manufactured. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics InductiveSignature
open OriginalClosureMeasure OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1200000

/-- The source seed stays at its actual original constant. Only the empty
source-argument spine is initialized at the independent caller root. -/
noncomputable def RetainedRichFamilySeed.atCaller
    {sourceRoot : EndpointRef sourceEnv U source sourceExpression sourceType}
    (seed : RetainedRichFamilySeed sourceRoot env registry target name levels)
    (callerRoot : EndpointRef callerEnv U callerSource callerExpression callerType)
    (locals : List Nat) (σ : Subst) (available : Valuation) :
    RichFamilyPlanConsumption callerRoot (seed.origin.familyHeader seed.seedWF).reference
      env registry target locals σ available name seed.seed seed.signature [] seed.atom :=
  .bare seed.plan

theorem RetainedRichFamilySeed.atCaller_queries
    {sourceRoot : EndpointRef sourceEnv U source sourceExpression sourceType}
    (seed : RetainedRichFamilySeed sourceRoot env registry target name levels)
    (callerRoot : EndpointRef callerEnv U callerSource callerExpression callerType)
    (locals : List Nat) (σ : Subst) (available : Valuation)
    (property : RichFamilyQueryPredicate callerEnv env U registry target callerSource locals σ) :
    (seed.atCaller callerRoot locals σ available).observed.Queries property :=
  trivial

private theorem outputPath_queries
    {root : EndpointRef sourceEnv U source rootExpression rootType}
    {header : EndpointRef headerEnv U [] declaredType (.sort headerLevel)}
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (result : RichFamilyPlanConsumption root header env registry target locals σ available
      name levels signature arguments a)
    (path : GeneralOutputPath env U registry target a b)
    (property : RichFamilyQueryPredicate sourceEnv env U registry target source locals σ)
    (ready : result.observed.Queries property) :
    (result.outputPath henv hscoped formed path).observed.Queries property := by
  induction path with
  | refl => exact ready
  | action path action ih => exact ih
  | code path action sorted ih => exact ih
  | pad path ih => exact ih
  | unpad path ih => exact ih

namespace CanonicalFamilyConsumption

section Native
variable
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {target : List VExpr}
    {strata : EquationStratification env} {name : Name} {levels : List VLevel}
    (outer : CanonicalConstOrigin env U registry strata name levels)
    {info : VConstant} {seedLevels : List VLevel}
    (origin : ConstantHeaderOrigin outer.owner.selected.origin.source name info)
    (lookup : env.constants name = some info)
    (notDefinition : registry.definitions name = none)
    (notNative : registry.natives name = none) (notQuotient : name ≠ ``Quot.lift)
    (seedWF : ∀ level ∈ seedLevels, level.WF U)
    (seedLength : seedLevels.length = info.uvars)
    (levelsWF : ∀ level ∈ levels, level.WF U)
    (equivalent : List.Forall₂ (· ≈ ·) seedLevels levels)
    (signature : ConstantTelescope (info.type.instL seedLevels))
    (typeClosed : info.type.Closed)
    {n : Nat} {atom : Atom n} {support : Profile n}
    {typeRealization planRealization : Subst}
    (certificate : RichCert origin.source env U registry target
      (.ref (origin.familyHeader seedWF).reference) [] typeRealization true support [])
    (typed : (Profile.singleton atom).HasType support)
    (plan : RichFamilyPlan env U registry target (origin.familyHeader seedWF).reference
      name seedLevels signature .nil planRealization [] (.singleton atom) [])

/-- Exact native-child extraction for `.canonicalConst`. Its source root
is the stored canonical site, not the caller's independent constant proof. -/
noncomputable def nativeFamilySeed :
    RetainedRichFamilySeed outer.site env registry target name levels :=
  .ofNative .here origin lookup notDefinition notNative notQuotient seedWF seedLength
    levelsWF equivalent signature typeClosed certificate typed plan

/-- The observation reconstructed from this seed is literally the native
child retained by the canonical constant carrier. -/
theorem nativeFamilySeed_observation (realization : Subst) :
    (nativeFamilySeed outer origin lookup notDefinition notNative notQuotient seedWF
      seedLength levelsWF equivalent signature typeClosed certificate typed plan).observation
      (locals := []) (σ := realization) =
    (RichObs.family (node := .ref outer.site) origin lookup notDefinition notNative notQuotient
      seedWF seedLength levelsWF equivalent signature typeClosed certificate typed plan) := rfl

end Native

/-- Consume the real caller argument against the native plan retained below
the canonical constant. All source slots belong to the caller; all header
nodes remain in the exact canonical seed's header source. This is the
application leaf needed after a constant/body compiler, without asking for a
physical function origin in the caller source. -/
theorem consumeNativeFamilyApplication
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {target : List VExpr}
    {strata : EquationStratification env} {name : Name} {levels : List VLevel}
    (outer : CanonicalConstOrigin env U registry strata name levels)
    {n : Nat} {key : Key n} {output : Atom n}
    (seed : RetainedRichFamilySeed outer.site env registry target name levels)
    (path : GeneralOutputPath env U registry target seed.atom (show Atom (n+1) from .fn key output))
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (formed : OnCtx target (env.IsType U))
    {callerRoot : EndpointRef callerEnv U callerSource callerExpression callerType}
    {argument : EndpointState callerEnv U callerSource a A}
    {rawInput : Profile n}
    (location : Located callerRoot argument)
    (observation : RichObs callerEnv env U registry target argument locals σ (rawInput : Profile n) footprint)
    (resources : footprint.Available available)
    (live : Profile.Live env U registry target rawInput)
    (arguments : GeneralNormalProfileAdapter env U registry target rawInput key.input)
    (admitted : Admitted env U registry target key (a.subst σ) (a.subst σ))
    (controls : OriginalWorldControls strata controlSource)
    (frontier : List (EquationWorldClosureOrder.World strata.rules.length))
    (ready : ControlledStoredQuery controls frontier (.observation observation)) :
    ∃ result : RichFamilyPlanConsumption callerRoot (seed.origin.familyHeader seed.seedWF).reference
        env registry target locals σ available name seed.seed seed.signature [a] output,
      result.observed.Queries (fun query =>
        Nonempty (ControlledStoredQuery controls frontier (.observation query))) := by
  let initial := seed.atCaller callerRoot locals σ available
  let start := initial.outputPath henv hscoped formed path
  exact start.appPreserving henv hscoped
    (seed.origin.sourceBelow.trans outer.owner.selected.origin.sourceBelow) formed location observation
    resources live arguments admitted
    (fun _ bound controlled => controlled.elim (fun value => value.raise bound))
    (outputPath_queries henv hscoped formed initial path _
      (seed.atCaller_queries callerRoot locals σ available _)) ⟨ready⟩

end CanonicalFamilyConsumption
end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
