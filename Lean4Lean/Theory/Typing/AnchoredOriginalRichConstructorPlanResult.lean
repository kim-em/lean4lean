import Lean4Lean.Theory.Typing.AnchoredOriginalRichCodeAction
import Lean4Lean.Theory.Typing.AnchoredFamilyCaptureInterpretation
import Lean4Lean.Theory.Typing.AnchoredOriginalProjectionSortableSyntax

/-! Native constructor plans rebuild their type support at the actual original
header endpoint. Declared domains may contain rich projected queries; neither
the binder plan nor its source type certificate erases those children. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
open private checks AtomWF FamilyWF ConstructorWF RecordWF RequestWF KeyWF AtomTyped from Lean4Lean.Theory.Typing.AnchoredProfiles
set_option backward.isDefEq.respectTransparency false

variable {header : EndpointRef headerEnv U [] declaredType (.sort headerLevel)}

structure RichConstructorPlanResult
    (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry) (target : List VExpr)
    {headerEnv : VEnv} {declaredType : VExpr} {headerLevel : VLevel}
    (header : EndpointRef headerEnv U [] declaredType (.sort headerLevel))
    (name : Name) (levels : List VLevel) (signature : ConstantTelescope declaredType)
    {source : List VExpr} (context : ContextDerivation headerEnv U source)
    {expression assigned : VExpr} (node : EndpointState headerEnv U source expression assigned)
    (σ : Subst) (arguments : List VExpr) (available : Valuation) (atom : Atom n) where
  footprint : Footprint
  plan : RichConstructorPlan env U registry target header name levels signature context σ arguments (.singleton atom) footprint
  resources : footprint.Available available
  support : Profile n
  typeFootprint : Footprint
  certificate : RichCert headerEnv env U registry target node (List.range arguments.length) σ true support typeFootprint
  typeResources : typeFootprint.Available available
  typed : (Profile.singleton atom).HasType support

noncomputable def RichConstructorPlan.raise {n : Nat} {profile : Profile n}
    (plan : RichConstructorPlan env U registry target header name levels signature context σ arguments profile footprint)
    {N : Nat} (bound : n ≤ N) :
    RichConstructorPlan env U registry target header name levels signature context σ arguments
      (raiseProfile N bound (profile : Profile n)) footprint := by
  induction N with
  | zero => have same : n = 0 := by omega
            subst n; exact plan
  | succ N ih =>
    by_cases same : n = N + 1
    · subst n; simpa only [raiseProfile_self] using plan
    · have previous : n ≤ N := by omega
      simpa only [raiseProfile_step previous] using RichConstructorPlan.pad (ih previous)

noncomputable def RichConstructorPlanResult.raise {n : Nat} {atom : Atom n}
    (result : RichConstructorPlanResult env U registry target header name levels signature context node σ arguments available atom)
    {N : Nat} (bound : n ≤ N) :
    RichConstructorPlanResult env U registry target header name levels signature context node σ arguments available
      (raiseAtom N bound (atom : Atom n)) where
  footprint := result.footprint
  plan := by simpa only [raiseProfile_singleton] using result.plan.raise bound
  resources := result.resources
  support := raiseProfile N bound result.support
  typeFootprint := result.typeFootprint
  certificate := result.certificate.raise bound
  typeResources := result.typeResources
  typed := by simpa only [raiseProfile_singleton] using Profile.HasType.raise bound result.typed

/-- The terminal packet retains the actual original result formation, not
just a legacy certificate for its displayed expression. -/
noncomputable def RichConstructorPlanResult.terminal {n : Nat}
    {keys : List (DataRequest (Profile n))} {captureFootprint resultFootprint : Footprint}
    {context : ContextDerivation headerEnv U source}
    {family : FamilyData (Profile n)}
    {node : EndpointState headerEnv U source signature.result (.sort resultLevel)}
    (saturated : arguments.length = signature.domains.length)
    (resultShape : signature.result = mkApps (.const family.name familyLevels) familyArguments)
    (relevant : family.relevant = true)
    (location : Located header node) (lineage : location.contextDerivation .nil = context)
    (captures : FamilyCaptures env U registry target source (List.range arguments.length) σ
      (constantCaptureVariables arguments.length) keys captureFootprint)
    (resultCode : RichCert headerEnv env U registry target node (List.range arguments.length) σ true
      (Profile.singleton (n := n + 1) (.family family)) resultFootprint)
    (captureResources : captureFootprint.Available available)
    (resultResources : resultFootprint.Available available) :
    RichConstructorPlanResult env U registry target header name levels signature context node σ arguments available
      (n := n + 1) (.ctor ⟨name, levels, keys, family, relevant⟩) where
  footprint := captureFootprint ++ resultFootprint
  plan := .terminal saturated resultShape relevant node location lineage captures resultCode
  resources := fun i need member => (List.mem_append.mp member).elim
    (captureResources i need) (resultResources i need)
  support := .singleton (.family family)
  typeFootprint := resultFootprint
  certificate := resultCode
  typeResources := resultResources
  typed := by
    have familyWF := resultCode.formed.wf_value
    refine ⟨?_, familyWF, ?_⟩
    · intro atom member
      cases List.mem_singleton.mp member
      exact ⟨familyWF _ (List.mem_singleton_self _), captures.inputsWF⟩
    · intro atom member
      cases List.mem_singleton.mp member
      exact ⟨_, List.mem_singleton_self _, rfl⟩

/-- A record terminal retains the selected original fields and their raw
projection guards; no global nonzero family-level premise is added. -/
noncomputable def RichConstructorPlanResult.terminalRecord {n : Nat}
    {demand : RecordData (Profile n)} {projection : VProjectionInfo}
    {captureFootprint resultFootprint : Footprint}
    {context : ContextDerivation headerEnv U source}
    {node : EndpointState headerEnv U source signature.result (.sort resultLevel)}
    (registered : env.projections demand.family.name projection)
    (lookup : registry.projections demand.family.name = some projection)
    (constructorName : projection.ctorName = name)
    (bounded : ∀ entry ∈ demand.fields, entry.1 < projection.numFields)
    (saturated : arguments.length = signature.domains.length)
    (resultShape : signature.result = mkApps (.const demand.family.name familyLevels) familyArguments)
    (location : Located header node) (lineage : location.contextDerivation .nil = context)
    (captures : FamilyCaptures env U registry target source (List.range arguments.length) σ
      (demand.fields.map fun entry => .bvar (arguments.length - 1 - (projection.nparams + entry.1)))
      (demand.fields.map (·.2)) captureFootprint)
    (resultCode : RichCert headerEnv env U registry target node (List.range arguments.length) σ true
      (Profile.singleton (n := n + 1) (.family demand.family)) resultFootprint)
    (origins : ∀ entry ∈ demand.fields,
      Nonempty (RankedData.ProjectionOrigin env U target projection demand.family.name entry.1
        (mkApps (.const name levels) ((constantCaptureVariables arguments.length).map (·.subst σ)))
        (signature.result.subst σ) entry.2.domain))
    (captureResources : captureFootprint.Available available)
    (resultResources : resultFootprint.Available available) :
    RichConstructorPlanResult env U registry target header name levels signature context node σ arguments available
      (n := n + 1) (.record demand) where
  footprint := captureFootprint ++ resultFootprint
  plan := .terminalRecord registered lookup constructorName bounded saturated resultShape
    node location lineage captures resultCode origins
  resources := fun i need member => (List.mem_append.mp member).elim
    (captureResources i need) (resultResources i need)
  support := .singleton (.family demand.family)
  typeFootprint := resultFootprint
  certificate := resultCode
  typeResources := resultResources
  typed := by
    have familyWF := resultCode.formed.wf_value
    refine ⟨?_, familyWF, ?_⟩
    · intro atom member
      cases List.mem_singleton.mp member
      exact ⟨familyWF _ (List.mem_singleton_self _),
        fun entry member => captures.inputsWF _ (List.mem_map_of_mem member)⟩
    · intro atom member
      cases List.mem_singleton.mp member
      exact ⟨_, List.mem_singleton_self _, rfl⟩

noncomputable def RichConstructorPlanResult.view
    (result : RichConstructorPlanResult env U registry target header name levels signature context node σ arguments available atom)
    (view : AtomView env U registry target atom next) :
    RichConstructorPlanResult env U registry target header name levels signature context node σ arguments available next where
  footprint := result.footprint
  plan := .view result.plan view
  resources := result.resources
  support := view.mapType result.support
  typeFootprint := result.typeFootprint
  certificate := .map view result.certificate
  typeResources := result.typeResources
  typed := view.mapType_typed result.typed

/-- Close both finite footprints at one original declared binder. The rich
projected-domain certificate is stored literally in both resulting trees. -/
theorem RichConstructorPlanResult.binder
    {context : ContextDerivation headerEnv U source}
    {domain : EndpointRef headerEnv U source A (.sort u)}
    {body : EndpointState headerEnv U (A :: source) B (.sort v)}
    (hu : u.WF U) (hv : v.WF U)
    (domainAt : signature.domains[arguments.length]? = some A)
    (location : Located header (.ref domain)) (lineage : location.contextDerivation .nil = context)
    (domainCode : RichCert headerEnv env U registry target (.ref domain) (List.range arguments.length)
      σ true (domainSupport : Profile n) domainFootprint)
    (domainAvailable : domainFootprint.Available available)
    (guard : LambdaGuard env U registry target σ A key domainSupport)
    (needs : List Need) (bounded : ∀ need ∈ needs, need.rank ≤ n)
    (covered : ∀ need ∈ needs, ∀ atom ∈ (need.atGrade n).atoms, atom ∈ key.input.atoms)
    (child : RichConstructorPlanResult env U registry target header name levels signature (.cons context domain)
      body (σ.cons key.anchor) (arguments ++ [key.anchor]) (available.push needs) (output : Atom n)) :
    Nonempty (RichConstructorPlanResult env U registry target header name levels signature context
      (.pi hu hv (.ref domain) body) σ arguments available (n := n + 1) (.fn key output)) := by
  obtain ⟨packed, outside, pack, coverage, outsideAvailable⟩ :=
    Footprint.pack_available child.resources bounded covered
  obtain ⟨typePacked, typeOutside, typePack, typeCoverage, typeOutsideAvailable⟩ :=
    Footprint.pack_available child.typeResources bounded covered
  have bodyCode : RichCert headerEnv env U registry target body (Locals.push (List.range arguments.length))
      (σ.cons key.anchor) true child.support child.typeFootprint := by
    simpa only [List.length_append, List.length_singleton, List.range_succ_eq_map, Locals.push] using child.certificate
  exact ⟨{
    footprint := domainFootprint ++ outside
    plan := .binder domainAt domain location lineage domainCode guard child.plan pack coverage
    resources := fun i need member => (List.mem_append.mp member).elim
      (domainAvailable i need) (outsideAvailable i need)
    support := .pi (A.subst σ) (B.subst σ.lift) domainSupport [(key, child.support)]
    typeFootprint := domainFootprint ++ typeOutside
    certificate := by
      simpa only [List.append_nil] using
        RichCert.pi hu hv domainCode PiGuard.literal (RichRows.cons guard bodyCode typePack typeCoverage .nil)
    typeResources := fun i need member => (List.mem_append.mp member).elim
      (domainAvailable i need) (typeOutsideAvailable i need)
    typed := by
      apply Profile.HasType.fn _ (List.mem_singleton_self _) child.typed
      refine Profile.WF.pi_iff.mpr ⟨domainCode.formed, ?_⟩
      intro k r member
      cases List.mem_singleton.mp member
      exact ⟨guard.inputTyped, child.typed.wf_type⟩ }⟩

/-- Conversion/reference exposure changes only the retained header code
occurrence. It does not replace the original domain children in the plan. -/
def RichConstructorPlanResult.restoreRoute
    (route : PrefixRoute headerEnv U source expression first last)
    (result : RichConstructorPlanResult env U registry target header name levels signature context last σ arguments available atom) :
    RichConstructorPlanResult env U registry target header name levels signature context first σ arguments available atom :=
  { result with certificate := .route route result.certificate }

/-- Closing the empty original header context yields a real rich constant
observation. Both closed child footprints are computed from availability. -/
theorem RichConstructorPlanResult.bareObservation
    (origin : ConstantHeaderOrigin sourceEnv name info)
    (levelsWF : ∀ level ∈ levels, level.WF U)
    (result : RichConstructorPlanResult env U registry target (origin.familyHeader levelsWF).reference name levels signature
      .nil (.ref (origin.familyHeader levelsWF).reference) realization [] (fun _ => []) atom)
    (lookup : env.constants name = some info)
    (notDefinition : registry.definitions name = none)
    (notNative : registry.natives name = none) (notQuotient : name ≠ ``Quot.lift)
    (levelCount : levels.length = info.uvars) (typeClosed : info.type.Closed)
    {node : EndpointState sourceEnv U source (.const name levels) assigned} :
    Nonempty (RichObs sourceEnv env U registry target node locals σ (.singleton atom) []) := by
  have footprintEmpty : result.footprint = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    rintro ⟨index, need⟩ member
    exact nomatch result.resources index need member
  have typeEmpty : result.typeFootprint = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    rintro ⟨index, need⟩ member
    exact nomatch result.typeResources index need member
  have equivalent : ∀ levels : List VLevel, List.Forall₂ (· ≈ ·) levels levels := by
    intro levels
    induction levels with
    | nil => exact .nil
    | cons level levels ih => exact .cons rfl ih
  exact ⟨.constructor origin lookup notDefinition notNative notQuotient levelsWF levelCount levelsWF (equivalent levels)
    signature typeClosed (by simpa only [List.length_nil, List.range_zero, typeEmpty] using result.certificate)
    result.typed (by simpa only [footprintEmpty] using result.plan)⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
