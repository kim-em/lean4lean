import Lean4Lean.Theory.Typing.AnchoredOriginalCanonicalConstOrigin
import Lean4Lean.Theory.Typing.EquationHeaderDerivation
import Lean4Lean.Theory.Typing.AnchoredOriginalCanonicalCodeOwner
import Lean4Lean.Theory.Typing.AnchoredCodeAction
import Lean4Lean.Theory.Typing.AnchoredOriginalSourceCaptureSyntax
import Lean4Lean.Theory.Typing.AnchoredSortableCert
import Lean4Lean.Theory.Typing.AnchoredOriginalProjectionQuery
import Lean4Lean.Theory.Typing.AnchoredOriginalDefinitionEndpoint
import Lean4Lean.Theory.Typing.AnchoredOriginalFamilyExtraction
import Lean4Lean.Theory.Typing.AnchoredRigidFamilySpine
import Lean4Lean.Theory.Typing.AnchoredSortableAppOrigin

/-! Shared endpoint-indexed hereditary queries and charged type recipes.
Typed projections retain their actual field and major originals. Canonical
code roots retain their original child and named charge through finite Pi
elimination; dependent bodies expose actual binder needs. Interpretation and
hereditary bounds are separate proof obligations. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalFactorCut
set_option backward.isDefEq.respectTransparency false

/-- A finite replacement for each requested local resource. Every entry
retains its actual variable observation and contributes exactly its footprint;
this is syntax, not a resource-supply function stored in a query. -/
inductive RecipeResourceTransfer (env : VEnv) (U : Nat)
    (registry : CanonicalHead.Registry) (target : List VExpr)
    (locals : List Nat) (σ : Subst) : Footprint → Footprint → Type where
  | nil : RecipeResourceTransfer env U registry target locals σ [] []
  | cons {need : Need}
      (observation : Obs env U registry target locals σ (.bvar index) need.profile queryFootprint)
      (tail : RecipeResourceTransfer env U registry target locals σ needs footprint) :
      RecipeResourceTransfer env U registry target locals σ ((index, need) :: needs)
        (queryFootprint ++ footprint)

private theorem richCodeAction_formed
    (action : SortableCodeAction env U registry target relevant profile nextRelevant nextProfile)
    (formed : profile.HasType (.sort relevant)) : nextProfile.HasType (.sort nextRelevant) := by
  induction action with
  | id => exact formed
  | retag targetFormed => exact targetFormed
  | comp first second ihfirst ihsecond => exact ihsecond (ihfirst formed)
  | union first second ihfirst ihsecond => exact (ihfirst formed).union (ihsecond formed)
  | support change => exact change.preservesSort formed
  | pad => exact formed.pad_sort
  | down => simpa only [Profile.down_sort] using formed.down
  | unpad => simpa only [Profile.down_sort] using formed.pad_inv
  | sortPad => exact formed.sortPad
  | familyPad => exact formed.familyPad
  | map change => exact change.mapType_sort formed
  | select member => exact formed.singleton_of_mem member
  | focusMinimal minimal bound => exact formed.restrict bound minimal.formation.wf_value

mutual
inductive RichCert : (sourceEnv env : VEnv) → (U : Nat) → (registry : CanonicalHead.Registry) →
    (target : List VExpr) →
    {source : List VExpr} → {expression assigned : VExpr} →
    EndpointState sourceEnv U source expression assigned →
    List Nat → Subst → Bool → {n : Nat} → Profile n → Footprint → Type where
  | legacy {node : EndpointState sourceEnv U source expression assigned}
      (certificate : SortableCert env U registry target locals σ expression relevant profile footprint) :
      RichCert sourceEnv env U registry target node locals σ relevant profile footprint
  /-- The actual caller formation retains a finite charged type recipe.
  Opening its canonical child is a separate recursive call; taking a Pi
  component never exposes that child as an uncharged certificate. -/
  | recipe {node : EndpointState sourceEnv U source expression assigned}
      (code : RichCodeRecipe env U registry target source locals σ expression relevant profile footprint) :
      RichCert sourceEnv env U registry target node locals σ relevant profile footprint
  | observe {node : EndpointState sourceEnv U source expression assigned}
      (observation : RichObs sourceEnv env U registry target node locals σ profile footprint)
      (formed : profile.HasType (.sort relevant)) :
      RichCert sourceEnv env U registry target node locals σ relevant profile footprint
  | pi {domain : EndpointState sourceEnv U source A (.sort u)}
      {body : EndpointState sourceEnv U (A :: source) B (.sort v)}
      (hu : u.WF U) (hv : v.WF U)
      (domainCode : RichCert sourceEnv env U registry target domain locals σ true ambient domainFootprint)
      (guard : PiGuard env U target σ A B prototypeDomain prototypeBody)
      (rows : RichRows sourceEnv env U registry target domain body locals σ relevant ambient values rowFootprint) :
      RichCert sourceEnv env U registry target (.pi hu hv domain body) locals σ relevant
        (Profile.pi prototypeDomain prototypeBody ambient values) (domainFootprint ++ rowFootprint)
  | route {first : EndpointState sourceEnv U source expression assigned}
      {last : EndpointState sourceEnv U source expression natural}
      (path : PrefixRoute sourceEnv U source expression first last)
      (certificate : RichCert sourceEnv env U registry target last locals σ relevant profile footprint) :
      RichCert sourceEnv env U registry target first locals σ relevant profile footprint
  | union
      (left : RichCert sourceEnv env U registry target node locals σ relevant p firstFootprint)
      (right : RichCert sourceEnv env U registry target node locals σ relevant q secondFootprint) :
      RichCert sourceEnv env U registry target node locals σ relevant (p.union q)
        (firstFootprint ++ secondFootprint)
  | pad (certificate : RichCert sourceEnv env U registry target node locals σ relevant profile footprint) :
      RichCert sourceEnv env U registry target node locals σ relevant profile.pad footprint
  | down (certificate : RichCert sourceEnv env U registry target node locals σ relevant
      (profile : Profile (n + 1)) footprint) :
      RichCert sourceEnv env U registry target node locals σ relevant profile.down footprint
  | map (view : AtomView env U registry target a b)
      (certificate : RichCert sourceEnv env U registry target node locals σ relevant profile footprint) :
      RichCert sourceEnv env U registry target node locals σ relevant (view.mapType profile) footprint
  | support (action : SupportAction env U registry target n)
      (certificate : RichCert sourceEnv env U registry target node locals σ relevant (profile : Profile n) footprint) :
      RichCert sourceEnv env U registry target node locals σ relevant (action.apply profile) footprint
  | select (certificate : RichCert sourceEnv env U registry target node locals σ relevant profile footprint)
      (member : atom ∈ profile.atoms) :
      RichCert sourceEnv env U registry target node locals σ relevant (.singleton atom) footprint

inductive RichRows : (sourceEnv env : VEnv) → (U : Nat) → (registry : CanonicalHead.Registry) →
    (target : List VExpr) →
    {source : List VExpr} → {A B : VExpr} → {u v : VLevel} →
    EndpointState sourceEnv U source A (.sort u) →
    EndpointState sourceEnv U (A :: source) B (.sort v) →
    List Nat → Subst → Bool → {n : Nat} → Profile n → List (Key n × Profile n) → Footprint → Type where
  | nil : RichRows sourceEnv env U registry target domain body locals σ relevant ambient [] []
  | cons {domain : EndpointState sourceEnv U source A (.sort u)}
      {body : EndpointState sourceEnv U (A :: source) B (.sort v)}
      {key : Key n} {packed support ambient : Profile n}
      (guard : LambdaGuard env U registry target σ A key ambient)
      (certificate : RichCert sourceEnv env U registry target body (Locals.push locals)
        (σ.cons key.anchor) relevant support bodyFootprint)
      (pack : BinderPack n packed bodyFootprint outside)
      (covered : ∀ atom ∈ packed.atoms, atom ∈ key.input.atoms)
      (tail : RichRows sourceEnv env U registry target domain body locals σ relevant ambient rows tailFootprint) :
      RichRows sourceEnv env U registry target domain body locals σ relevant ambient ((key, support) :: rows)
        (outside ++ tailFootprint)

inductive RichObs : (sourceEnv env : VEnv) → (U : Nat) → (registry : CanonicalHead.Registry) →
    (target : List VExpr) →
    {source : List VExpr} → {expression assigned : VExpr} →
    EndpointState sourceEnv U source expression assigned →
    List Nat → Subst → {n : Nat} → Profile n → Footprint → Type where
  /-- A finite rigid application demand retains its exact earlier-header
  code. The declared result may become a sort only after applying arguments;
  no literal declaration telescope is required. Frozen demand levels remain
  distinct from both the actual display and the genuine header seed. -/
  | rigidFamily {info : VConstant} {name : Name}
      {seedLevels frozenLevels levels : List VLevel}
      {node : EndpointState sourceEnv U source (.const name levels) assigned}
      (origin : ConstantHeaderOrigin sourceEnv name info)
      (lookup : env.constants name = some info)
      (inert : CanonicalDataHead.HeadInert registry name)
      (seedWF : ∀ level ∈ seedLevels, level.WF U)
      (seedLength : seedLevels.length = info.uvars)
      (frozenWF : ∀ level ∈ frozenLevels, level.WF U)
      (levelsWF : ∀ level ∈ levels, level.WF U)
      (seedFrozen : List.Forall₂ (· ≈ ·) seedLevels frozenLevels)
      (frozenLevelsEq : List.Forall₂ (· ≈ ·) frozenLevels levels)
      (typeClosed : info.type.Closed)
      (plan : RigidFamilySpine n)
      {support : Profile n} {typeRealization : Subst}
      (certificate : RichCert origin.source env U registry target
        (.ref (origin.familyHeader seedWF).reference) [] typeRealization true support [])
      (ready : plan.Ready env U registry target)
      (typed : (Profile.singleton (plan.atom name frozenLevels [])).HasType support) :
      RichObs sourceEnv env U registry target node locals σ
        (Profile.singleton (plan.atom name frozenLevels [])) []
  | family {info : VConstant} {name : Name} {seedLevels levels : List VLevel}
      {node : EndpointState sourceEnv U source (.const name levels) assigned}
      (origin : ConstantHeaderOrigin sourceEnv name info)
      (lookup : env.constants name = some info)
      (notDefinition : registry.definitions name = none)
      (notNative : registry.natives name = none)
      (notQuotient : name ≠ ``Quot.lift)
      (seedWF : ∀ level ∈ seedLevels, level.WF U)
      (seedLength : seedLevels.length = info.uvars)
      (levelsWF : ∀ level ∈ levels, level.WF U)
      (equivalent : List.Forall₂ (· ≈ ·) seedLevels levels)
      (signature : ConstantTelescope (info.type.instL seedLevels))
      (typeClosed : info.type.Closed)
      {typeSupport : Profile n} {typeRealization planRealization : Subst}
      (typeCertificate : RichCert origin.source env U registry target
        (.ref (origin.familyHeader seedWF).reference) [] typeRealization true typeSupport [])
      (typed : demand.HasType typeSupport)
      (tree : RichFamilyPlan env U registry target (origin.familyHeader seedWF).reference
        name seedLevels signature .nil planRealization [] demand []) :
      RichObs sourceEnv env U registry target node locals σ demand []
  | constructor {info : VConstant} {name : Name} {seedLevels levels : List VLevel}
      {node : EndpointState sourceEnv U source (.const name levels) assigned}
      (origin : ConstantHeaderOrigin sourceEnv name info)
      (lookup : env.constants name = some info)
      (notDefinition : registry.definitions name = none)
      (notNative : registry.natives name = none)
      (notQuotient : name ≠ ``Quot.lift)
      (seedWF : ∀ level ∈ seedLevels, level.WF U)
      (seedLength : seedLevels.length = info.uvars)
      (levelsWF : ∀ level ∈ levels, level.WF U)
      (equivalent : List.Forall₂ (· ≈ ·) seedLevels levels)
      (signature : ConstantTelescope (info.type.instL seedLevels))
      (typeClosed : info.type.Closed)
      {typeSupport : Profile n} {typeRealization planRealization : Subst}
      (typeCertificate : RichCert origin.source env U registry target
        (.ref (origin.familyHeader seedWF).reference) [] typeRealization true typeSupport [])
      (typed : demand.HasType typeSupport)
      (tree : RichConstructorPlan env U registry target (origin.familyHeader seedWF).reference
        name seedLevels signature .nil planRealization [] demand []) :
      RichObs sourceEnv env U registry target node locals σ demand []
  /-- Canonical definition opening retains exactly the original body chosen
  by the target equation order and its COMPUTED assigned formation. An
  arbitrary declaration-history source is not interchangeable with this source:
  its equations need not form a prefix of the chosen canonical order. -/
  | canonicalDelta {strata : EquationStratification env}
      {value : VDefVal} {seedLevels levels : List VLevel}
      {node : EndpointState sourceEnv U source (.const name levels) assigned}
      (lookup : registry.definitions name = some value)
      (nameEq : value.name = name)
      (registered : DefinitionRegistered env value)
      (seedWF : ∀ level ∈ seedLevels, level.WF U)
      (seedLength : seedLevels.length = value.uvars)
      (levelsWF : ∀ level ∈ levels, level.WF U)
      (equivalent : List.Forall₂ (· ≈ ·) seedLevels levels)
      (bodyClosed : value.value.Closed) (typeClosed : value.type.Closed)
      {support : Profile n} {typeRealization bodyRealization : Subst}
      (certificate : RichCert (strata.select registered.2).origin.source env U registry target
        (EndpointState.ref (.left (EquationHeaderOrigin.instantiatedRhs
          (strata.select registered.2).origin seedWF))).typeFormation.node
        [] typeRealization true support [])
      (typed : profile.HasType support)
      (body : RichObs (strata.select registered.2).origin.source env U registry target
        (.ref (.left (EquationHeaderOrigin.instantiatedRhs
          (strata.select registered.2).origin seedWF))) [] bodyRealization profile []) :
      RichObs sourceEnv env U registry target node locals σ profile []
  /-- A closed constant subterm under the enclosing canonical owner's charge. -/
  | canonicalConst {strata : EquationStratification env}
      {node : EndpointState sourceEnv U source (.const name levels) assigned}
      (origin : CanonicalConstOrigin env U registry strata name levels)
      (realization : Subst)
      (query : RichObs origin.owner.selected.origin.source env U registry target
        (.ref origin.site) [] realization profile footprint)
      (resources : footprint.Available (fun _ => [])) :
      RichObs sourceEnv env U registry target node locals σ profile []
  | legacy {node : EndpointState sourceEnv U source expression assigned}
      (observation : SortableObs env U registry target locals σ expression profile footprint) :
      RichObs sourceEnv env U registry target node locals σ profile footprint
  | code (certificate : RichCert sourceEnv env U registry target node locals σ relevant profile footprint) :
      RichObs sourceEnv env U registry target node locals σ profile footprint
  | projection {node : EndpointState sourceEnv U source (.proj name index major) assigned}
      (head : ProjectionHead node) {record : RecordData (Profile n)} {request : DataRequest (Profile n)}
      (nameEq : record.family.name = name) (member : (index, request) ∈ record.fields)
      (majorObservation : RichObs sourceEnv env U registry target (.ref (.right head.major))
        locals σ (.singleton (n := n + 1) (.record record)) majorFootprint)
      (fieldCertificate : RichCert sourceEnv env U registry target head.field locals σ true support fieldFootprint)
      (typed : request.input.HasType support)
      (alignment : DomainChain env U registry target request.input request.domain (head.fieldType.subst σ)) :
      RichObs sourceEnv env U registry target node locals σ request.input (majorFootprint ++ fieldFootprint)
  /-- A sortable field output can use a smaller assigned support than the
  retained record request. The finite output path supplies value code; the
  actual field certificate supplies its assigned support. The frozen request
  domain is not identified with the original field type. -/
  | projectionSortable {node : EndpointState sourceEnv U source (.proj name index major) assigned}
      (head : ProjectionHead node) {record : RecordData (Profile n)} {request : DataRequest (Profile n)}
      (nameEq : record.family.name = name) (member : (index, request) ∈ record.fields)
      (majorObservation : RichObs sourceEnv env U registry target (.ref (.right head.major))
        locals σ (.singleton (n := n + 1) (.record record)) majorFootprint)
      {atom : Atom n} {output : Atom m}
      (selected : atom ∈ request.input.atoms)
      (path : GeneralOutputPath env U registry target atom output)
      (sortable : (Profile.singleton output).HasType (.sort relevant))
      (fieldCertificate : RichCert sourceEnv env U registry target head.field locals σ true support fieldFootprint)
      (typed : (Profile.singleton output).HasType support) :
      RichObs sourceEnv env U registry target node locals σ (.singleton output)
        (majorFootprint ++ fieldFootprint)
  | app {domain : EndpointState sourceEnv U source A (.sort u)}
      {body : EndpointState sourceEnv U (A :: source) B (.sort v)}
      {function : EndpointState sourceEnv U source f (.forallE A B)}
      {argument : EndpointState sourceEnv U source a A}
      {result : EndpointState sourceEnv U source (B.inst a) (.sort v)}
      (hu : u.WF U) (hv : v.WF U) {key : Key n} {output : Atom n}
      (fn : RichObs sourceEnv env U registry target function locals σ (Profile.fn key output) fnFootprint)
      (arg : RichObs sourceEnv env U registry target argument locals σ rawInput argFootprint)
      (arguments : GeneralNormalProfileAdapter env U registry target rawInput key.input)
      (admitted : Admitted env U registry target key (a.subst σ) (a.subst σ)) :
      RichObs sourceEnv env U registry target (.app hu hv domain body function argument result)
        locals σ (.singleton output) (fnFootprint ++ argFootprint)
  | lam {domain : EndpointState sourceEnv U source A (.sort u)}
      {codomain : EndpointState sourceEnv U (A :: source) B (.sort v)}
      {body : EndpointState sourceEnv U (A :: source) expression B}
      (hu : u.WF U) (hv : v.WF U) {key : Key n} {output : Atom n} {support packed : Profile n}
      (domainCode : RichCert sourceEnv env U registry target domain locals σ true support domainFootprint)
      (guard : LambdaGuard env U registry target σ A key support)
      (observation : RichObs sourceEnv env U registry target body (Locals.push locals)
        (σ.cons key.anchor) (.singleton output) bodyFootprint)
      (pack : BinderPack n packed bodyFootprint outside)
      (covered : ∀ atom ∈ packed.atoms, atom ∈ key.input.atoms) :
      RichObs sourceEnv env U registry target (.lam hu hv domain codomain body)
        locals σ (Profile.fn key output) (domainFootprint ++ outside)
  | route {first : EndpointState sourceEnv U source expression assigned}
      {last : EndpointState sourceEnv U source expression natural}
      (path : PrefixRoute sourceEnv U source expression first last)
      (observation : RichObs sourceEnv env U registry target last locals σ profile footprint) :
      RichObs sourceEnv env U registry target first locals σ profile footprint
  | union
      (left : RichObs sourceEnv env U registry target node locals σ p firstFootprint)
      (right : RichObs sourceEnv env U registry target node locals σ q secondFootprint) :
      RichObs sourceEnv env U registry target node locals σ (p.union q) (firstFootprint ++ secondFootprint)
  | view (source : RichObs sourceEnv env U registry target node locals σ (.singleton a) footprint)
      (view : AtomView env U registry target a b) :
      RichObs sourceEnv env U registry target node locals σ (.singleton b) footprint
  | action (source : RichObs sourceEnv env U registry target node locals σ (.singleton a) footprint)
      (action : AtomAction env U registry target a b) :
      RichObs sourceEnv env U registry target node locals σ (.singleton b) footprint
  | select (source : RichObs sourceEnv env U registry target node locals σ profile footprint)
      (member : atom ∈ profile.atoms) :
      RichObs sourceEnv env U registry target node locals σ (.singleton atom) footprint
  | pad (source : RichObs sourceEnv env U registry target node locals σ profile footprint) :
      RichObs sourceEnv env U registry target node locals σ profile.pad footprint
  | unpad (source : RichObs sourceEnv env U registry target node locals σ profile.pad footprint) :
      RichObs sourceEnv env U registry target node locals σ profile footprint

/-- Each declared domain is an actual occurrence in the retained earlier
header. Rich projected type queries stay at that original occurrence. -/
inductive RichFamilyPlan : (env : VEnv) → (U : Nat) → (registry : CanonicalHead.Registry) →
    (target : List VExpr) → {headerEnv : VEnv} → {declaredType : VExpr} → {headerLevel : VLevel} →
    (header : EndpointRef headerEnv U [] declaredType (.sort headerLevel)) →
    (name : Name) → (levels : List VLevel) → (signature : ConstantTelescope declaredType) →
    {source : List VExpr} → (context : ContextDerivation headerEnv U source) → Subst →
    (arguments : List VExpr) → {n : Nat} → Profile n → Footprint → Type where
  | terminal {header : EndpointRef headerEnv U [] declaredType (.sort headerLevel)}
      {name : Name} {levels : List VLevel} {signature : ConstantTelescope declaredType}
      {source : List VExpr} {context : ContextDerivation headerEnv U source} {σ : Subst}
      {arguments : List VExpr} {keys : List (DataRequest (Profile n))}
      (saturated : arguments.length = signature.domains.length)
      (resultSort : signature.result = .sort level)
      (relevance : Relevant level relevant)
      (captures : FamilyCaptures env U registry target source (List.range arguments.length)
        σ (constantCaptureVariables arguments.length) keys footprint) :
      RichFamilyPlan env U registry target header name levels signature context σ arguments
        (n := n + 1) (.singleton (.family ⟨name, levels, relevant, keys⟩)) footprint
  | binder {header : EndpointRef headerEnv U [] declaredType (.sort headerLevel)}
      {name : Name} {levels : List VLevel} {signature : ConstantTelescope declaredType}
      {source : List VExpr} {context : ContextDerivation headerEnv U source} {σ : Subst}
      {arguments : List VExpr} {domain : VExpr} {level : VLevel} {key : Key n} {output : Atom n}
      {support packed : Profile n}
      (domainOrigin : signature.domains[arguments.length]? = some domain)
      (original : EndpointRef headerEnv U source domain (.sort level))
      (location : Located header (.ref original))
      (lineage : location.contextDerivation .nil = context)
      (domainCode : RichCert headerEnv env U registry target (.ref original) (List.range arguments.length)
        σ true support domainFootprint)
      (guard : LambdaGuard env U registry target σ domain key support)
      (body : RichFamilyPlan env U registry target header name levels signature (.cons context original) (σ.cons key.anchor) (arguments ++ [key.anchor])
        (.singleton output) bodyFootprint)
      (pack : BinderPack n packed bodyFootprint outside)
      (covered : ∀ atom ∈ packed.atoms, atom ∈ key.input.atoms) :
      RichFamilyPlan env U registry target header name levels signature context σ arguments (Profile.fn key output)
        (domainFootprint ++ outside)
  | view {header : EndpointRef headerEnv U [] declaredType (.sort headerLevel)}
      {name : Name} {levels : List VLevel} {signature : ConstantTelescope declaredType}
      {source : List VExpr} {context : ContextDerivation headerEnv U source} {σ : Subst}
      (source : RichFamilyPlan env U registry target header name levels signature context σ arguments
        (.singleton oldAtom) footprint)
      (view : AtomView env U registry target oldAtom newAtom) :
      RichFamilyPlan env U registry target header name levels signature context σ arguments (.singleton newAtom) footprint
  | pad {header : EndpointRef headerEnv U [] declaredType (.sort headerLevel)}
      {name : Name} {levels : List VLevel} {signature : ConstantTelescope declaredType}
      {source : List VExpr} {context : ContextDerivation headerEnv U source} {σ : Subst}
      (source : RichFamilyPlan env U registry target header name levels signature context σ arguments demand footprint) :
      RichFamilyPlan env U registry target header name levels signature context σ arguments demand.pad footprint

/-- Native constructor plans retain projected domain certificates and the
actual original result-type occurrence, including nullary constructors. -/
inductive RichConstructorPlan : (env : VEnv) → (U : Nat) → (registry : CanonicalHead.Registry) →
    (target : List VExpr) → {headerEnv : VEnv} → {declaredType : VExpr} → {headerLevel : VLevel} →
    (header : EndpointRef headerEnv U [] declaredType (.sort headerLevel)) →
    (name : Name) → (levels : List VLevel) → (signature : ConstantTelescope declaredType) →
    {source : List VExpr} → (context : ContextDerivation headerEnv U source) → Subst →
    (arguments : List VExpr) → {n : Nat} → Profile n → Footprint → Type where
  | terminal {header : EndpointRef headerEnv U [] declaredType (.sort headerLevel)}
      {name : Name} {levels : List VLevel} {signature : ConstantTelescope declaredType}
      {source : List VExpr} {context : ContextDerivation headerEnv U source} {σ : Subst}
      {arguments : List VExpr} {family : FamilyData (Profile n)}
      {keys : List (DataRequest (Profile n))} {familyLevels : List VLevel}
      {familyArguments : List VExpr} {resultLevel : VLevel}
      (saturated : arguments.length = signature.domains.length)
      (resultShape : signature.result = mkApps (.const family.name familyLevels) familyArguments)
      (relevant : family.relevant = true)
      (resultNode : EndpointState headerEnv U source signature.result (.sort resultLevel))
      (resultLocation : Located header resultNode)
      (resultLineage : resultLocation.contextDerivation .nil = context)
      (captures : FamilyCaptures env U registry target source (List.range arguments.length)
        σ (constantCaptureVariables arguments.length) keys captureFootprint)
      (resultCode : RichCert headerEnv env U registry target resultNode
        (List.range arguments.length) σ true
        (Profile.singleton (n := n + 1) (.family family)) resultFootprint) :
      RichConstructorPlan env U registry target header name levels signature context σ arguments
        (n := n + 1) (.singleton (.ctor ⟨name, levels, keys, family, relevant⟩))
        (captureFootprint ++ resultFootprint)
  | terminalRecord {header : EndpointRef headerEnv U [] declaredType (.sort headerLevel)}
      {name : Name} {levels : List VLevel} {signature : ConstantTelescope declaredType}
      {source : List VExpr} {context : ContextDerivation headerEnv U source} {σ : Subst}
      {arguments : List VExpr} {demand : RecordData (Profile n)}
      {projection : VProjectionInfo} {familyLevels : List VLevel}
      {familyArguments : List VExpr} {resultLevel : VLevel}
      (registered : env.projections demand.family.name projection)
      (projectionLookup : registry.projections demand.family.name = some projection)
      (constructorName : projection.ctorName = name)
      (bounded : ∀ entry ∈ demand.fields, entry.1 < projection.numFields)
      (saturated : arguments.length = signature.domains.length)
      (resultShape : signature.result = mkApps (.const demand.family.name familyLevels) familyArguments)
      (resultNode : EndpointState headerEnv U source signature.result (.sort resultLevel))
      (resultLocation : Located header resultNode)
      (resultLineage : resultLocation.contextDerivation .nil = context)
      (captures : FamilyCaptures env U registry target source (List.range arguments.length)
        σ (demand.fields.map fun entry => .bvar
          (arguments.length - 1 - (projection.nparams + entry.1)))
        (demand.fields.map (·.2)) captureFootprint)
      (resultCode : RichCert headerEnv env U registry target resultNode
        (List.range arguments.length) σ true
        (Profile.singleton (n := n + 1) (.family demand.family)) resultFootprint)
      (origins : ∀ entry ∈ demand.fields,
        Nonempty (RankedData.ProjectionOrigin env U target projection demand.family.name entry.1
          (mkApps (.const name levels)
            ((constantCaptureVariables arguments.length).map (·.subst σ)))
          (signature.result.subst σ) entry.2.domain)) :
      RichConstructorPlan env U registry target header name levels signature context σ arguments
        (n := n + 1) (.singleton (.record demand)) (captureFootprint ++ resultFootprint)
  | binder {header : EndpointRef headerEnv U [] declaredType (.sort headerLevel)}
      {name : Name} {levels : List VLevel} {signature : ConstantTelescope declaredType}
      {source : List VExpr} {context : ContextDerivation headerEnv U source} {σ : Subst}
      {arguments : List VExpr} {domain : VExpr} {level : VLevel} {key : Key n} {output : Atom n}
      {support packed : Profile n}
      (domainOrigin : signature.domains[arguments.length]? = some domain)
      (original : EndpointRef headerEnv U source domain (.sort level))
      (location : Located header (.ref original))
      (lineage : location.contextDerivation .nil = context)
      (domainCode : RichCert headerEnv env U registry target (.ref original) (List.range arguments.length)
        σ true support domainFootprint)
      (guard : LambdaGuard env U registry target σ domain key support)
      (body : RichConstructorPlan env U registry target header name levels signature (.cons context original) (σ.cons key.anchor) (arguments ++ [key.anchor])
        (.singleton output) bodyFootprint)
      (pack : BinderPack n packed bodyFootprint outside)
      (covered : ∀ atom ∈ packed.atoms, atom ∈ key.input.atoms) :
      RichConstructorPlan env U registry target header name levels signature context σ arguments (Profile.fn key output)
        (domainFootprint ++ outside)
  | view {header : EndpointRef headerEnv U [] declaredType (.sort headerLevel)}
      {name : Name} {levels : List VLevel} {signature : ConstantTelescope declaredType}
      {source : List VExpr} {context : ContextDerivation headerEnv U source} {σ : Subst}
      (source : RichConstructorPlan env U registry target header name levels signature context σ arguments
        (.singleton oldAtom) footprint)
      (view : AtomView env U registry target oldAtom newAtom) :
      RichConstructorPlan env U registry target header name levels signature context σ arguments (.singleton newAtom) footprint
  | pad {header : EndpointRef headerEnv U [] declaredType (.sort headerLevel)}
      {name : Name} {levels : List VLevel} {signature : ConstantTelescope declaredType}
      {source : List VExpr} {context : ContextDerivation headerEnv U source} {σ : Subst}
      (source : RichConstructorPlan env U registry target header name levels signature context σ arguments demand footprint) :
      RichConstructorPlan env U registry target header name levels signature context σ arguments demand.pad footprint

/-- Finite type code with a retained canonical charge and explicit binder
resources. Every root contains an actual selected original formation and its
actual certificate. No interpretation function or completed comparison is
stored in this syntax. -/
inductive RichCodeRecipe : (env : VEnv) → (U : Nat) →
    (registry : CanonicalHead.Registry) → (target : List VExpr) →
    (source : List VExpr) → (locals : List Nat) → (σ : Subst) →
      (expression : VExpr) → (relevant : Bool) → {n : Nat} → Profile n → Footprint → Type where
  | root (source : List VExpr) (locals : List Nat) (σ : Subst)
      {strata : EquationStratification env} {name : Name}
      (owner : CanonicalCodeOwner env registry strata name)
      (node : EndpointState owner.selected.origin.source U [] canonicalExpression (.sort level))
      (closed : canonicalExpression.Closed)
      (expressionEq : EqUpToLevels U canonicalExpression expression)
      (realization : Subst)
      (certificate : RichCert owner.selected.origin.source env U registry target node
        [] realization relevant profile footprint)
      (resources : footprint.Available (fun _ => [])) :
      RichCodeRecipe env U registry target source locals σ expression relevant profile []
  | domain
      (parent : RichCodeRecipe env U registry target source locals σ (.forallE A B)
        relevant (.pi prototypeDomain prototypeBody (support : Profile n) rows) footprint) :
      RichCodeRecipe env U registry target source locals σ A true support footprint
  | body
      (parent : RichCodeRecipe env U registry target source locals σ.tail (.forallE A B)
        relevant (.pi prototypeDomain prototypeBody (support : Profile n) rows) footprint)
      (selected : (key, result) ∈ rows)
      (anchor : key.anchor = σ 0) :
      RichCodeRecipe env U registry target (A :: source) (Locals.push locals) σ B relevant result
        ((0, ⟨n, key.input⟩) :: footprint.sourceLift (.skip .refl))
  | fixedBody
      (parent : RichCodeRecipe env U registry target source locals σ (.forallE A B.lift)
        relevant (.pi prototypeDomain prototypeBody (support : Profile n) rows) footprint)
      (selected : (key, result) ∈ rows)
      (admitted : Admitted env U registry target key anchor anchor) :
      RichCodeRecipe env U registry target source locals σ B relevant result footprint
  | resources
      (parent : RichCodeRecipe env U registry target source locals σ expression relevant profile required)
      (transfer : RecipeResourceTransfer env U registry target locals σ required footprint) :
      RichCodeRecipe env U registry target source locals σ expression relevant profile footprint
  | action
      (change : SortableCodeAction env U registry target relevant profile nextRelevant nextProfile)
      (parent : RichCodeRecipe env U registry target source locals σ expression relevant profile footprint) :
      RichCodeRecipe env U registry target source locals σ expression nextRelevant nextProfile footprint

end

mutual
theorem RichCert.formed (certificate : RichCert sourceEnv env U registry target node locals σ relevant profile footprint) :
    profile.HasType (.sort relevant) := by
  match certificate with
  | .legacy source => exact source.formed
  | .recipe code => exact code.formed
  | .observe _ formed => exact formed
  | .pi _ _ domain _ rows =>
    exact Profile.HasType.pi_iff.mpr ⟨Profile.WF.pi_iff.mpr
      ⟨domain.formed, fun key output member =>
        ⟨(rows.typed member).1, (rows.typed member).2.wf_value⟩⟩,
      fun key output member => (rows.typed member).2⟩
  | .route _ source => exact source.formed
  | .union first second => exact first.formed.union second.formed
  | .pad source => exact source.formed.pad_sort
  | .down source => simpa only [Profile.down_sort] using source.formed.down
  | .map view source => exact view.mapType_sort source.formed
  | .support action source => exact action.preservesSort source.formed
  | .select source member => exact source.formed.singleton_of_mem member
termination_by sizeOf certificate
decreasing_by all_goals simp_wf <;> omega

theorem RichRows.typed
    (rows : RichRows sourceEnv env U registry target domain body locals σ relevant ambient values footprint)
    (member : (key, output) ∈ values) : key.input.HasType ambient ∧ output.HasType (.sort relevant) := by
  match rows with
  | .nil => cases member
  | .cons guard code pack covered tail =>
    rcases List.mem_cons.mp member with equal | member
    · have result := code.formed
      cases equal
      exact ⟨guard.inputTyped, result⟩
    · exact tail.typed member
termination_by sizeOf rows
decreasing_by all_goals simp_wf <;> omega

theorem RichCodeRecipe.formed
    (recipe : RichCodeRecipe env U registry target source locals σ expression relevant profile footprint) :
    profile.HasType (.sort relevant) := by
  match recipe with
  | .root _ _ _ _ _ _ _ _ certificate _ => exact certificate.formed
  | .domain parent => exact (Profile.WF.pi_iff.mp parent.formed.1).1
  | .body parent selected _ | .fixedBody parent selected _ =>
    exact (Profile.HasType.pi_iff.mp parent.formed).2 _ _ selected
  | .resources parent _ => exact parent.formed
  | .action change parent => exact richCodeAction_formed change parent.formed
termination_by sizeOf recipe
decreasing_by all_goals simp_wf <;> omega

end

def RichCert.ofCast {node : EndpointState sourceEnv U source expression assigned}
    (expressionEq : expression = nextExpression) (typeEq : assigned = nextType)
    (certificate : RichCert sourceEnv env U registry target (node.cast expressionEq typeEq)
      locals σ relevant profile footprint) :
    RichCert sourceEnv env U registry target node locals σ relevant profile footprint := by
  cases expressionEq
  cases typeEq
  exact certificate

/-- Each source demand is retained either at an exactly matching destination
slot or by an actual finite original destination query. The output footprint
is computed from those queries; foreign owner resources are never erased. -/
inductive RichFootprintTransfer
    (sourceRaw : Subst) (destinationEnv env : VEnv) (U : Nat)
    (registry : CanonicalHead.Registry) (target : List VExpr)
    {destinationSource : List VExpr}
    (context : ContextDerivation destinationEnv U destinationSource)
    (destinationRaw : Subst) (locals : List Nat) (commonLeft : Subst) :
    Footprint → Footprint → Type where
  | nil : RichFootprintTransfer sourceRaw destinationEnv env U registry target context destinationRaw locals commonLeft [] []
  | local (agreement : sourceRaw index = destinationRaw destinationIndex)
      (tail : RichFootprintTransfer sourceRaw destinationEnv env U registry target context destinationRaw locals commonLeft needs footprint) :
      RichFootprintTransfer sourceRaw destinationEnv env U registry target context destinationRaw locals commonLeft
        ((index, need) :: needs) ((destinationIndex, need) :: footprint)
  | query
      (node : EndpointState destinationEnv U destinationSource expression assigned)
      (provenance : EndpointProvenance context node)
      (agreement : expression.subst destinationRaw = sourceRaw index)
      (bound : need.rank ≤ rank)
      (observation : RichObs destinationEnv env U registry target node locals
        (destinationRaw.comp commonLeft) (profile : Profile rank) queryFootprint)
      (adapter : GeneralNormalProfileAdapter env U registry target profile (raiseProfile rank bound need.profile))
      (tail : RichFootprintTransfer sourceRaw destinationEnv env U registry target context destinationRaw locals commonLeft needs footprint) :
      RichFootprintTransfer sourceRaw destinationEnv env U registry target context destinationRaw locals commonLeft
        ((index, need) :: needs) (queryFootprint ++ footprint)


end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
