import Lean4Lean.Theory.Typing.EquationHeaderDerivation
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldProvenance
import Lean4Lean.Theory.Typing.AnchoredOriginalRichRecordExtraction

/-! Query-owned provenance is separate from frame provenance. These positive
annotations name the exact observer, so extracting a record observer cannot
silently substitute an unrelated query. Every shared Rich, Sortable and legacy
query/plan constructor recurses into its stored children. Legacy opening nodes
also retain actual original header/equation sites; target registration alone
is not an opening bound. Shared code recipes retain the exact canonical stratification and original
formation child. Their binder demands remain in the indexed footprint. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalFactorCut
open InductiveSignature
open NativeRecursorData (SaturatedProgram)
open private recordShape_raise recordShape_normal recordAdapter_rigid from
  Lean4Lean.Theory.Typing.AnchoredOriginalRichRecordExtraction
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

/-- An actual original call site with its exact semantic frame environment.
Neither a numerical cost nor a freely chosen list of worlds is provenance. -/
structure WorldQuerySite {registry : CanonicalHead.Registry} {target : List VExpr}
    (strata : EquationStratification env)
    (node : EndpointState sourceEnv U source expression assigned)
    (locals : List Nat) (σ : Subst) where
  context : ContextDerivation sourceEnv U source
  provenance : EndpointProvenance context node
  right : Subst
  available : Valuation
  frame : OriginalRichFrame sourceEnv env U registry target context locals σ right available
  annotation : OriginalFrameWorldProvenance strata frame

noncomputable def WorldQuerySite.worlds
    (site : WorldQuerySite (registry := registry) (target := target) strata node locals σ) :
    List (EquationWorldClosureOrder.World strata.rules.length) :=
  (WorldClosureProvenance.original node site.annotation.controls site.annotation.environment).worlds

/-- A canonical closed opening has the actual empty source frame. No unused
reserve can be inserted into its purported original call site. -/
noncomputable def WorldQuerySite.empty
    {node : EndpointState sourceEnv U [] expression assigned}
    (controls : OriginalWorldControls strata sourceEnv)
    (provenance : EndpointProvenance (.nil : ContextDerivation sourceEnv U []) node)
    (realization : Subst) :
    WorldQuerySite (registry := registry) (target := target) strata node [] realization where
  context := .nil
  provenance := provenance
  right := realization
  available := fun _ => []
  frame := .nil
  annotation := ⟨controls, .nil⟩

mutual
inductive WorldObsProvenance (strata : EquationStratification env) :
    {sourceEnv : VEnv} → {U : Nat} → {registry : CanonicalHead.Registry} → {target : List VExpr} →
    {source : List VExpr} → {expression assigned : VExpr} →
    {node : EndpointState sourceEnv U source expression assigned} → {locals : List Nat} → {σ : Subst} →
    {n : Nat} → {profile : Profile n} → {footprint : Footprint} →
    RichObs sourceEnv env U registry target node locals σ profile footprint → Type where
  | var {node : EndpointState sourceEnv U source (.bvar i) assigned} :
      WorldObsProvenance strata (RichObs.legacy (node := node) (.legacy (.var locals σ i profile)))
  | empty {node : EndpointState sourceEnv U source expression assigned} :
      WorldObsProvenance strata (RichObs.legacy (node := node) (locals := locals) (σ := σ)
        (.legacy (Obs.empty (n := n))))
  | sort {node : EndpointState sourceEnv U source (.sort level) assigned}
      (relevant : Relevant level flag) :
      WorldObsProvenance strata (RichObs.legacy (node := node) (locals := locals) (σ := σ)
        (.legacy (Obs.sort (n := n) relevant)))
  | canonicalDelta {value : VDefVal} {seedLevels levels : List VLevel}
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
      {body : RichObs (strata.select registered.2).origin.source env U registry target
        (.ref (.left (EquationHeaderOrigin.instantiatedRhs
          (strata.select registered.2).origin seedWF))) [] bodyRealization profile []}
      (certificateProvenance : WorldCertProvenance strata certificate)
      (bodyProvenance : WorldObsProvenance strata body)
      (controls : OriginalWorldControls strata (strata.select registered.2).origin.source)
      (typeProvenance : EndpointProvenance .nil
        (EndpointState.ref (.left (EquationHeaderOrigin.instantiatedRhs
          (strata.select registered.2).origin seedWF))).typeFormation.node)
      (bodyProvenanceSite : EndpointProvenance .nil
        (.ref (.left (EquationHeaderOrigin.instantiatedRhs
          (strata.select registered.2).origin seedWF)))) :
      WorldObsProvenance strata (RichObs.canonicalDelta (strata := strata)
        (node := node) (locals := locals) (σ := σ) lookup nameEq registered
        seedWF seedLength levelsWF equivalent bodyClosed typeClosed certificate typed body)
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
      (typed : (Profile.singleton (plan.atom name frozenLevels [])).HasType support)
      (child : WorldCertProvenance strata certificate)
      (controls : OriginalWorldControls strata origin.source)
      (provenance : EndpointProvenance .nil (.ref (origin.familyHeader seedWF).reference)) :
      WorldObsProvenance strata (RichObs.rigidFamily (node := node) (locals := locals) (σ := σ)
        origin lookup inert seedWF seedLength frozenWF levelsWF seedFrozen frozenLevelsEq
        typeClosed plan certificate ready typed)
  | canonicalConst
      {node : EndpointState sourceEnv U source (.const name levels) assigned}
      (origin : CanonicalConstOrigin env U registry strata name levels)
      (realization : Subst)
      (query : RichObs origin.owner.selected.origin.source env U registry target
        (.ref origin.site) [] realization profile footprint)
      (resources : footprint.Available (fun _ => []))
      (child : WorldObsProvenance strata query)
      (controls : OriginalWorldControls strata origin.owner.selected.origin.source)
      (provenance : EndpointProvenance .nil (.ref origin.site)) :
      WorldObsProvenance strata (RichObs.canonicalConst (node := node)
        (locals := locals) (σ := σ) origin realization query resources)
  | code (child : WorldCertProvenance strata certificate) :
      WorldObsProvenance strata (.code certificate)
  | projection {node : EndpointState sourceEnv U source (.proj name index majorExpression) assigned}
      {record : RecordData (Profile n)} {request : DataRequest (Profile n)}
      (head : ProjectionHead node) (nameEq : record.family.name = name)
      (member : (index, request) ∈ record.fields)
      {majorObservation : RichObs sourceEnv env U registry target (.ref (.right head.major))
        locals σ (.singleton (n := n + 1) (.record record)) majorFootprint}
      {fieldCertificate : RichCert sourceEnv env U registry target head.field locals σ true support fieldFootprint}
      (major : WorldObsProvenance strata majorObservation)
      (field : WorldCertProvenance strata fieldCertificate)
      (majorSite : WorldQuerySite (registry := registry) (target := target) strata
        (.ref (.right head.major)) locals σ)
      (fieldSite : WorldQuerySite (registry := registry) (target := target) strata head.field locals σ)
      (typed : request.input.HasType support)
      (alignment : DomainChain env U registry target request.input request.domain (head.fieldType.subst σ)) :
      WorldObsProvenance strata (.projection head nameEq member majorObservation fieldCertificate typed alignment)
  | projectionSortable {node : EndpointState sourceEnv U source (.proj name index majorExpression) assigned}
      {record : RecordData (Profile n)} {request : DataRequest (Profile n)}
      (head : ProjectionHead node) (nameEq : record.family.name = name)
      (member : (index, request) ∈ record.fields)
      {majorObservation : RichObs sourceEnv env U registry target (.ref (.right head.major))
        locals σ (.singleton (n := n + 1) (.record record)) majorFootprint}
      {atom : Atom n} {output : Atom m}
      (selected : atom ∈ request.input.atoms)
      (path : GeneralOutputPath env U registry target atom output)
      (sortable : (Profile.singleton output).HasType (.sort relevant))
      {fieldCertificate : RichCert sourceEnv env U registry target head.field locals σ true support fieldFootprint}
      (major : WorldObsProvenance strata majorObservation)
      (field : WorldCertProvenance strata fieldCertificate)
      (majorSite : WorldQuerySite (registry := registry) (target := target) strata
        (.ref (.right head.major)) locals σ)
      (fieldSite : WorldQuerySite (registry := registry) (target := target) strata head.field locals σ)
      (typed : (Profile.singleton output).HasType support) :
      WorldObsProvenance strata (.projectionSortable head nameEq member majorObservation
        selected path sortable fieldCertificate typed)
  | app {domain : EndpointState sourceEnv U source A (.sort u)}
      {body : EndpointState sourceEnv U (A :: source) B (.sort v)}
      {function : EndpointState sourceEnv U source f (.forallE A B)}
      {argument : EndpointState sourceEnv U source a A}
      {result : EndpointState sourceEnv U source (B.inst a) (.sort v)}
      {key : Key n} {output : Atom n}
      {fnQuery : RichObs sourceEnv env U registry target function locals σ (Profile.fn key output) fnFootprint}
      {argQuery : RichObs sourceEnv env U registry target argument locals σ rawInput argFootprint}
      (hu : u.WF U) (hv : v.WF U)
      (fn : WorldObsProvenance strata fnQuery) (arg : WorldObsProvenance strata argQuery)
      (arguments : GeneralNormalProfileAdapter env U registry target rawInput key.input)
      (admitted : Admitted env U registry target key (a.subst σ) (a.subst σ)) :
      WorldObsProvenance strata (.app (domain := domain) (body := body) (result := result)
        hu hv fnQuery argQuery arguments admitted)
  | route (path : PrefixRoute sourceEnv U source expression first last)
      (child : WorldObsProvenance strata observation) :
      WorldObsProvenance strata (.route path observation)
  | union (first : WorldObsProvenance strata left) (second : WorldObsProvenance strata right) :
      WorldObsProvenance strata (.union left right)
  | view {observation : RichObs sourceEnv env U registry target node locals σ (.singleton a) footprint}
      (child : WorldObsProvenance strata observation) (view : AtomView env U registry target a b) :
      WorldObsProvenance strata (.view observation view)
  | action {observation : RichObs sourceEnv env U registry target node locals σ (.singleton a) footprint}
      (child : WorldObsProvenance strata observation) (action : AtomAction env U registry target a b) :
      WorldObsProvenance strata (.action observation action)
  | select {observation : RichObs sourceEnv env U registry target node locals σ profile footprint}
      (child : WorldObsProvenance strata observation) (member : atom ∈ profile.atoms) :
      WorldObsProvenance strata (.select observation member)
  | pad (child : WorldObsProvenance strata observation) : WorldObsProvenance strata (.pad observation)
  | unpad (child : WorldObsProvenance strata observation) : WorldObsProvenance strata (.unpad observation)
  | castProfile {observation : RichObs sourceEnv env U registry target node locals σ profile footprint}
      (equal : profile = nextProfile) (child : WorldObsProvenance strata observation) :
      WorldObsProvenance strata ((congrArg (fun p => RichObs sourceEnv env U registry target node locals σ p footprint) equal).mp observation)
  | lowerRaised {bound : n ≤ N}
      {observation : RichObs sourceEnv env U registry target node locals σ (raiseProfile N bound profile) footprint}
      (child : WorldObsProvenance strata observation) : WorldObsProvenance strata observation.lowerRaised
  | family {info : VConstant}
      {name : Name}
      {seedLevels levels : List VLevel}
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
      {typeSupport : Profile n}
      {typeRealization planRealization : Subst}
      (typeCertificate : RichCert origin.source env U registry target
        (.ref (origin.familyHeader seedWF).reference) [] typeRealization true typeSupport [])
      (typed : demand.HasType typeSupport)
      (tree : RichFamilyPlan env U registry target (origin.familyHeader seedWF).reference
        name seedLevels signature .nil planRealization [] demand [])
      (typeCertificateProvenance : WorldCertProvenance strata typeCertificate)
      (treeProvenance : WorldFamilyPlanProvenance strata tree)
      (headerSite : WorldQuerySite (registry := registry) (target := target) strata
        (.ref (origin.familyHeader seedWF).reference) [] typeRealization) :
      WorldObsProvenance strata (show RichObs sourceEnv env U registry target node locals σ demand [] from RichObs.family (node := node) origin lookup notDefinition notNative notQuotient seedWF seedLength levelsWF equivalent signature typeClosed typeCertificate typed tree)
  | constructor {info : VConstant}
      {name : Name}
      {seedLevels levels : List VLevel}
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
      {typeSupport : Profile n}
      {typeRealization planRealization : Subst}
      (typeCertificate : RichCert origin.source env U registry target
        (.ref (origin.familyHeader seedWF).reference) [] typeRealization true typeSupport [])
      (typed : demand.HasType typeSupport)
      (tree : RichConstructorPlan env U registry target (origin.familyHeader seedWF).reference
        name seedLevels signature .nil planRealization [] demand [])
      (typeCertificateProvenance : WorldCertProvenance strata typeCertificate)
      (treeProvenance : WorldConstructorPlanProvenance strata tree)
      (headerSite : WorldQuerySite (registry := registry) (target := target) strata
        (.ref (origin.familyHeader seedWF).reference) [] typeRealization) :
      WorldObsProvenance strata (show RichObs sourceEnv env U registry target node locals σ demand [] from RichObs.constructor (node := node) origin lookup notDefinition notNative notQuotient seedWF seedLength levelsWF equivalent signature typeClosed typeCertificate typed tree)
  | legacy {node : EndpointState sourceEnv U source expression assigned}
      (observation : SortableObs env U registry target locals σ expression profile footprint)
      (observationProvenance : WorldSortableObsProvenance strata observation) :
      WorldObsProvenance strata (show RichObs sourceEnv env U registry target node locals σ profile footprint from RichObs.legacy observation)
  | lam {domain : EndpointState sourceEnv U source A (.sort u)}
      {codomain : EndpointState sourceEnv U (A :: source) B (.sort v)}
      {body : EndpointState sourceEnv U (A :: source) expression B}
      (hu : u.WF U)
      (hv : v.WF U)
      {key : Key n}
      {output : Atom n}
      {support packed : Profile n}
      (domainCode : RichCert sourceEnv env U registry target domain locals σ true support domainFootprint)
      (guard : LambdaGuard env U registry target σ A key support)
      (observation : RichObs sourceEnv env U registry target body (Locals.push locals)
        (σ.cons key.anchor) (.singleton output) bodyFootprint)
      (pack : BinderPack n packed bodyFootprint outside)
      (covered : ∀ atom ∈ packed.atoms, atom ∈ key.input.atoms)
      (domainCodeProvenance : WorldCertProvenance strata domainCode)
      (observationProvenance : WorldObsProvenance strata observation) :
      WorldObsProvenance strata (show RichObs sourceEnv env U registry target (.lam hu hv domain codomain body)
        locals σ (Profile.fn key output) (domainFootprint ++ outside) from RichObs.lam hu hv domainCode guard observation pack covered)
inductive WorldCertProvenance (strata : EquationStratification env) :
    {sourceEnv : VEnv} → {U : Nat} → {registry : CanonicalHead.Registry} → {target : List VExpr} →
    {source : List VExpr} → {expression assigned : VExpr} →
    {node : EndpointState sourceEnv U source expression assigned} → {locals : List Nat} → {σ : Subst} →
    {relevant : Bool} → {n : Nat} → {profile : Profile n} → {footprint : Footprint} →
    RichCert sourceEnv env U registry target node locals σ relevant profile footprint → Type where
  | recipe {node : EndpointState sourceEnv U source expression assigned}
      {code : RichCodeRecipe env U registry target source locals σ expression relevant profile footprint}
      (child : WorldCodeRecipeProvenance strata code) :
      WorldCertProvenance strata (RichCert.recipe (node := node) code)
  | observe {observation : RichObs sourceEnv env U registry target node locals σ profile footprint}
      (child : WorldObsProvenance strata observation) (formed : profile.HasType (.sort relevant)) :
      WorldCertProvenance strata (.observe observation formed)
  | route (path : PrefixRoute sourceEnv U source expression first last)
      (child : WorldCertProvenance strata certificate) : WorldCertProvenance strata (.route path certificate)
  | union (first : WorldCertProvenance strata left) (second : WorldCertProvenance strata right) :
      WorldCertProvenance strata (.union left right)
  | pad (child : WorldCertProvenance strata certificate) : WorldCertProvenance strata (.pad certificate)
  | down (child : WorldCertProvenance strata certificate) : WorldCertProvenance strata (.down certificate)
  | map {certificate : RichCert sourceEnv env U registry target node locals σ relevant profile footprint}
      (view : AtomView env U registry target a b) (child : WorldCertProvenance strata certificate) :
      WorldCertProvenance strata (.map view certificate)
  | support {certificate : RichCert sourceEnv env U registry target node locals σ relevant (profile : Profile n) footprint}
      (action : SupportAction env U registry target n) (child : WorldCertProvenance strata certificate) :
      WorldCertProvenance strata (.support action certificate)
  | select {certificate : RichCert sourceEnv env U registry target node locals σ relevant profile footprint}
      (child : WorldCertProvenance strata certificate) (member : atom ∈ profile.atoms) :
      WorldCertProvenance strata (.select certificate member)  | legacy {node : EndpointState sourceEnv U source expression assigned}
      (certificate : SortableCert env U registry target locals σ expression relevant profile footprint)
      (certificateProvenance : WorldSortableCertProvenance strata certificate) :
      WorldCertProvenance strata (show RichCert sourceEnv env U registry target node locals σ relevant profile footprint from RichCert.legacy certificate)
  | pi {domain : EndpointState sourceEnv U source A (.sort u)}
      {body : EndpointState sourceEnv U (A :: source) B (.sort v)}
      (hu : u.WF U)
      (hv : v.WF U)
      (domainCode : RichCert sourceEnv env U registry target domain locals σ true ambient domainFootprint)
      (guard : PiGuard env U target σ A B prototypeDomain prototypeBody)
      (rows : RichRows sourceEnv env U registry target domain body locals σ relevant ambient values rowFootprint)
      (domainCodeProvenance : WorldCertProvenance strata domainCode)
      (rowsProvenance : WorldRowsProvenance strata rows) :
      WorldCertProvenance strata (show RichCert sourceEnv env U registry target (.pi hu hv domain body) locals σ relevant
        (Profile.pi prototypeDomain prototypeBody ambient values) (domainFootprint ++ rowFootprint) from RichCert.pi hu hv domainCode guard rows)

/-- Provenance for a shared finite recipe. A canonical root belongs to this
exact stratification, and retains its actual queried formation. Structural
eliminations copy the raw row/admission and their indexed binder need. -/
inductive WorldCodeRecipeProvenance (strata : EquationStratification env) :
    {U : Nat} → {registry : CanonicalHead.Registry} → {target : List VExpr} →
    {source : List VExpr} → {locals : List Nat} → {σ : Subst} → {expression : VExpr} →
    {relevant : Bool} → {n : Nat} → {profile : Profile n} → {footprint : Footprint} →
    RichCodeRecipe env U registry target source locals σ expression relevant profile footprint → Type where
  | root (source : List VExpr) (locals : List Nat) (σ : Subst)
      {name : Name} (owner : CanonicalCodeOwner env registry strata name)
      (node : EndpointState owner.selected.origin.source U [] canonicalExpression (.sort level))
      (closed : canonicalExpression.Closed)
      (expressionEq : EqUpToLevels U canonicalExpression expression)
      (realization : Subst)
      (certificate : RichCert owner.selected.origin.source env U registry target node
        [] realization relevant profile footprint)
      (resources : footprint.Available (fun _ => []))
      (child : WorldCertProvenance strata certificate)
      (controls : OriginalWorldControls strata owner.selected.origin.source)
      (provenance : EndpointProvenance (.nil : ContextDerivation owner.selected.origin.source U []) node) :
      WorldCodeRecipeProvenance strata
        (RichCodeRecipe.root source locals σ owner node closed expressionEq realization certificate resources)
  | domain
      {parent : RichCodeRecipe env U registry target source locals σ (.forallE A B)
        relevant (.pi prototypeDomain prototypeBody (support : Profile n) rows) footprint}
      (child : WorldCodeRecipeProvenance strata parent) :
      WorldCodeRecipeProvenance strata (RichCodeRecipe.domain parent)
  | body {σ : Subst}
      {parent : RichCodeRecipe env U registry target source locals σ.tail (.forallE A B)
        relevant (.pi prototypeDomain prototypeBody (support : Profile n) rows) footprint}
      (child : WorldCodeRecipeProvenance strata parent)
      (selected : (key, result) ∈ rows) (anchor : key.anchor = σ 0) :
      WorldCodeRecipeProvenance strata (RichCodeRecipe.body parent selected anchor)
  | fixedBody {B : VExpr}
      {parent : RichCodeRecipe env U registry target source locals σ (.forallE A B.lift)
        relevant (.pi prototypeDomain prototypeBody (support : Profile n) rows) footprint}
      (child : WorldCodeRecipeProvenance strata parent)
      (selected : (key, result) ∈ rows)
      (admitted : Admitted env U registry target key anchor anchor) :
      WorldCodeRecipeProvenance strata (RichCodeRecipe.fixedBody parent selected admitted)
  | resources
      {parent : RichCodeRecipe env U registry target source locals σ expression relevant profile required}
      {transfer : RecipeResourceTransfer env U registry target locals σ required footprint}
      (child : WorldCodeRecipeProvenance strata parent)
      (transferProvenance : WorldRecipeResourceProvenance strata transfer) :
      WorldCodeRecipeProvenance strata (RichCodeRecipe.resources parent transfer)
  | action
      {parent : RichCodeRecipe env U registry target source locals σ expression relevant profile footprint}
      (change : SortableCodeAction env U registry target relevant profile nextRelevant nextProfile)
      (child : WorldCodeRecipeProvenance strata parent) :
      WorldCodeRecipeProvenance strata (RichCodeRecipe.action change parent)

/-- Every finite replacement retains provenance for the exact plain variable
observation it stores. Concatenation follows the transfer's actual entries. -/
inductive WorldRecipeResourceProvenance (strata : EquationStratification env) :
    {U : Nat} → {registry : CanonicalHead.Registry} → {target : List VExpr} →
    {locals : List Nat} → {σ : Subst} → {required footprint : Footprint} →
    RecipeResourceTransfer env U registry target locals σ required footprint → Type where
  | nil : WorldRecipeResourceProvenance strata
      (show RecipeResourceTransfer env U registry target locals σ [] [] from .nil)
  | cons {need : Need}
      {observation : Obs env U registry target locals σ (.bvar index) need.profile queryFootprint}
      {tail : RecipeResourceTransfer env U registry target locals σ needs footprint}
      (head : WorldLegacyObsProvenance strata observation)
      (rest : WorldRecipeResourceProvenance strata tail) :
      WorldRecipeResourceProvenance strata (RecipeResourceTransfer.cons observation tail)

inductive WorldLegacyObsProvenance (strata : EquationStratification env) :
    {U : Nat} → {registry : CanonicalHead.Registry} → {target : List VExpr} →
    {locals : List Nat} → {σ : Subst} → {expression : VExpr} →
    {n : Nat} → {profile : Profile n} → {footprint : Footprint} →
    Obs env U registry target locals σ expression profile footprint → Type where
  | delta {value : VDefVal}
      {name : Name}
      {seedLevels levels : List VLevel}
      (lookup : registry.definitions name = some value)
      (name_eq : value.name = name)
      (registered : DefinitionRegistered env value)
      (seedWF : ∀ level ∈ seedLevels, level.WF U)
      (seedLength : seedLevels.length = value.uvars)
      (levelsWF : ∀ level ∈ levels, level.WF U)
      (equivalent : List.Forall₂ (· ≈ ·) seedLevels levels)
      (bodyClosed : value.value.Closed)
      (typeClosed : value.type.Closed)
      {atom : Atom n}
      {support : Profile n}
      {typeRealization bodyRealization : Subst}
      (certificate : CodeCert env U registry target [] typeRealization
        (value.type.instL seedLevels) support [])
      (typed : (Profile.singleton atom).HasType support)
      (body : Obs env U registry target [] bodyRealization
        (value.value.instL seedLevels) (.singleton atom) [])
      (certificateProvenance : WorldLegacyCertProvenance strata certificate)
      (bodyProvenance : WorldLegacyObsProvenance strata body)
      (origin : EquationHeaderOrigin env value.toDefEq)
      (typeSite : WorldQuerySite (registry := registry) (target := target) strata
        (.ref (.left (EquationHeaderOrigin.instantiatedType origin seedWF))) [] typeRealization)
      (bodySite : WorldQuerySite (registry := registry) (target := target) strata
        (.ref (.left (EquationHeaderOrigin.instantiatedRhs origin seedWF))) [] bodyRealization) :
      WorldLegacyObsProvenance strata (show Obs env U registry target locals σ (.const name levels) (.singleton atom) [] from Obs.delta lookup name_eq registered seedWF seedLength levelsWF equivalent bodyClosed typeClosed certificate typed body)
  | native {data : NativeRecursorData}
      {name : Name}
      {seedLevels levels : List VLevel}
      (lookup : registry.natives name = some data)
      (notDefinition : registry.definitions name = none)
      (name_eq : data.name = name)
      (registered : NativeRecursorRegistered env data)
      (seedWF : ∀ level ∈ seedLevels, level.WF U)
      (levelsWF : ∀ level ∈ levels, level.WF U)
      (equivalent : List.Forall₂ (· ≈ ·) seedLevels levels)
      (signature : NativeConstantSignature data seedLevels)
      (typeClosed : signature.type.Closed)
      {typeSupport : Profile n}
      {typeRealization : Subst}
      (typeCertificate : CodeCert env U registry target [] typeRealization
        (signature.type.instL seedLevels) typeSupport [])
      (typed : demand.HasType typeSupport)
      (tree : NativePlan env U registry target signature [] demand [])
      (typeCertificateProvenance : WorldLegacyCertProvenance strata typeCertificate)
      (treeProvenance : WorldNativePlanProvenance strata tree)
      {info : VConstant}
      (origin : ConstantHeaderOrigin env name info)
      (headerType : info.type = signature.type)
      (headerSite : WorldQuerySite (registry := registry) (target := target) strata
        (.ref (origin.familyHeader seedWF).reference) [] typeRealization) :
      WorldLegacyObsProvenance strata (show Obs env U registry target locals σ (.const name levels) demand [] from Obs.native lookup notDefinition name_eq registered seedWF levelsWF equivalent signature typeClosed typeCertificate typed tree)
  | family {info : VConstant}
      {name : Name}
      {seedLevels levels : List VLevel}
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
      {typeSupport : Profile n}
      {typeRealization : Subst}
      (typeCertificate : CodeCert env U registry target [] typeRealization
        (info.type.instL seedLevels) typeSupport [])
      (typed : demand.HasType typeSupport)
      (tree : FamilyPlan env U registry target name seedLevels signature [] demand [])
      (typeCertificateProvenance : WorldLegacyCertProvenance strata typeCertificate)
      (treeProvenance : WorldLegacyFamilyPlanProvenance strata tree)
      (origin : ConstantHeaderOrigin env name info)
      (headerSite : WorldQuerySite (registry := registry) (target := target) strata
        (.ref (origin.familyHeader seedWF).reference) [] typeRealization) :
      WorldLegacyObsProvenance strata (show Obs env U registry target locals σ (.const name levels) demand [] from Obs.family lookup notDefinition notNative notQuotient seedWF seedLength levelsWF equivalent signature typeClosed typeCertificate typed tree)
  | constructor {info : VConstant}
      {name : Name}
      {seedLevels levels : List VLevel}
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
      {typeSupport : Profile n}
      {typeRealization : Subst}
      (typeCertificate : CodeCert env U registry target [] typeRealization
        (info.type.instL seedLevels) typeSupport [])
      (typed : demand.HasType typeSupport)
      (tree : ConstructorPlan env U registry target name seedLevels signature [] demand [])
      (typeCertificateProvenance : WorldLegacyCertProvenance strata typeCertificate)
      (treeProvenance : WorldLegacyConstructorPlanProvenance strata tree)
      (origin : ConstantHeaderOrigin env name info)
      (headerSite : WorldQuerySite (registry := registry) (target := target) strata
        (.ref (origin.familyHeader seedWF).reference) [] typeRealization) :
      WorldLegacyObsProvenance strata (show Obs env U registry target locals σ (.const name levels) demand [] from Obs.constructor lookup notDefinition notNative notQuotient seedWF seedLength levelsWF equivalent signature typeClosed typeCertificate typed tree)
  | var (locals : List Nat)
      (σ : Subst)
      (i : Nat)
      (demand : Profile n) :
      WorldLegacyObsProvenance strata (show Obs env U registry target locals σ (.bvar i) demand [(i, ⟨n, demand⟩)] from Obs.var locals σ i demand)
  | empty  :
      WorldLegacyObsProvenance strata (show Obs env U registry target locals σ expression (n := n) .empty [] from Obs.empty )
  | sort (relevant : Relevant level flag) :
      WorldLegacyObsProvenance strata (show Obs env U registry target locals σ (.sort level) (.sort (n := n) flag) [] from Obs.sort relevant)
  | app {key : Key n}
      {output : Atom n}
      (fn : Obs env U registry target locals σ f (Profile.fn key output) fnFootprint)
      (arg : Obs env U registry target locals σ a rawInput argFootprint)
      (arguments : NormalProfileAdapter env U registry target rawInput key.input)
      (admitted : Admitted env U registry target key (a.subst σ) (a.subst σ))
      (fnProvenance : WorldLegacyObsProvenance strata fn)
      (argProvenance : WorldLegacyObsProvenance strata arg) :
      WorldLegacyObsProvenance strata (show Obs env U registry target locals σ (.app f a) (.singleton output)
        (fnFootprint ++ argFootprint) from Obs.app fn arg arguments admitted)
  | lam {key : Key n}
      {output : Atom n}
      {support packed : Profile n}
      (domain : CodeCert env U registry target locals σ annotation support domainFootprint)
      (guard : LambdaGuard env U registry target σ annotation key support)
      (body : Obs env U registry target (Locals.push locals) (σ.cons key.anchor) expression
        (.singleton output) bodyFootprint)
      (normal : BinderPack n packed bodyFootprint externalFootprint)
      (covered : ∀ atom ∈ packed.atoms, atom ∈ key.input.atoms)
      (domainProvenance : WorldLegacyCertProvenance strata domain)
      (bodyProvenance : WorldLegacyObsProvenance strata body) :
      WorldLegacyObsProvenance strata (show Obs env U registry target locals σ (.lam annotation expression) (Profile.fn key output)
        (domainFootprint ++ externalFootprint) from Obs.lam domain guard body normal covered)
  | pi {ambient : Profile n}
      {rows : List (Key n × Profile n)}
      {prototypeDomain prototypeBody : VExpr}
      (domain : CodeCert env U registry target locals σ A ambient domainFootprint)
      (guard : PiGuard env U target σ A B prototypeDomain prototypeBody)
      (bodies : PiRows env U registry target locals σ A B ambient rows rowFootprint)
      (domainProvenance : WorldLegacyCertProvenance strata domain)
      (bodiesProvenance : WorldLegacyRowsProvenance strata bodies) :
      WorldLegacyObsProvenance strata (show Obs env U registry target locals σ (.forallE A B)
        (Profile.pi prototypeDomain prototypeBody ambient rows)
        (domainFootprint ++ rowFootprint) from Obs.pi domain guard bodies)
  | union (left : Obs env U registry target locals σ expression leftDemand leftFootprint)
      (right : Obs env U registry target locals σ expression rightDemand rightFootprint)
      (leftProvenance : WorldLegacyObsProvenance strata left)
      (rightProvenance : WorldLegacyObsProvenance strata right) :
      WorldLegacyObsProvenance strata (show Obs env U registry target locals σ expression (leftDemand.union rightDemand)
        (leftFootprint ++ rightFootprint) from Obs.union left right)
  | view (source : Obs env U registry target locals σ expression (.singleton oldAtom) footprint)
      (view : AtomView env U registry target oldAtom newAtom)
      (sourceProvenance : WorldLegacyObsProvenance strata source) :
      WorldLegacyObsProvenance strata (show Obs env U registry target locals σ expression (.singleton newAtom) footprint from Obs.view source view)
  | pad (source : Obs env U registry target locals σ expression demand footprint)
      (sourceProvenance : WorldLegacyObsProvenance strata source) :
      WorldLegacyObsProvenance strata (show Obs env U registry target locals σ expression demand.pad footprint from Obs.pad source)
  | unpad (source : Obs env U registry target locals σ expression demand.pad footprint)
      (sourceProvenance : WorldLegacyObsProvenance strata source) :
      WorldLegacyObsProvenance strata (show Obs env U registry target locals σ expression demand footprint from Obs.unpad source)
  | rowShift (source : Obs env U registry target locals σ expression (Profile.fn key output) footprint)
      (sourceProvenance : WorldLegacyObsProvenance strata source) :
      WorldLegacyObsProvenance strata (show Obs env U registry target locals σ expression (Profile.fn key.pad (.pad output)) footprint from Obs.rowShift source)

inductive WorldLegacyCertProvenance (strata : EquationStratification env) :
    {U : Nat} → {registry : CanonicalHead.Registry} → {target : List VExpr} →
    {locals : List Nat} → {σ : Subst} → {expression : VExpr} →
    {n : Nat} → {profile : Profile n} → {footprint : Footprint} →
    CodeCert env U registry target locals σ expression profile footprint → Type where
  | seed (observation : Obs env U registry target locals σ expression profile footprint)
      (formed : profile.HasType (.sort true))
      (observationProvenance : WorldLegacyObsProvenance strata observation) :
      WorldLegacyCertProvenance strata (show CodeCert env U registry target locals σ expression profile footprint from CodeCert.seed observation formed)
  | union (left : CodeCert env U registry target locals σ expression leftDemand leftFootprint)
      (right : CodeCert env U registry target locals σ expression rightDemand rightFootprint)
      (leftProvenance : WorldLegacyCertProvenance strata left)
      (rightProvenance : WorldLegacyCertProvenance strata right) :
      WorldLegacyCertProvenance strata (show CodeCert env U registry target locals σ expression (leftDemand.union rightDemand)
        (leftFootprint ++ rightFootprint) from CodeCert.union left right)
  | pad (source : CodeCert env U registry target locals σ expression profile footprint)
      (sourceProvenance : WorldLegacyCertProvenance strata source) :
      WorldLegacyCertProvenance strata (show CodeCert env U registry target locals σ expression profile.pad footprint from CodeCert.pad source)
  | familyPad {family : FamilyData (Profile n)}
      (source : CodeCert env U registry target locals σ expression
        (Profile.singleton (n := n + 1) (.family family)) footprint)
      (sourceProvenance : WorldLegacyCertProvenance strata source) :
      WorldLegacyCertProvenance strata (show CodeCert env U registry target locals σ expression
        (Profile.singleton (n := n + 2) (.family (family.map id Profile.pad))) footprint from CodeCert.familyPad source)
  | unpad (source : CodeCert env U registry target locals σ expression profile.pad footprint)
      (sourceProvenance : WorldLegacyCertProvenance strata source) :
      WorldLegacyCertProvenance strata (show CodeCert env U registry target locals σ expression profile footprint from CodeCert.unpad source)
  | down {profile : Profile (n + 1)}
      (source : CodeCert env U registry target locals σ expression profile footprint)
      (sourceProvenance : WorldLegacyCertProvenance strata source) :
      WorldLegacyCertProvenance strata (show CodeCert env U registry target locals σ expression profile.down footprint from CodeCert.down source)
  | map {a b : Atom n}
      (view : AtomView env U registry target a b)
      (source : CodeCert env U registry target locals σ expression profile footprint)
      (sourceProvenance : WorldLegacyCertProvenance strata source) :
      WorldLegacyCertProvenance strata (show CodeCert env U registry target locals σ expression (view.mapType profile) footprint from CodeCert.map view source)
  | select {profile : Profile n}
      {atom : Atom n}
      (source : CodeCert env U registry target locals σ expression profile footprint)
      (member : atom ∈ profile.atoms)
      (sourceProvenance : WorldLegacyCertProvenance strata source) :
      WorldLegacyCertProvenance strata (show CodeCert env U registry target locals σ expression (.singleton atom) footprint from CodeCert.select source member)
  | focusMinimal {value focused : Profile n}
      (source : CodeCert env U registry target locals σ expression support footprint)
      (minimal : Minimal value focused)
      (bound : focused ≤ support)
      (sourceProvenance : WorldLegacyCertProvenance strata source) :
      WorldLegacyCertProvenance strata (show CodeCert env U registry target locals σ expression focused footprint from CodeCert.focusMinimal source minimal bound)

inductive WorldLegacyRowsProvenance (strata : EquationStratification env) :
    {U : Nat} → {registry : CanonicalHead.Registry} → {target : List VExpr} →
    {locals : List Nat} → {σ : Subst} → {A B : VExpr} → 
    {n : Nat} → {ambient : Profile n} → {rows : List (Key n × Profile n)} → {footprint : Footprint} →
    PiRows env U registry target locals σ A B ambient rows footprint → Type where
  | nil  :
      WorldLegacyRowsProvenance strata (show PiRows env U registry target locals σ A B ambient [] [] from PiRows.nil )
  | cons {key : Key n}
      {output packed ambient : Profile n}
      (guard : LambdaGuard env U registry target σ A key ambient)
      (body : CodeCert env U registry target (Locals.push locals) (σ.cons key.anchor)
        B output bodyFootprint)
      (normal : BinderPack n packed bodyFootprint externalFootprint)
      (covered : ∀ atom ∈ packed.atoms, atom ∈ key.input.atoms)
      (tail : PiRows env U registry target locals σ A B ambient rows tailFootprint)
      (bodyProvenance : WorldLegacyCertProvenance strata body)
      (tailProvenance : WorldLegacyRowsProvenance strata tail) :
      WorldLegacyRowsProvenance strata (show PiRows env U registry target locals σ A B ambient ((key, output) :: rows)
        (externalFootprint ++ tailFootprint) from PiRows.cons guard body normal covered tail)

inductive WorldNativeCapturesProvenance (strata : EquationStratification env) :
    {U : Nat} → {registry : CanonicalHead.Registry} → {target : List VExpr} →
    {data : NativeRecursorData} → {program : SaturatedProgram data} →
    {witnesses : List VExpr} → {count : Nat} → {required footprint : Footprint} →
    NativeCaptures env U registry target program witnesses count required footprint → Type where
  | prefix {data : NativeRecursorData}
      {program : SaturatedProgram data}
      {witnesses : List VExpr}
      (required : Footprint) :
      WorldNativeCapturesProvenance strata (show NativeCaptures env U registry target program witnesses 0 required
        (Footprint.sourceLift (.skipN .refl (program.prefixArgs.length - data.indexOffset)) required) from NativeCaptures.prefix required)
  | index {data : NativeRecursorData}
      {program : SaturatedProgram data}
      {witnesses : List VExpr}
      {templates : NativeIndexTemplates program}
      {naturalAvailable captureAvailable : Valuation}
      {input packed : Profile n}
      {required outside previousNative : Footprint}
      {value : VExpr}
      {naturalSupport declaredSupport : Profile n}
      {naturalFootprint declaredFootprint : Footprint}
      (naturalCertificate : CodeCert env U registry target
        (List.range (data.indexOffset + templates.slot))
        (nativeCaptureSubst (program.prefixArgs.take (data.indexOffset + templates.slot)))
        templates.naturalDomain naturalSupport naturalFootprint)
      (naturalResources : naturalFootprint.Available naturalAvailable)
      (declaredCertificate : CodeCert env U registry target
        (List.range (data.indexOffset + templates.field))
        (nativeCaptureSubst (witnesses.take (data.indexOffset + templates.field)))
        templates.declaredDomain declaredSupport declaredFootprint)
      (declaredResources : declaredFootprint.Available captureAvailable)
      (naturalTyped : input.HasType naturalSupport)
      (declaredTyped : input.HasType declaredSupport)
      (alignment : DomainChain env U registry target input
        (templates.naturalDomain.subst (nativeCaptureSubst
          (program.prefixArgs.take (data.indexOffset + templates.slot))))
        (templates.declaredDomain.subst (nativeCaptureSubst
          (witnesses.take (data.indexOffset + templates.field)))))
      (declaredCode : TypeRelated env U registry target
        (templates.declaredDomain.subst (nativeCaptureSubst
          (witnesses.take (data.indexOffset + templates.field))))
        (templates.declaredDomain.subst (nativeCaptureSubst
          (witnesses.take (data.indexOffset + templates.field)))) declaredSupport)
      (nativeValue : program.prefixArgs[data.indexOffset + templates.slot]? = some value)
      (copiedValue : witnesses[data.indexOffset + templates.field]? = some value)
      (pack : BinderPack n packed required outside)
      (covered : ∀ atom ∈ packed.atoms, atom ∈ input.atoms)
      (previous : NativeCaptures env U registry target program witnesses templates.field
        (declaredFootprint ++ outside) previousNative)
      (naturalCertificateProvenance : WorldLegacyCertProvenance strata naturalCertificate)
      (declaredCertificateProvenance : WorldLegacyCertProvenance strata declaredCertificate)
      (previousProvenance : WorldNativeCapturesProvenance strata previous) :
      WorldNativeCapturesProvenance strata (show NativeCaptures env U registry target program witnesses (templates.field + 1) required
        (previousNative ++
          Footprint.sourceLift (.skipN .refl
            (program.prefixArgs.length - (data.indexOffset + templates.slot)))
            naturalFootprint ++
          [(program.prefixArgs.length - 1 - (data.indexOffset + templates.slot), ⟨n, input⟩)]) from NativeCaptures.index naturalCertificate naturalResources declaredCertificate declaredResources naturalTyped declaredTyped alignment declaredCode nativeValue copiedValue pack covered previous)
  | proof {data : NativeRecursorData}
      {program : SaturatedProgram data}
      {witnesses : List VExpr}
      {field : Nat}
      {domain witness : VExpr}
      {required outside native : Footprint}
      (instruction : program.instructions[field]? = some (.proof domain))
      (captured : witnesses[data.indexOffset + field]? = some witness)
      (sourceProof : env.HasType U
        (((program.equationBody.domains.take (data.indexOffset + field)).map
          (·.instL program.levels)).reverse) domain (.sort .zero))
      (domainProof : env.HasType U target
        (domain.subst (nativeCaptureSubst (witnesses.take (data.indexOffset + field)))) (.sort .zero))
      (inhabitant : env.HasType U target witness
        (domain.subst (nativeCaptureSubst (witnesses.take (data.indexOffset + field)))))
      (pack : BinderPack n (.empty : Profile n) required outside)
      (previous : NativeCaptures env U registry target program witnesses field outside native)
      (previousProvenance : WorldNativeCapturesProvenance strata previous) :
      WorldNativeCapturesProvenance strata (show NativeCaptures env U registry target program witnesses (field + 1) required native from NativeCaptures.proof instruction captured sourceProof domainProof inhabitant pack previous)

inductive WorldNativePlanProvenance (strata : EquationStratification env) :
    {U : Nat} → {registry : CanonicalHead.Registry} → {target : List VExpr} →
    {data : NativeRecursorData} → {levels : List VLevel} →
    {signature : NativeConstantSignature data levels} → {arguments : List VExpr} →
    {n : Nat} → {profile : Profile n} → {footprint : Footprint} →
    NativePlan env U registry target signature arguments profile footprint → Type where
  | terminal {data : NativeRecursorData}
      {levels : List VLevel}
      {signature : NativeConstantSignature data levels}
      {arguments : List VExpr}
      {demand : Profile n}
      {nativeFootprint : Footprint}
      (program : SaturatedProgram data)
      (selected : data.saturatedProgram levels arguments = some program)
      (lhsClosed : program.equation.lhs.Closed)
      (rhsClosed : program.equation.rhs.Closed)
      (saturated : arguments.length = data.majorOffset + 1)
      (noTrailing : program.trailing = [])
      (prefix_eq : program.prefixArgs = arguments)
      (witnesses : List VExpr)
      (witnessLength : witnesses.length = program.equationBody.domains.length)
      (witnessPrefix : witnesses.take data.indexOffset = arguments.take data.indexOffset)
      (argumentAlignment : Ctx.SubstEq env U target
        (nativeCaptureSubst arguments)
        (nativeCaptureSubst (nativeEquationArguments program witnesses)) signature.domains.reverse)
      (arguments_eq : arguments = nativeEquationArguments program witnesses)
      {bodyFootprint : Footprint}
      (body : Obs env U registry target (List.range program.equationBody.domains.length)
        (nativeCaptureSubst witnesses) (program.equationBody.rhs.instL levels) demand bodyFootprint)
      (captures : NativeCaptures env U registry target program witnesses
        program.instructions.length bodyFootprint nativeFootprint)
      (bodyProvenance : WorldLegacyObsProvenance strata body)
      (capturesProvenance : WorldNativeCapturesProvenance strata captures)
      (origin : EquationHeaderOrigin env program.equation)
      (levelsWF : ∀ level ∈ levels, level.WF U)
      (equationSite : WorldQuerySite (registry := registry) (target := target) strata
        (.ref (.left (EquationHeaderOrigin.instantiatedRhs origin levelsWF))) [] (nativeCaptureSubst [])) :
      WorldNativePlanProvenance strata (show NativePlan env U registry target signature arguments demand nativeFootprint from NativePlan.terminal program selected lhsClosed rhsClosed saturated noTrailing prefix_eq witnesses witnessLength witnessPrefix argumentAlignment arguments_eq body captures)
  | binder {data : NativeRecursorData}
      {levels : List VLevel}
      {signature : NativeConstantSignature data levels}
      {arguments : List VExpr}
      {domain : VExpr}
      {key : Key n}
      {output : Atom n}
      {support packed : Profile n}
      {domainFootprint bodyFootprint outside : Footprint}
      (domainOrigin : signature.domains[arguments.length]? = some domain)
      (domainCode : CodeCert env U registry target (List.range arguments.length)
        (nativeCaptureSubst arguments) domain support domainFootprint)
      (guard : LambdaGuard env U registry target (nativeCaptureSubst arguments) domain key support)
      (body : NativePlan env U registry target signature (arguments ++ [key.anchor])
        (.singleton output) bodyFootprint)
      (pack : BinderPack n packed bodyFootprint outside)
      (covered : ∀ atom ∈ packed.atoms, atom ∈ key.input.atoms)
      (domainCodeProvenance : WorldLegacyCertProvenance strata domainCode)
      (bodyProvenance : WorldNativePlanProvenance strata body) :
      WorldNativePlanProvenance strata (show NativePlan env U registry target signature arguments (Profile.fn key output)
        (domainFootprint ++ outside) from NativePlan.binder domainOrigin domainCode guard body pack covered)

inductive WorldFamilyCapturesProvenance (strata : EquationStratification env) :
    {U : Nat} → {registry : CanonicalHead.Registry} → {target : List VExpr} →
    {source : List VExpr} → {locals : List Nat} → {σ : Subst} → {n : Nat} →
    {expressions : List VExpr} → {keys : List (DataRequest (Profile n))} → {footprint : Footprint} →
    FamilyCaptures env U registry target source locals σ expressions keys footprint → Type where
  | nil  :
      WorldFamilyCapturesProvenance strata (show FamilyCaptures env U registry target source locals σ (n := n) [] [] [] from FamilyCaptures.nil )
  | cons {key : DataRequest (Profile n)}
      {index : Nat}
      {A : VExpr}
      {rawInput : Profile n}
      (lookup : Lookup source index A)
      (value : Obs env U registry target locals σ (.bvar index) rawInput valueFootprint)
      (adapter : NormalProfileAdapter env U registry target rawInput key.input)
      (alignment : DomainChain env U registry target key.input key.domain (A.subst σ))
      (anchor : RankedData.RequestAdmission env U (relations env U registry n) target key (σ index) (σ index))
      (tail : FamilyCaptures env U registry target source locals σ expressions keys tailFootprint)
      (valueProvenance : WorldLegacyObsProvenance strata value)
      (tailProvenance : WorldFamilyCapturesProvenance strata tail) :
      WorldFamilyCapturesProvenance strata (show FamilyCaptures env U registry target source locals σ (.bvar index :: expressions) (key :: keys)
        (valueFootprint ++ tailFootprint) from FamilyCaptures.cons lookup value adapter alignment anchor tail)

inductive WorldLegacyFamilyPlanProvenance (strata : EquationStratification env) :
    {U : Nat} → {registry : CanonicalHead.Registry} → {target : List VExpr} →
    {name : Name} → {levels : List VLevel} → {declaredType : VExpr} →
    {signature : ConstantTelescope declaredType} → {arguments : List VExpr} →
    {n : Nat} → {profile : Profile n} → {footprint : Footprint} →
    FamilyPlan env U registry target name levels signature arguments profile footprint → Type where
  | terminal {name : Name}
      {levels : List VLevel}
      {declaredType : VExpr}
      {signature : ConstantTelescope declaredType}
      {arguments : List VExpr}
      {keys : List (DataRequest (Profile n))}
      (saturated : arguments.length = signature.domains.length)
      (resultSort : signature.result = .sort level)
      (relevance : Relevant level relevant)
      (captures : FamilyCaptures env U registry target signature.domains.reverse (List.range arguments.length)
        (nativeCaptureSubst arguments) (constantCaptureVariables arguments.length) keys footprint)
      (capturesProvenance : WorldFamilyCapturesProvenance strata captures) :
      WorldLegacyFamilyPlanProvenance strata (show FamilyPlan env U registry target name levels signature arguments
        (n := n + 1) (.singleton (.family ⟨name, levels, relevant, keys⟩)) footprint from FamilyPlan.terminal saturated resultSort relevance captures)
  | binder {name : Name}
      {levels : List VLevel}
      {declaredType : VExpr}
      {signature : ConstantTelescope declaredType}
      {arguments : List VExpr}
      {domain : VExpr}
      {key : Key n}
      {output : Atom n}
      {support packed : Profile n}
      (domainOrigin : signature.domains[arguments.length]? = some domain)
      (domainCode : CodeCert env U registry target (List.range arguments.length)
        (nativeCaptureSubst arguments) domain support domainFootprint)
      (guard : LambdaGuard env U registry target (nativeCaptureSubst arguments) domain key support)
      (body : FamilyPlan env U registry target name levels signature (arguments ++ [key.anchor])
        (.singleton output) bodyFootprint)
      (pack : BinderPack n packed bodyFootprint outside)
      (covered : ∀ atom ∈ packed.atoms, atom ∈ key.input.atoms)
      (domainCodeProvenance : WorldLegacyCertProvenance strata domainCode)
      (bodyProvenance : WorldLegacyFamilyPlanProvenance strata body) :
      WorldLegacyFamilyPlanProvenance strata (show FamilyPlan env U registry target name levels signature arguments (Profile.fn key output)
        (domainFootprint ++ outside) from FamilyPlan.binder domainOrigin domainCode guard body pack covered)
  | view {name : Name}
      {levels : List VLevel}
      {declaredType : VExpr}
      {signature : ConstantTelescope declaredType}
      (source : FamilyPlan env U registry target name levels signature arguments
        (.singleton oldAtom) footprint)
      (view : AtomView env U registry target oldAtom newAtom)
      (sourceProvenance : WorldLegacyFamilyPlanProvenance strata source) :
      WorldLegacyFamilyPlanProvenance strata (show FamilyPlan env U registry target name levels signature arguments (.singleton newAtom) footprint from FamilyPlan.view source view)
  | pad {name : Name}
      {levels : List VLevel}
      {declaredType : VExpr}
      {signature : ConstantTelescope declaredType}
      (source : FamilyPlan env U registry target name levels signature arguments demand footprint)
      (sourceProvenance : WorldLegacyFamilyPlanProvenance strata source) :
      WorldLegacyFamilyPlanProvenance strata (show FamilyPlan env U registry target name levels signature arguments demand.pad footprint from FamilyPlan.pad source)

inductive WorldLegacyConstructorPlanProvenance (strata : EquationStratification env) :
    {U : Nat} → {registry : CanonicalHead.Registry} → {target : List VExpr} →
    {name : Name} → {levels : List VLevel} → {declaredType : VExpr} →
    {signature : ConstantTelescope declaredType} → {arguments : List VExpr} →
    {n : Nat} → {profile : Profile n} → {footprint : Footprint} →
    ConstructorPlan env U registry target name levels signature arguments profile footprint → Type where
  | terminal {name : Name}
      {levels : List VLevel}
      {declaredType : VExpr}
      {signature : ConstantTelescope declaredType}
      {arguments : List VExpr}
      {family : FamilyData (Profile n)}
      {keys : List (DataRequest (Profile n))}
      {familyLevels : List VLevel}
      {familyArguments : List VExpr}
      (saturated : arguments.length = signature.domains.length)
      (resultShape : signature.result = mkApps (.const family.name familyLevels) familyArguments)
      (relevant : family.relevant = true)
      (captures : FamilyCaptures env U registry target signature.domains.reverse (List.range arguments.length)
        (nativeCaptureSubst arguments) (constantCaptureVariables arguments.length) keys captureFootprint)
      (resultCode : CodeCert env U registry target (List.range arguments.length)
        (nativeCaptureSubst arguments) signature.result
        (Profile.singleton (n := n + 1) (.family family)) resultFootprint)
      (capturesProvenance : WorldFamilyCapturesProvenance strata captures)
      (resultCodeProvenance : WorldLegacyCertProvenance strata resultCode) :
      WorldLegacyConstructorPlanProvenance strata (show ConstructorPlan env U registry target name levels signature arguments
        (n := n + 1) (.singleton (.ctor ⟨name, levels, keys, family, relevant⟩))
        (captureFootprint ++ resultFootprint) from ConstructorPlan.terminal saturated resultShape relevant captures resultCode)
  | binder {name : Name}
      {levels : List VLevel}
      {declaredType : VExpr}
      {signature : ConstantTelescope declaredType}
      {arguments : List VExpr}
      {domain : VExpr}
      {key : Key n}
      {output : Atom n}
      {support packed : Profile n}
      (domainOrigin : signature.domains[arguments.length]? = some domain)
      (domainCode : CodeCert env U registry target (List.range arguments.length)
        (nativeCaptureSubst arguments) domain support domainFootprint)
      (guard : LambdaGuard env U registry target (nativeCaptureSubst arguments) domain key support)
      (body : ConstructorPlan env U registry target name levels signature (arguments ++ [key.anchor])
        (.singleton output) bodyFootprint)
      (pack : BinderPack n packed bodyFootprint outside)
      (covered : ∀ atom ∈ packed.atoms, atom ∈ key.input.atoms)
      (domainCodeProvenance : WorldLegacyCertProvenance strata domainCode)
      (bodyProvenance : WorldLegacyConstructorPlanProvenance strata body) :
      WorldLegacyConstructorPlanProvenance strata (show ConstructorPlan env U registry target name levels signature arguments (Profile.fn key output)
        (domainFootprint ++ outside) from ConstructorPlan.binder domainOrigin domainCode guard body pack covered)
  | view {name : Name}
      {levels : List VLevel}
      {declaredType : VExpr}
      {signature : ConstantTelescope declaredType}
      (source : ConstructorPlan env U registry target name levels signature arguments
        (.singleton oldAtom) footprint)
      (view : AtomView env U registry target oldAtom newAtom)
      (sourceProvenance : WorldLegacyConstructorPlanProvenance strata source) :
      WorldLegacyConstructorPlanProvenance strata (show ConstructorPlan env U registry target name levels signature arguments (.singleton newAtom) footprint from ConstructorPlan.view source view)
  | pad {name : Name}
      {levels : List VLevel}
      {declaredType : VExpr}
      {signature : ConstantTelescope declaredType}
      (source : ConstructorPlan env U registry target name levels signature arguments demand footprint)
      (sourceProvenance : WorldLegacyConstructorPlanProvenance strata source) :
      WorldLegacyConstructorPlanProvenance strata (show ConstructorPlan env U registry target name levels signature arguments demand.pad footprint from ConstructorPlan.pad source)

inductive WorldSortableObsProvenance (strata : EquationStratification env) :
    {U : Nat} → {registry : CanonicalHead.Registry} → {target : List VExpr} →
    {locals : List Nat} → {σ : Subst} → {expression : VExpr} →
    {n : Nat} → {profile : Profile n} → {footprint : Footprint} →
    SortableObs env U registry target locals σ expression profile footprint → Type where
  | family {info : VConstant}
      {name : Name}
      {seedLevels levels : List VLevel}
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
      {typeSupport : Profile n}
      {typeRealization : Subst}
      (typeCertificate : SortableCert env U registry target [] typeRealization
        (info.type.instL seedLevels) true typeSupport [])
      (typed : demand.HasType typeSupport)
      (tree : SortableFamilyPlan env U registry target name seedLevels signature [] demand [])
      (typeCertificateProvenance : WorldSortableCertProvenance strata typeCertificate)
      (treeProvenance : WorldSortableFamilyPlanProvenance strata tree)
      (origin : ConstantHeaderOrigin env name info)
      (headerSite : WorldQuerySite (registry := registry) (target := target) strata
        (.ref (origin.familyHeader seedWF).reference) [] typeRealization) :
      WorldSortableObsProvenance strata (show SortableObs env U registry target locals σ (.const name levels) demand [] from SortableObs.family lookup notDefinition notNative notQuotient seedWF seedLength levelsWF equivalent signature typeClosed typeCertificate typed tree)
  | legacy (observation : Obs env U registry target locals σ expression demand footprint)
      (observationProvenance : WorldLegacyObsProvenance strata observation) :
      WorldSortableObsProvenance strata (show SortableObs env U registry target locals σ expression demand footprint from SortableObs.legacy observation)
  | code (relevant : Bool)
      (certificate : SortableCert env U registry target locals σ expression relevant demand footprint)
      (certificateProvenance : WorldSortableCertProvenance strata certificate) :
      WorldSortableObsProvenance strata (show SortableObs env U registry target locals σ expression demand footprint from SortableObs.code relevant certificate)
  | app {key : Key n}
      {output : Atom n}
      (fn : SortableObs env U registry target locals σ f (Profile.fn key output) fnFootprint)
      (arg : SortableObs env U registry target locals σ a rawInput argFootprint)
      (arguments : GeneralNormalProfileAdapter env U registry target rawInput key.input)
      (admitted : Admitted env U registry target key (a.subst σ) (a.subst σ))
      (fnProvenance : WorldSortableObsProvenance strata fn)
      (argProvenance : WorldSortableObsProvenance strata arg) :
      WorldSortableObsProvenance strata (show SortableObs env U registry target locals σ (.app f a) (.singleton output)
        (fnFootprint ++ argFootprint) from SortableObs.app fn arg arguments admitted)
  | lam {key : Key n}
      {output : Atom n}
      {support packed : Profile n}
      (domain : SortableCert env U registry target locals σ annotation true support domainFootprint)
      (guard : LambdaGuard env U registry target σ annotation key support)
      (body : SortableObs env U registry target (Locals.push locals) (σ.cons key.anchor) expression
        (.singleton output) bodyFootprint)
      (normal : BinderPack n packed bodyFootprint externalFootprint)
      (covered : ∀ atom ∈ packed.atoms, atom ∈ key.input.atoms)
      (domainProvenance : WorldSortableCertProvenance strata domain)
      (bodyProvenance : WorldSortableObsProvenance strata body) :
      WorldSortableObsProvenance strata (show SortableObs env U registry target locals σ (.lam annotation expression) (Profile.fn key output)
        (domainFootprint ++ externalFootprint) from SortableObs.lam domain guard body normal covered)
  | union (left : SortableObs env U registry target locals σ expression leftDemand leftFootprint)
      (right : SortableObs env U registry target locals σ expression rightDemand rightFootprint)
      (leftProvenance : WorldSortableObsProvenance strata left)
      (rightProvenance : WorldSortableObsProvenance strata right) :
      WorldSortableObsProvenance strata (show SortableObs env U registry target locals σ expression (leftDemand.union rightDemand)
        (leftFootprint ++ rightFootprint) from SortableObs.union left right)
  | view (source : SortableObs env U registry target locals σ expression (.singleton oldAtom) footprint)
      (view : AtomView env U registry target oldAtom newAtom)
      (sourceProvenance : WorldSortableObsProvenance strata source) :
      WorldSortableObsProvenance strata (show SortableObs env U registry target locals σ expression (.singleton newAtom) footprint from SortableObs.view source view)
  | action (source : SortableObs env U registry target locals σ expression (.singleton oldAtom) footprint)
      (action : AtomAction env U registry target oldAtom newAtom)
      (sourceProvenance : WorldSortableObsProvenance strata source) :
      WorldSortableObsProvenance strata (show SortableObs env U registry target locals σ expression (.singleton newAtom) footprint from SortableObs.action source action)
  | pad (source : SortableObs env U registry target locals σ expression demand footprint)
      (sourceProvenance : WorldSortableObsProvenance strata source) :
      WorldSortableObsProvenance strata (show SortableObs env U registry target locals σ expression demand.pad footprint from SortableObs.pad source)
  | unpad (source : SortableObs env U registry target locals σ expression demand.pad footprint)
      (sourceProvenance : WorldSortableObsProvenance strata source) :
      WorldSortableObsProvenance strata (show SortableObs env U registry target locals σ expression demand footprint from SortableObs.unpad source)
  | rowShift (source : SortableObs env U registry target locals σ expression (Profile.fn key output) footprint)
      (sourceProvenance : WorldSortableObsProvenance strata source) :
      WorldSortableObsProvenance strata (show SortableObs env U registry target locals σ expression (Profile.fn key.pad (.pad output)) footprint from SortableObs.rowShift source)

inductive WorldSortableCertProvenance (strata : EquationStratification env) :
    {U : Nat} → {registry : CanonicalHead.Registry} → {target : List VExpr} →
    {locals : List Nat} → {σ : Subst} → {expression : VExpr} → {relevant : Bool} →
    {n : Nat} → {profile : Profile n} → {footprint : Footprint} →
    SortableCert env U registry target locals σ expression relevant profile footprint → Type where
  | ofCode (source : CodeCert env U registry target locals σ expression profile footprint)
      (formed : profile.HasType (.sort relevant))
      (sourceProvenance : WorldLegacyCertProvenance strata source) :
      WorldSortableCertProvenance strata (show SortableCert env U registry target locals σ expression relevant profile footprint from SortableCert.ofCode source formed)
  | pi {ambient : Profile n}
      {rows : List (Key n × Profile n)}
      {prototypeDomain prototypeBody : VExpr}
      (domain : SortableCert env U registry target locals σ A true ambient domainFootprint)
      (guard : PiGuard env U target σ A B prototypeDomain prototypeBody)
      (bodies : SortableRows env U registry target locals σ A B relevant ambient rows rowFootprint)
      (domainProvenance : WorldSortableCertProvenance strata domain)
      (bodiesProvenance : WorldSortableRowsProvenance strata bodies) :
      WorldSortableCertProvenance strata (show SortableCert env U registry target locals σ (.forallE A B) relevant
        (Profile.pi prototypeDomain prototypeBody ambient rows)
        (domainFootprint ++ rowFootprint) from SortableCert.pi domain guard bodies)
  | observe (observation : SortableObs env U registry target locals σ expression profile footprint)
      (formed : profile.HasType (.sort relevant))
      (observationProvenance : WorldSortableObsProvenance strata observation) :
      WorldSortableCertProvenance strata (show SortableCert env U registry target locals σ expression relevant profile footprint from SortableCert.observe observation formed)
  | seed (observation : Obs env U registry target locals σ expression profile footprint)
      (formed : profile.HasType (.sort relevant))
      (observationProvenance : WorldLegacyObsProvenance strata observation) :
      WorldSortableCertProvenance strata (show SortableCert env U registry target locals σ expression relevant profile footprint from SortableCert.seed observation formed)
  | union (left : SortableCert env U registry target locals σ expression relevant leftDemand leftFootprint)
      (right : SortableCert env U registry target locals σ expression relevant rightDemand rightFootprint)
      (leftProvenance : WorldSortableCertProvenance strata left)
      (rightProvenance : WorldSortableCertProvenance strata right) :
      WorldSortableCertProvenance strata (show SortableCert env U registry target locals σ expression relevant (leftDemand.union rightDemand)
        (leftFootprint ++ rightFootprint) from SortableCert.union left right)
  | pad (source : SortableCert env U registry target locals σ expression relevant profile footprint)
      (sourceProvenance : WorldSortableCertProvenance strata source) :
      WorldSortableCertProvenance strata (show SortableCert env U registry target locals σ expression relevant profile.pad footprint from SortableCert.pad source)
  | sortPad (source : SortableCert env U registry target locals σ expression relevant
        (Profile.sort (n := n) flag) footprint)
      (sourceProvenance : WorldSortableCertProvenance strata source) :
      WorldSortableCertProvenance strata (show SortableCert env U registry target locals σ expression relevant
        (Profile.sort (n := n + 1) flag) footprint from SortableCert.sortPad source)
  | familyPad {family : FamilyData (Profile n)}
      (source : SortableCert env U registry target locals σ expression relevant
        (Profile.singleton (n := n + 1) (.family family)) footprint)
      (sourceProvenance : WorldSortableCertProvenance strata source) :
      WorldSortableCertProvenance strata (show SortableCert env U registry target locals σ expression relevant
        (Profile.singleton (n := n + 2) (.family (family.map id Profile.pad))) footprint from SortableCert.familyPad source)
  | unpad (source : SortableCert env U registry target locals σ expression relevant profile.pad footprint)
      (sourceProvenance : WorldSortableCertProvenance strata source) :
      WorldSortableCertProvenance strata (show SortableCert env U registry target locals σ expression relevant profile footprint from SortableCert.unpad source)
  | down {profile : Profile (n + 1)}
      (source : SortableCert env U registry target locals σ expression relevant profile footprint)
      (sourceProvenance : WorldSortableCertProvenance strata source) :
      WorldSortableCertProvenance strata (show SortableCert env U registry target locals σ expression relevant profile.down footprint from SortableCert.down source)
  | map {a b : Atom n}
      (view : AtomView env U registry target a b)
      (source : SortableCert env U registry target locals σ expression relevant profile footprint)
      (sourceProvenance : WorldSortableCertProvenance strata source) :
      WorldSortableCertProvenance strata (show SortableCert env U registry target locals σ expression relevant (view.mapType profile) footprint from SortableCert.map view source)
  | support (action : SupportAction env U registry target n)
      (source : SortableCert env U registry target locals σ expression relevant profile footprint)
      (sourceProvenance : WorldSortableCertProvenance strata source) :
      WorldSortableCertProvenance strata (show SortableCert env U registry target locals σ expression relevant (action.apply profile) footprint from SortableCert.support action source)
  | select {profile : Profile n}
      {atom : Atom n}
      (source : SortableCert env U registry target locals σ expression relevant profile footprint)
      (member : atom ∈ profile.atoms)
      (sourceProvenance : WorldSortableCertProvenance strata source) :
      WorldSortableCertProvenance strata (show SortableCert env U registry target locals σ expression relevant (.singleton atom) footprint from SortableCert.select source member)
  | focusMinimal {value focused : Profile n}
      (source : SortableCert env U registry target locals σ expression relevant support footprint)
      (minimal : Minimal value focused)
      (bound : focused ≤ support)
      (sourceProvenance : WorldSortableCertProvenance strata source) :
      WorldSortableCertProvenance strata (show SortableCert env U registry target locals σ expression relevant focused footprint from SortableCert.focusMinimal source minimal bound)

inductive WorldSortableRowsProvenance (strata : EquationStratification env) :
    {U : Nat} → {registry : CanonicalHead.Registry} → {target : List VExpr} →
    {locals : List Nat} → {σ : Subst} → {A B : VExpr} → {relevant : Bool} → 
    {n : Nat} → {ambient : Profile n} → {rows : List (Key n × Profile n)} → {footprint : Footprint} →
    SortableRows env U registry target locals σ A B relevant ambient rows footprint → Type where
  | nil  :
      WorldSortableRowsProvenance strata (show SortableRows env U registry target locals σ A B relevant ambient [] [] from SortableRows.nil )
  | cons {key : Key n}
      {output packed ambient : Profile n}
      (guard : LambdaGuard env U registry target σ A key ambient)
      (body : SortableCert env U registry target (Locals.push locals) (σ.cons key.anchor)
        B relevant output bodyFootprint)
      (normal : BinderPack n packed bodyFootprint externalFootprint)
      (covered : ∀ atom ∈ packed.atoms, atom ∈ key.input.atoms)
      (tail : SortableRows env U registry target locals σ A B relevant ambient rows tailFootprint)
      (bodyProvenance : WorldSortableCertProvenance strata body)
      (tailProvenance : WorldSortableRowsProvenance strata tail) :
      WorldSortableRowsProvenance strata (show SortableRows env U registry target locals σ A B relevant ambient ((key, output) :: rows)
        (externalFootprint ++ tailFootprint) from SortableRows.cons guard body normal covered tail)

inductive WorldSortableFamilyPlanProvenance (strata : EquationStratification env) :
    {U : Nat} → {registry : CanonicalHead.Registry} → {target : List VExpr} →
    {name : Name} → {levels : List VLevel} → {declaredType : VExpr} →
    {signature : ConstantTelescope declaredType} → {arguments : List VExpr} →
    {n : Nat} → {profile : Profile n} → {footprint : Footprint} →
    SortableFamilyPlan env U registry target name levels signature arguments profile footprint → Type where
  | terminal {name : Name}
      {levels : List VLevel}
      {declaredType : VExpr}
      {signature : ConstantTelescope declaredType}
      {arguments : List VExpr}
      {keys : List (DataRequest (Profile n))}
      (saturated : arguments.length = signature.domains.length)
      (resultSort : signature.result = .sort level)
      (relevance : Relevant level relevant)
      (captures : FamilyCaptures env U registry target signature.domains.reverse (List.range arguments.length)
        (nativeCaptureSubst arguments) (constantCaptureVariables arguments.length) keys footprint)
      (capturesProvenance : WorldFamilyCapturesProvenance strata captures) :
      WorldSortableFamilyPlanProvenance strata (show SortableFamilyPlan env U registry target name levels signature arguments
        (n := n + 1) (.singleton (.family ⟨name, levels, relevant, keys⟩)) footprint from SortableFamilyPlan.terminal saturated resultSort relevance captures)
  | binder {name : Name}
      {levels : List VLevel}
      {declaredType : VExpr}
      {signature : ConstantTelescope declaredType}
      {arguments : List VExpr}
      {domain : VExpr}
      {key : Key n}
      {output : Atom n}
      {support packed : Profile n}
      (domainOrigin : signature.domains[arguments.length]? = some domain)
      (domainCode : SortableCert env U registry target (List.range arguments.length)
        (nativeCaptureSubst arguments) domain true support domainFootprint)
      (guard : LambdaGuard env U registry target (nativeCaptureSubst arguments) domain key support)
      (body : SortableFamilyPlan env U registry target name levels signature (arguments ++ [key.anchor])
        (.singleton output) bodyFootprint)
      (pack : BinderPack n packed bodyFootprint outside)
      (covered : ∀ atom ∈ packed.atoms, atom ∈ key.input.atoms)
      (domainCodeProvenance : WorldSortableCertProvenance strata domainCode)
      (bodyProvenance : WorldSortableFamilyPlanProvenance strata body) :
      WorldSortableFamilyPlanProvenance strata (show SortableFamilyPlan env U registry target name levels signature arguments (Profile.fn key output)
        (domainFootprint ++ outside) from SortableFamilyPlan.binder domainOrigin domainCode guard body pack covered)
  | view {name : Name}
      {levels : List VLevel}
      {declaredType : VExpr}
      {signature : ConstantTelescope declaredType}
      (source : SortableFamilyPlan env U registry target name levels signature arguments
        (.singleton oldAtom) footprint)
      (view : AtomView env U registry target oldAtom newAtom)
      (sourceProvenance : WorldSortableFamilyPlanProvenance strata source) :
      WorldSortableFamilyPlanProvenance strata (show SortableFamilyPlan env U registry target name levels signature arguments (.singleton newAtom) footprint from SortableFamilyPlan.view source view)
  | pad {name : Name}
      {levels : List VLevel}
      {declaredType : VExpr}
      {signature : ConstantTelescope declaredType}
      (source : SortableFamilyPlan env U registry target name levels signature arguments demand footprint)
      (sourceProvenance : WorldSortableFamilyPlanProvenance strata source) :
      WorldSortableFamilyPlanProvenance strata (show SortableFamilyPlan env U registry target name levels signature arguments demand.pad footprint from SortableFamilyPlan.pad source)

inductive WorldRowsProvenance (strata : EquationStratification env) :
    {U : Nat} → {registry : CanonicalHead.Registry} → {target : List VExpr} →
    {sourceEnv : VEnv} → {source : List VExpr} → {A B : VExpr} → {u v : VLevel} →
    {domain : EndpointState sourceEnv U source A (.sort u)} →
    {body : EndpointState sourceEnv U (A :: source) B (.sort v)} →
    {locals : List Nat} → {σ : Subst} → {relevant : Bool} →
    {n : Nat} → {ambient : Profile n} → {rows : List (Key n × Profile n)} → {footprint : Footprint} →
    RichRows sourceEnv env U registry target domain body locals σ relevant ambient rows footprint → Type where
  | nil  :
      WorldRowsProvenance strata (show RichRows sourceEnv env U registry target domain body locals σ relevant ambient [] [] from RichRows.nil )
  | cons {domain : EndpointState sourceEnv U source A (.sort u)}
      {body : EndpointState sourceEnv U (A :: source) B (.sort v)}
      {key : Key n}
      {packed support ambient : Profile n}
      (guard : LambdaGuard env U registry target σ A key ambient)
      (certificate : RichCert sourceEnv env U registry target body (Locals.push locals)
        (σ.cons key.anchor) relevant support bodyFootprint)
      (pack : BinderPack n packed bodyFootprint outside)
      (covered : ∀ atom ∈ packed.atoms, atom ∈ key.input.atoms)
      (tail : RichRows sourceEnv env U registry target domain body locals σ relevant ambient rows tailFootprint)
      (certificateProvenance : WorldCertProvenance strata certificate)
      (tailProvenance : WorldRowsProvenance strata tail) :
      WorldRowsProvenance strata (show RichRows sourceEnv env U registry target domain body locals σ relevant ambient ((key, support) :: rows)
        (outside ++ tailFootprint) from RichRows.cons guard certificate pack covered tail)

inductive WorldFamilyPlanProvenance (strata : EquationStratification env) :
    {U : Nat} → {registry : CanonicalHead.Registry} → {target : List VExpr} →
    {headerEnv : VEnv} → {declaredType : VExpr} → {headerLevel : VLevel} →
    {header : EndpointRef headerEnv U [] declaredType (.sort headerLevel)} →
    {name : Name} → {levels : List VLevel} → {signature : ConstantTelescope declaredType} →
    {source : List VExpr} → {context : ContextDerivation headerEnv U source} → {σ : Subst} →
    {arguments : List VExpr} → {n : Nat} → {profile : Profile n} → {footprint : Footprint} →
    RichFamilyPlan env U registry target header name levels signature context σ arguments profile footprint → Type where
  | terminal {header : EndpointRef headerEnv U [] declaredType (.sort headerLevel)}
      {name : Name}
      {levels : List VLevel}
      {signature : ConstantTelescope declaredType}
      {source : List VExpr}
      {context : ContextDerivation headerEnv U source}
      {σ : Subst}
      {arguments : List VExpr}
      {keys : List (DataRequest (Profile n))}
      (saturated : arguments.length = signature.domains.length)
      (resultSort : signature.result = .sort level)
      (relevance : Relevant level relevant)
      (captures : FamilyCaptures env U registry target source (List.range arguments.length)
        σ (constantCaptureVariables arguments.length) keys footprint)
      (capturesProvenance : WorldFamilyCapturesProvenance strata captures) :
      WorldFamilyPlanProvenance strata (show RichFamilyPlan env U registry target header name levels signature context σ arguments
        (n := n + 1) (.singleton (.family ⟨name, levels, relevant, keys⟩)) footprint from RichFamilyPlan.terminal saturated resultSort relevance captures)
  | binder {header : EndpointRef headerEnv U [] declaredType (.sort headerLevel)}
      {name : Name}
      {levels : List VLevel}
      {signature : ConstantTelescope declaredType}
      {source : List VExpr}
      {context : ContextDerivation headerEnv U source}
      {σ : Subst}
      {arguments : List VExpr}
      {domain : VExpr}
      {level : VLevel}
      {key : Key n}
      {output : Atom n}
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
      (covered : ∀ atom ∈ packed.atoms, atom ∈ key.input.atoms)
      (domainCodeProvenance : WorldCertProvenance strata domainCode)
      (bodyProvenance : WorldFamilyPlanProvenance strata body) :
      WorldFamilyPlanProvenance strata (show RichFamilyPlan env U registry target header name levels signature context σ arguments (Profile.fn key output)
        (domainFootprint ++ outside) from RichFamilyPlan.binder domainOrigin original location lineage domainCode guard body pack covered)
  | view {header : EndpointRef headerEnv U [] declaredType (.sort headerLevel)}
      {name : Name}
      {levels : List VLevel}
      {signature : ConstantTelescope declaredType}
      {source : List VExpr}
      {context : ContextDerivation headerEnv U source}
      {σ : Subst}
      (source : RichFamilyPlan env U registry target header name levels signature context σ arguments
        (.singleton oldAtom) footprint)
      (view : AtomView env U registry target oldAtom newAtom)
      (sourceProvenance : WorldFamilyPlanProvenance strata source) :
      WorldFamilyPlanProvenance strata (show RichFamilyPlan env U registry target header name levels signature context σ arguments (.singleton newAtom) footprint from RichFamilyPlan.view source view)
  | pad {header : EndpointRef headerEnv U [] declaredType (.sort headerLevel)}
      {name : Name}
      {levels : List VLevel}
      {signature : ConstantTelescope declaredType}
      {source : List VExpr}
      {context : ContextDerivation headerEnv U source}
      {σ : Subst}
      (source : RichFamilyPlan env U registry target header name levels signature context σ arguments demand footprint)
      (sourceProvenance : WorldFamilyPlanProvenance strata source) :
      WorldFamilyPlanProvenance strata (show RichFamilyPlan env U registry target header name levels signature context σ arguments demand.pad footprint from RichFamilyPlan.pad source)

inductive WorldConstructorPlanProvenance (strata : EquationStratification env) :
    {U : Nat} → {registry : CanonicalHead.Registry} → {target : List VExpr} →
    {headerEnv : VEnv} → {declaredType : VExpr} → {headerLevel : VLevel} →
    {header : EndpointRef headerEnv U [] declaredType (.sort headerLevel)} →
    {name : Name} → {levels : List VLevel} → {signature : ConstantTelescope declaredType} →
    {source : List VExpr} → {context : ContextDerivation headerEnv U source} → {σ : Subst} →
    {arguments : List VExpr} → {n : Nat} → {profile : Profile n} → {footprint : Footprint} →
    RichConstructorPlan env U registry target header name levels signature context σ arguments profile footprint → Type where
  | terminal {header : EndpointRef headerEnv U [] declaredType (.sort headerLevel)}
      {name : Name}
      {levels : List VLevel}
      {signature : ConstantTelescope declaredType}
      {source : List VExpr}
      {context : ContextDerivation headerEnv U source}
      {σ : Subst}
      {arguments : List VExpr}
      {family : FamilyData (Profile n)}
      {keys : List (DataRequest (Profile n))}
      {familyLevels : List VLevel}
      {familyArguments : List VExpr}
      {resultLevel : VLevel}
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
        (Profile.singleton (n := n + 1) (.family family)) resultFootprint)
      (capturesProvenance : WorldFamilyCapturesProvenance strata captures)
      (resultCodeProvenance : WorldCertProvenance strata resultCode) :
      WorldConstructorPlanProvenance strata (show RichConstructorPlan env U registry target header name levels signature context σ arguments
        (n := n + 1) (.singleton (.ctor ⟨name, levels, keys, family, relevant⟩))
        (captureFootprint ++ resultFootprint) from RichConstructorPlan.terminal saturated resultShape relevant resultNode resultLocation resultLineage captures resultCode)
  | terminalRecord {header : EndpointRef headerEnv U [] declaredType (.sort headerLevel)}
      {name : Name}
      {levels : List VLevel}
      {signature : ConstantTelescope declaredType}
      {source : List VExpr}
      {context : ContextDerivation headerEnv U source}
      {σ : Subst}
      {arguments : List VExpr}
      {demand : RecordData (Profile n)}
      {projection : VProjectionInfo}
      {familyLevels : List VLevel}
      {familyArguments : List VExpr}
      {resultLevel : VLevel}
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
          (signature.result.subst σ) entry.2.domain))
      (capturesProvenance : WorldFamilyCapturesProvenance strata captures)
      (resultCodeProvenance : WorldCertProvenance strata resultCode) :
      WorldConstructorPlanProvenance strata (show RichConstructorPlan env U registry target header name levels signature context σ arguments
        (n := n + 1) (.singleton (.record demand)) (captureFootprint ++ resultFootprint) from RichConstructorPlan.terminalRecord registered projectionLookup constructorName bounded saturated resultShape resultNode resultLocation resultLineage captures resultCode origins)
  | binder {header : EndpointRef headerEnv U [] declaredType (.sort headerLevel)}
      {name : Name}
      {levels : List VLevel}
      {signature : ConstantTelescope declaredType}
      {source : List VExpr}
      {context : ContextDerivation headerEnv U source}
      {σ : Subst}
      {arguments : List VExpr}
      {domain : VExpr}
      {level : VLevel}
      {key : Key n}
      {output : Atom n}
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
      (covered : ∀ atom ∈ packed.atoms, atom ∈ key.input.atoms)
      (domainCodeProvenance : WorldCertProvenance strata domainCode)
      (bodyProvenance : WorldConstructorPlanProvenance strata body) :
      WorldConstructorPlanProvenance strata (show RichConstructorPlan env U registry target header name levels signature context σ arguments (Profile.fn key output)
        (domainFootprint ++ outside) from RichConstructorPlan.binder domainOrigin original location lineage domainCode guard body pack covered)
  | view {header : EndpointRef headerEnv U [] declaredType (.sort headerLevel)}
      {name : Name}
      {levels : List VLevel}
      {signature : ConstantTelescope declaredType}
      {source : List VExpr}
      {context : ContextDerivation headerEnv U source}
      {σ : Subst}
      (source : RichConstructorPlan env U registry target header name levels signature context σ arguments
        (.singleton oldAtom) footprint)
      (view : AtomView env U registry target oldAtom newAtom)
      (sourceProvenance : WorldConstructorPlanProvenance strata source) :
      WorldConstructorPlanProvenance strata (show RichConstructorPlan env U registry target header name levels signature context σ arguments (.singleton newAtom) footprint from RichConstructorPlan.view source view)
  | pad {header : EndpointRef headerEnv U [] declaredType (.sort headerLevel)}
      {name : Name}
      {levels : List VLevel}
      {signature : ConstantTelescope declaredType}
      {source : List VExpr}
      {context : ContextDerivation headerEnv U source}
      {σ : Subst}
      (source : RichConstructorPlan env U registry target header name levels signature context σ arguments demand footprint)
      (sourceProvenance : WorldConstructorPlanProvenance strata source) :
      WorldConstructorPlanProvenance strata (show RichConstructorPlan env U registry target header name levels signature context σ arguments demand.pad footprint from RichConstructorPlan.pad source)

end

mutual
noncomputable def WorldObsProvenance.worlds (annotation : WorldObsProvenance strata observation) :
    List (EquationWorldClosureOrder.World strata.rules.length) :=
  match annotation with
  | .var | .empty | .sort _ => []
  | .canonicalDelta (registry := registry) (target := target)
      (typeRealization := typeRealization) (bodyRealization := bodyRealization)
      _ _ _ _ _ _ _ _ _ _ _ typeChild bodyChild controls typeProvenance bodyProvenance =>
      (WorldQuerySite.empty (registry := registry) (target := target)
        controls typeProvenance typeRealization).worlds ++
      (WorldQuerySite.empty (registry := registry) (target := target)
        controls bodyProvenance bodyRealization).worlds ++ typeChild.worlds ++ bodyChild.worlds
  | .rigidFamily (name := name) (levels := levels) (node := node)
      (registry := registry) (target := target) (typeRealization := realization)
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ child controls provenance =>
      (WorldQuerySite.empty (registry := registry) (target := target)
        controls provenance realization).worlds ++ child.worlds
  | .canonicalConst (name := name) (levels := levels) (node := node) (registry := registry) (target := target)
      _ realization _ _ child controls provenance =>
      (WorldQuerySite.empty (registry := registry) (target := target)
        controls provenance realization).worlds ++ child.worlds
  | .family (name := name) (node := node) _ _ _ _ _ _ _ _ _ _ _ _ _ _ typeCertificateProvenance treeProvenance headerSite => headerSite.worlds ++ typeCertificateProvenance.worlds ++ treeProvenance.worlds
  | .constructor (name := name) (node := node) _ _ _ _ _ _ _ _ _ _ _ _ _ _ typeCertificateProvenance treeProvenance headerSite => headerSite.worlds ++ typeCertificateProvenance.worlds ++ treeProvenance.worlds
  | .legacy _ observationProvenance => observationProvenance.worlds
  | .lam _ _ _ _ _ _ _ domainCodeProvenance observationProvenance => domainCodeProvenance.worlds ++ observationProvenance.worlds
  | .code child => child.worlds
  | .projection _ _ _ major field majorSite fieldSite _ _ =>
      majorSite.worlds ++ fieldSite.worlds ++ major.worlds ++ field.worlds
  | .projectionSortable _ _ _ _ _ _ major field majorSite fieldSite _ =>
      majorSite.worlds ++ fieldSite.worlds ++ major.worlds ++ field.worlds
  | .app _ _ fn arg _ _ => fn.worlds ++ arg.worlds
  | .route _ child => child.worlds
  | .union first second => first.worlds ++ second.worlds
  | .view child _ | .action child _ | .select child _ | .pad child | .unpad child | .castProfile _ child | .lowerRaised child => child.worlds
noncomputable def WorldCertProvenance.worlds (annotation : WorldCertProvenance strata certificate) :
    List (EquationWorldClosureOrder.World strata.rules.length) :=
  match annotation with
  | .recipe child => child.worlds
  | .legacy _ certificateProvenance => certificateProvenance.worlds
  | .pi _ _ _ _ _ domainCodeProvenance rowsProvenance => domainCodeProvenance.worlds ++ rowsProvenance.worlds
  | .observe child _ => child.worlds
  | .route _ child => child.worlds
  | .union first second => first.worlds ++ second.worlds
  | .pad child | .down child | .map _ child | .support _ child | .select child _ => child.worlds
noncomputable def WorldCodeRecipeProvenance.worlds (annotation : WorldCodeRecipeProvenance strata recipe) :
    List (EquationWorldClosureOrder.World strata.rules.length) :=
  match annotation with
  | .root (registry := registry) (target := target) _ _ _ _ _ _ _ realization _ _ child controls provenance =>
      (WorldQuerySite.empty (registry := registry) (target := target) controls provenance realization).worlds ++ child.worlds
  | .domain child | .body child _ _ | .fixedBody child _ _ | .action _ child => child.worlds
  | .resources child transfer => child.worlds ++ transfer.worlds
noncomputable def WorldRecipeResourceProvenance.worlds
    (annotation : WorldRecipeResourceProvenance strata transfer) :
    List (EquationWorldClosureOrder.World strata.rules.length) :=
  match annotation with
  | .nil => []
  | .cons head rest => head.worlds ++ rest.worlds
noncomputable def WorldLegacyObsProvenance.worlds (annotation : WorldLegacyObsProvenance strata query) :
    List (EquationWorldClosureOrder.World strata.rules.length) :=
  match annotation with
  | .delta _ _ _ _ _ _ _ _ _ _ _ _ certificateProvenance bodyProvenance _ typeSite bodySite => typeSite.worlds ++ bodySite.worlds ++ certificateProvenance.worlds ++ bodyProvenance.worlds
  | .native _ _ _ _ _ _ _ _ _ _ _ _ typeCertificateProvenance treeProvenance _ _ headerSite => headerSite.worlds ++ typeCertificateProvenance.worlds ++ treeProvenance.worlds
  | .family _ _ _ _ _ _ _ _ _ _ _ _ _ typeCertificateProvenance treeProvenance _ headerSite => headerSite.worlds ++ typeCertificateProvenance.worlds ++ treeProvenance.worlds
  | .constructor _ _ _ _ _ _ _ _ _ _ _ _ _ typeCertificateProvenance treeProvenance _ headerSite => headerSite.worlds ++ typeCertificateProvenance.worlds ++ treeProvenance.worlds
  | .var _ _ _ _ => []
  | .empty => []
  | .sort _ => []
  | .app _ _ _ _ fnProvenance argProvenance => fnProvenance.worlds ++ argProvenance.worlds
  | .lam _ _ _ _ _ domainProvenance bodyProvenance => domainProvenance.worlds ++ bodyProvenance.worlds
  | .pi _ _ _ domainProvenance bodiesProvenance => domainProvenance.worlds ++ bodiesProvenance.worlds
  | .union _ _ leftProvenance rightProvenance => leftProvenance.worlds ++ rightProvenance.worlds
  | .view _ _ sourceProvenance => sourceProvenance.worlds
  | .pad _ sourceProvenance => sourceProvenance.worlds
  | .unpad _ sourceProvenance => sourceProvenance.worlds
  | .rowShift _ sourceProvenance => sourceProvenance.worlds
noncomputable def WorldLegacyCertProvenance.worlds (annotation : WorldLegacyCertProvenance strata query) :
    List (EquationWorldClosureOrder.World strata.rules.length) :=
  match annotation with
  | .seed _ _ observationProvenance => observationProvenance.worlds
  | .union _ _ leftProvenance rightProvenance => leftProvenance.worlds ++ rightProvenance.worlds
  | .pad _ sourceProvenance => sourceProvenance.worlds
  | .familyPad _ sourceProvenance => sourceProvenance.worlds
  | .unpad _ sourceProvenance => sourceProvenance.worlds
  | .down _ sourceProvenance => sourceProvenance.worlds
  | .map _ _ sourceProvenance => sourceProvenance.worlds
  | .select _ _ sourceProvenance => sourceProvenance.worlds
  | .focusMinimal _ _ _ sourceProvenance => sourceProvenance.worlds
noncomputable def WorldLegacyRowsProvenance.worlds (annotation : WorldLegacyRowsProvenance strata query) :
    List (EquationWorldClosureOrder.World strata.rules.length) :=
  match annotation with
  | .nil => []
  | .cons _ _ _ _ _ bodyProvenance tailProvenance => bodyProvenance.worlds ++ tailProvenance.worlds
noncomputable def WorldNativeCapturesProvenance.worlds (annotation : WorldNativeCapturesProvenance strata query) :
    List (EquationWorldClosureOrder.World strata.rules.length) :=
  match annotation with
  | .prefix _ => []
  | .index _ _ _ _ _ _ _ _ _ _ _ _ _ naturalCertificateProvenance declaredCertificateProvenance previousProvenance => naturalCertificateProvenance.worlds ++ declaredCertificateProvenance.worlds ++ previousProvenance.worlds
  | .proof _ _ _ _ _ _ _ previousProvenance => previousProvenance.worlds
noncomputable def WorldNativePlanProvenance.worlds (annotation : WorldNativePlanProvenance strata query) :
    List (EquationWorldClosureOrder.World strata.rules.length) :=
  match annotation with
  | .terminal _ _ _ _ _ _ _ _ _ _ _ _ _ _ bodyProvenance capturesProvenance _ _ equationSite => equationSite.worlds ++ bodyProvenance.worlds ++ capturesProvenance.worlds
  | .binder _ _ _ _ _ _ domainCodeProvenance bodyProvenance => domainCodeProvenance.worlds ++ bodyProvenance.worlds
noncomputable def WorldFamilyCapturesProvenance.worlds (annotation : WorldFamilyCapturesProvenance strata query) :
    List (EquationWorldClosureOrder.World strata.rules.length) :=
  match annotation with
  | .nil => []
  | .cons _ _ _ _ _ _ valueProvenance tailProvenance => valueProvenance.worlds ++ tailProvenance.worlds
noncomputable def WorldLegacyFamilyPlanProvenance.worlds (annotation : WorldLegacyFamilyPlanProvenance strata query) :
    List (EquationWorldClosureOrder.World strata.rules.length) :=
  match annotation with
  | .terminal _ _ _ _ capturesProvenance => capturesProvenance.worlds
  | .binder _ _ _ _ _ _ domainCodeProvenance bodyProvenance => domainCodeProvenance.worlds ++ bodyProvenance.worlds
  | .view _ _ sourceProvenance => sourceProvenance.worlds
  | .pad _ sourceProvenance => sourceProvenance.worlds
noncomputable def WorldLegacyConstructorPlanProvenance.worlds (annotation : WorldLegacyConstructorPlanProvenance strata query) :
    List (EquationWorldClosureOrder.World strata.rules.length) :=
  match annotation with
  | .terminal _ _ _ _ _ capturesProvenance resultCodeProvenance => capturesProvenance.worlds ++ resultCodeProvenance.worlds
  | .binder _ _ _ _ _ _ domainCodeProvenance bodyProvenance => domainCodeProvenance.worlds ++ bodyProvenance.worlds
  | .view _ _ sourceProvenance => sourceProvenance.worlds
  | .pad _ sourceProvenance => sourceProvenance.worlds
noncomputable def WorldSortableObsProvenance.worlds (annotation : WorldSortableObsProvenance strata query) :
    List (EquationWorldClosureOrder.World strata.rules.length) :=
  match annotation with
  | .family _ _ _ _ _ _ _ _ _ _ _ _ _ typeCertificateProvenance treeProvenance _ headerSite => headerSite.worlds ++ typeCertificateProvenance.worlds ++ treeProvenance.worlds
  | .legacy _ observationProvenance => observationProvenance.worlds
  | .code _ _ certificateProvenance => certificateProvenance.worlds
  | .app _ _ _ _ fnProvenance argProvenance => fnProvenance.worlds ++ argProvenance.worlds
  | .lam _ _ _ _ _ domainProvenance bodyProvenance => domainProvenance.worlds ++ bodyProvenance.worlds
  | .union _ _ leftProvenance rightProvenance => leftProvenance.worlds ++ rightProvenance.worlds
  | .view _ _ sourceProvenance => sourceProvenance.worlds
  | .action _ _ sourceProvenance => sourceProvenance.worlds
  | .pad _ sourceProvenance => sourceProvenance.worlds
  | .unpad _ sourceProvenance => sourceProvenance.worlds
  | .rowShift _ sourceProvenance => sourceProvenance.worlds
noncomputable def WorldSortableCertProvenance.worlds (annotation : WorldSortableCertProvenance strata query) :
    List (EquationWorldClosureOrder.World strata.rules.length) :=
  match annotation with
  | .ofCode _ _ sourceProvenance => sourceProvenance.worlds
  | .pi _ _ _ domainProvenance bodiesProvenance => domainProvenance.worlds ++ bodiesProvenance.worlds
  | .observe _ _ observationProvenance => observationProvenance.worlds
  | .seed _ _ observationProvenance => observationProvenance.worlds
  | .union _ _ leftProvenance rightProvenance => leftProvenance.worlds ++ rightProvenance.worlds
  | .pad _ sourceProvenance => sourceProvenance.worlds
  | .sortPad _ sourceProvenance => sourceProvenance.worlds
  | .familyPad _ sourceProvenance => sourceProvenance.worlds
  | .unpad _ sourceProvenance => sourceProvenance.worlds
  | .down _ sourceProvenance => sourceProvenance.worlds
  | .map _ _ sourceProvenance => sourceProvenance.worlds
  | .support _ _ sourceProvenance => sourceProvenance.worlds
  | .select _ _ sourceProvenance => sourceProvenance.worlds
  | .focusMinimal _ _ _ sourceProvenance => sourceProvenance.worlds
noncomputable def WorldSortableRowsProvenance.worlds (annotation : WorldSortableRowsProvenance strata query) :
    List (EquationWorldClosureOrder.World strata.rules.length) :=
  match annotation with
  | .nil => []
  | .cons _ _ _ _ _ bodyProvenance tailProvenance => bodyProvenance.worlds ++ tailProvenance.worlds
noncomputable def WorldSortableFamilyPlanProvenance.worlds (annotation : WorldSortableFamilyPlanProvenance strata query) :
    List (EquationWorldClosureOrder.World strata.rules.length) :=
  match annotation with
  | .terminal _ _ _ _ capturesProvenance => capturesProvenance.worlds
  | .binder _ _ _ _ _ _ domainCodeProvenance bodyProvenance => domainCodeProvenance.worlds ++ bodyProvenance.worlds
  | .view _ _ sourceProvenance => sourceProvenance.worlds
  | .pad _ sourceProvenance => sourceProvenance.worlds
noncomputable def WorldRowsProvenance.worlds (annotation : WorldRowsProvenance strata query) :
    List (EquationWorldClosureOrder.World strata.rules.length) :=
  match annotation with
  | .nil => []
  | .cons _ _ _ _ _ certificateProvenance tailProvenance => certificateProvenance.worlds ++ tailProvenance.worlds
noncomputable def WorldFamilyPlanProvenance.worlds (annotation : WorldFamilyPlanProvenance strata query) :
    List (EquationWorldClosureOrder.World strata.rules.length) :=
  match annotation with
  | .terminal _ _ _ _ capturesProvenance => capturesProvenance.worlds
  | .binder _ _ _ _ _ _ _ _ _ domainCodeProvenance bodyProvenance => domainCodeProvenance.worlds ++ bodyProvenance.worlds
  | .view _ _ sourceProvenance => sourceProvenance.worlds
  | .pad _ sourceProvenance => sourceProvenance.worlds
noncomputable def WorldConstructorPlanProvenance.worlds (annotation : WorldConstructorPlanProvenance strata query) :
    List (EquationWorldClosureOrder.World strata.rules.length) :=
  match annotation with
  | .terminal _ _ _ _ _ _ _ _ capturesProvenance resultCodeProvenance => capturesProvenance.worlds ++ resultCodeProvenance.worlds
  | .terminalRecord _ _ _ _ _ _ _ _ _ _ _ _ capturesProvenance resultCodeProvenance => capturesProvenance.worlds ++ resultCodeProvenance.worlds
  | .binder _ _ _ _ _ _ _ _ _ domainCodeProvenance bodyProvenance => domainCodeProvenance.worlds ++ bodyProvenance.worlds
  | .view _ _ sourceProvenance => sourceProvenance.worlds
  | .pad _ sourceProvenance => sourceProvenance.worlds
end

/-- The exact selection/view/lowering used by record extraction retains all
query-owned opening provenance, even though its footprint need not mention it. -/
theorem RichGradedResult.recordObservation_worlds
    (henv : env.Ordered)
    (result : RichGradedResult sourceEnv env U registry target node locals σ available
      (Profile.singleton (n := n + 1) (.record (record : RecordData (Profile n)))))
    (annotation : WorldObsProvenance strata result.observation) :
    ∃ footprint, ∃ observation : RichObs sourceEnv env U registry target node locals σ
      (Profile.singleton (n := n + 1) (.record record)) footprint,
      ∃ output : WorldObsProvenance strata observation,
        footprint.Available available ∧ output.worlds = annotation.worlds := by
  have adapter := result.adapter
  rw [raiseProfile_singleton] at adapter
  have shape := recordShape_raise record result.bound
  have normalized := recordShape_normal shape
  change GeneralProfileAdapter env U registry target _ (.singleton (AdapterNormal.atom _)) at adapter
  rw [normalized] at adapter
  obtain ⟨normal, member, ⟨entry⟩⟩ := adapter.origin (List.mem_singleton_self _)
  obtain ⟨original, originalMember, equal⟩ := List.mem_map.mp member
  subst normal
  have same := recordAdapter_rigid entry shape
  let selected := RichObs.view (.select result.observation originalMember) (AdapterNormal.view henv original)
  have outputEq : Profile.singleton (AdapterNormal.atom original) =
      raiseProfile result.rank result.bound (Profile.singleton (n := n + 1) (.record record)) := by
    simp only [raiseProfile_singleton, same]
  let observed : RichObs sourceEnv env U registry target node locals σ
      (raiseProfile result.rank result.bound (Profile.singleton (n := n + 1) (.record record))) result.footprint :=
    (congrArg (fun profile => RichObs sourceEnv env U registry target node locals σ profile result.footprint) outputEq).mp selected
  let output : WorldObsProvenance strata observed.lowerRaised :=
    .lowerRaised (.castProfile outputEq (.view (.select annotation originalMember) (AdapterNormal.view henv original)))
  exact ⟨result.footprint, observed.lowerRaised, output, result.resources, rfl⟩


end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
