import Lean4Lean.Theory.Typing.AnchoredOriginalRichFamilyObservationConsumption
import Lean4Lean.Theory.Typing.AnchoredOriginalRichFamilyPlanLegacy

/-! Source family consumption keeps the native constant's original header,
seed universes and closed code query. The legacy initializer computes actual
header locations rather than supplying new declared-domain semantics. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics InductiveSignature
open OriginalClosureMeasure OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1200000

theorem RichFamilyPlan.singleton_of_mem
    {demand : Profile n} {atom : Atom n}
    (plan : RichFamilyPlan env U registry target header name levels signature context σ arguments demand footprint)
    (member : atom ∈ demand.atoms) : demand = .singleton atom := by
  match n, demand, footprint, plan with
  | _, _, _, .terminal .. => cases List.mem_singleton.mp member; rfl
  | _, _, _, .binder .. => cases List.mem_singleton.mp member; rfl
  | _, _, _, .view .. => cases List.mem_singleton.mp member; rfl
  | _, _, _, .pad source =>
    obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
    rw [source.singleton_of_mem present]
    rfl
termination_by sizeOf plan

/-- The retained native leaf, including its precise original header root.
The code query and literal plan are copied from that leaf, not normalized
against an independently selected registration packet. -/
structure RetainedRichFamilySeed
    (root : EndpointRef sourceEnv U source rootExpression rootType)
    (env : VEnv) (registry : CanonicalHead.Registry) (target : List VExpr)
    (name : Name) (levels : List VLevel) where
  assigned : VExpr
  node : EndpointState sourceEnv U source (.const name levels) assigned
  location : Located root node
  info : VConstant
  origin : ConstantHeaderOrigin sourceEnv name info
  lookup : env.constants name = some info
  notDefinition : registry.definitions name = none
  notNative : registry.natives name = none
  notQuotient : name ≠ ``Quot.lift
  seed : List VLevel
  seedWF : ∀ level ∈ seed, level.WF U
  seedLength : seed.length = info.uvars
  levelsWF : ∀ level ∈ levels, level.WF U
  equivalent : List.Forall₂ (· ≈ ·) seed levels
  signature : ConstantTelescope (info.type.instL seed)
  typeClosed : info.type.Closed
  rank : Nat
  atom : Atom rank
  typeRealization : Subst
  typeSupport : Profile rank
  typeCertificate : RichCert origin.source env U registry target
    (.ref (origin.familyHeader seedWF).reference) [] typeRealization true typeSupport []
  typed : (Profile.singleton atom).HasType typeSupport
  planRealization : Subst
  plan : RichFamilyPlan env U registry target (origin.familyHeader seedWF).reference
    name seed signature .nil planRealization [] (.singleton atom) []

noncomputable def RetainedRichFamilySeed.observation
    {root : EndpointRef sourceEnv U source rootExpression rootType}
    (seed : RetainedRichFamilySeed root env registry target name levels) :
    RichObs sourceEnv env U registry target seed.node locals σ (.singleton seed.atom) [] :=
  .family seed.origin seed.lookup seed.notDefinition seed.notNative seed.notQuotient
    seed.seedWF seed.seedLength seed.levelsWF seed.equivalent seed.signature seed.typeClosed
    seed.typeCertificate seed.typed seed.plan

/-- Native extraction retains exactly the fields of the actual leaf. -/
noncomputable def RetainedRichFamilySeed.ofNative
    {info : VConstant} {assigned : VExpr} {n : Nat} {atom : Atom n} {support : Profile n}
    {typeRealization planRealization : Subst}
    {root : EndpointRef sourceEnv U source rootExpression rootType}
    {node : EndpointState sourceEnv U source (.const name levels) assigned}
    (location : Located root node)
    (origin : ConstantHeaderOrigin sourceEnv name info)
    (lookup : env.constants name = some info)
    (notDefinition : registry.definitions name = none) (notNative : registry.natives name = none)
    (notQuotient : name ≠ ``Quot.lift)
    (seedWF : ∀ level ∈ seedLevels, level.WF U) (seedLength : seedLevels.length = info.uvars)
    (levelsWF : ∀ level ∈ levels, level.WF U) (equivalent : List.Forall₂ (· ≈ ·) seedLevels levels)
    (signature : ConstantTelescope (info.type.instL seedLevels)) (typeClosed : info.type.Closed)
    (certificate : RichCert origin.source env U registry target
      (.ref (origin.familyHeader seedWF).reference) [] typeRealization true support [])
    (typed : (Profile.singleton (atom : Atom n)).HasType support)
    (plan : RichFamilyPlan env U registry target (origin.familyHeader seedWF).reference name seedLevels signature
      .nil planRealization [] (.singleton atom) []) :
    RetainedRichFamilySeed root env registry target name levels where
  assigned := assigned
  node := node
  location := location
  info := info
  origin := origin
  lookup := lookup
  notDefinition := notDefinition
  notNative := notNative
  notQuotient := notQuotient
  seed := seedLevels
  seedWF := seedWF
  seedLength := seedLength
  levelsWF := levelsWF
  equivalent := equivalent
  signature := signature
  typeClosed := typeClosed
  rank := n
  atom := atom
  typeRealization := typeRealization
  typeSupport := support
  typeCertificate := certificate
  typed := typed
  planRealization := planRealization
  plan := plan

/-- A legacy leaf keeps its literal seed and guards. Its original header
spine is computed once; no family/domain answer is an input. -/
noncomputable def RetainedRichFamilySeed.ofSortable
    {info : VConstant} {assigned : VExpr} {n : Nat} {atom : Atom n} {support : Profile n}
    {typeRealization : Subst}
    {root : EndpointRef sourceEnv U source rootExpression rootType}
    {node : EndpointState sourceEnv U source (.const name levels) assigned}
    (location : Located root node)
    (origin : ConstantHeaderOrigin sourceEnv name info)
    (lookup : env.constants name = some info)
    (notDefinition : registry.definitions name = none) (notNative : registry.natives name = none)
    (notQuotient : name ≠ ``Quot.lift)
    (seedWF : ∀ level ∈ seedLevels, level.WF U) (seedLength : seedLevels.length = info.uvars)
    (levelsWF : ∀ level ∈ levels, level.WF U) (equivalent : List.Forall₂ (· ≈ ·) seedLevels levels)
    (signature : ConstantTelescope (info.type.instL seedLevels)) (typeClosed : info.type.Closed)
    (certificate : SortableCert env U registry target [] typeRealization
      (info.type.instL seedLevels) true support [])
    (typed : (Profile.singleton (atom : Atom n)).HasType support)
    (plan : SortableFamilyPlan env U registry target name seedLevels signature [] (.singleton atom) []) :
    RetainedRichFamilySeed root env registry target name levels :=
  .ofNative location origin lookup notDefinition notNative notQuotient seedWF seedLength levelsWF
    equivalent signature typeClosed (.legacy certificate) typed
    (Classical.choice (SortableFamilyPlan.atOriginalHeader plan))

structure RetainedRichFamilyConsumption
    (root : EndpointRef sourceEnv U source rootExpression rootType)
    (env : VEnv) (registry : CanonicalHead.Registry) (target : List VExpr)
    (locals : List Nat) (σ : Subst) (available : Valuation)
    (name : Name) (levels : List VLevel) (arguments : List VExpr) (requested : Atom n) where
  seed : RetainedRichFamilySeed root env registry target name levels
  cursor : RichFamilyPlanConsumption root (seed.origin.familyHeader seed.seedWF).reference
    env registry target locals σ available name seed.seed seed.signature arguments requested

noncomputable def RetainedRichFamilySeed.initial
    (seed : RetainedRichFamilySeed root env registry target name levels) :
    RetainedRichFamilyConsumption root env registry target locals σ available name levels [] seed.atom :=
  ⟨seed, .bare seed.plan⟩

noncomputable def RetainedRichFamilyConsumption.outputPath
    {root : EndpointRef sourceEnv U source rootExpression rootType}
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (result : RetainedRichFamilyConsumption root env registry target locals σ available name levels arguments a)
    (path : GeneralOutputPath env U registry target a b) :
    RetainedRichFamilyConsumption root env registry target locals σ available name levels arguments b :=
  ⟨result.seed, result.cursor.outputPath henv hscoped formed path⟩

/-- Application consumption keeps the SAME seed packet for every prefix. -/
theorem RetainedRichFamilyConsumption.appOrigin
    {root : EndpointRef sourceEnv U source rootExpression rootType}
    (henv : env.Ordered) (hscoped : registry.Scoped) (below : sourceEnv ≤ env)
    (formed : OnCtx target (env.IsType U))
    (origin : RichAppOrigin root env registry target source locals σ f a)
    (result : RetainedRichFamilyConsumption root env registry target locals σ available name levels arguments
      (n := origin.rank+1) (.fn origin.key origin.output))
    (resources : (origin.functionFootprint ++ origin.argumentFootprint).Available available)
    (live : Profile.Live env U registry target origin.rawInput)
    (path : GeneralOutputPath env U registry target origin.output requested) :
    ∃ next : RetainedRichFamilyConsumption root env registry target locals σ available name levels
      (arguments ++ [a]) requested, next.seed = result.seed := by
  obtain ⟨next⟩ := result.cursor.appOrigin henv hscoped (result.seed.origin.sourceBelow.trans below)
    formed origin resources live path
  exact ⟨⟨result.seed, next⟩, rfl⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
