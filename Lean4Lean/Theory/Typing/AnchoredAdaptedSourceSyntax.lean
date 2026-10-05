import Lean4Lean.Theory.Typing.DefinitionPatterns
import Lean4Lean.Theory.Typing.AnchoredSourceObservation
import Lean4Lean.Theory.Typing.AnchoredSourceFootprint
import Lean4Lean.Theory.Typing.AnchoredAdapterNormalization
import Lean4Lean.Theory.Typing.AnchoredNativeSyntax
import Lean4Lean.Theory.Typing.AnchoredConstantSyntax
import Lean4Lean.Theory.Typing.NativeRecursorRegistration
import Lean4Lean.Theory.Typing.AnchoredDomainChainTransport

/-! Strictly positive source observations and finite native plans. Native
children live at their literal declared telescopes with witnessed base-context
captures. Universe-equivalent source packets retain one original finite plan. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
open InductiveSignature NativeRecursorData
set_option backward.isDefEq.respectTransparency false
mutual
inductive Obs (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) : (locals : List Nat) → Subst → VExpr →
      {n : Nat} → Profile n → Footprint → Type where
  | delta {value : VDefVal} {name : Name} {seedLevels levels : List VLevel}
      (lookup : registry.definitions name = some value)
      (name_eq : value.name = name)
      (registered : DefinitionRegistered env value)
      (seedWF : ∀ level ∈ seedLevels, level.WF U)
      (seedLength : seedLevels.length = value.uvars)
      (levelsWF : ∀ level ∈ levels, level.WF U)
      (equivalent : List.Forall₂ (· ≈ ·) seedLevels levels)
      (bodyClosed : value.value.Closed) (typeClosed : value.type.Closed)
      {atom : Atom n} {support : Profile n} {typeRealization bodyRealization : Subst}
      (certificate : CodeCert env U registry target [] typeRealization
        (value.type.instL seedLevels) support [])
      (typed : (Profile.singleton atom).HasType support)
      (body : Obs env U registry target [] bodyRealization
        (value.value.instL seedLevels) (.singleton atom) []) :
      Obs env U registry target locals σ (.const name levels) (.singleton atom) []
  | native {data : NativeRecursorData} {name : Name} {seedLevels levels : List VLevel}
      (lookup : registry.natives name = some data)
      (notDefinition : registry.definitions name = none)
      (name_eq : data.name = name)
      (registered : NativeRecursorRegistered env data)
      (seedWF : ∀ level ∈ seedLevels, level.WF U)
      (levelsWF : ∀ level ∈ levels, level.WF U)
      (equivalent : List.Forall₂ (· ≈ ·) seedLevels levels)
      (signature : NativeConstantSignature data seedLevels)
      (typeClosed : signature.type.Closed)
      {typeSupport : Profile n} {typeRealization : Subst}
      (typeCertificate : CodeCert env U registry target [] typeRealization
        (signature.type.instL seedLevels) typeSupport [])
      (typed : demand.HasType typeSupport)
      (tree : NativePlan env U registry target signature [] demand []) :
      Obs env U registry target locals σ (.const name levels) demand []
  | family {info : VConstant} {name : Name} {seedLevels levels : List VLevel}
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
      {typeSupport : Profile n} {typeRealization : Subst}
      (typeCertificate : CodeCert env U registry target [] typeRealization
        (info.type.instL seedLevels) typeSupport [])
      (typed : demand.HasType typeSupport)
      (tree : FamilyPlan env U registry target name seedLevels signature [] demand []) :
      Obs env U registry target locals σ (.const name levels) demand []
  | constructor {info : VConstant} {name : Name} {seedLevels levels : List VLevel}
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
      {typeSupport : Profile n} {typeRealization : Subst}
      (typeCertificate : CodeCert env U registry target [] typeRealization
        (info.type.instL seedLevels) typeSupport [])
      (typed : demand.HasType typeSupport)
      (tree : ConstructorPlan env U registry target name seedLevels signature [] demand []) :
      Obs env U registry target locals σ (.const name levels) demand []
  | var (locals : List Nat) (σ : Subst) (i : Nat) (demand : Profile n) :
      Obs env U registry target locals σ (.bvar i) demand [(i, ⟨n, demand⟩)]
  | empty :
      Obs env U registry target locals σ expression (n := n) .empty []
  | sort (relevant : Relevant level flag) :
      Obs env U registry target locals σ (.sort level) (.sort (n := n) flag) []
  | app {key : Key n} {output : Atom n}
      (fn : Obs env U registry target locals σ f (Profile.fn key output) fnFootprint)
      (arg : Obs env U registry target locals σ a rawInput argFootprint)
      (arguments : NormalProfileAdapter env U registry target rawInput key.input)
      (admitted : Admitted env U registry target key (a.subst σ) (a.subst σ)) :
      Obs env U registry target locals σ (.app f a) (.singleton output)
        (fnFootprint ++ argFootprint)
  | lam {key : Key n} {output : Atom n} {support packed : Profile n}
      (domain : CodeCert env U registry target locals σ annotation support domainFootprint)
      (guard : LambdaGuard env U registry target σ annotation key support)
      (body : Obs env U registry target (Locals.push locals) (σ.cons key.anchor) expression
        (.singleton output) bodyFootprint)
      (normal : BinderPack n packed bodyFootprint externalFootprint)
      (covered : ∀ atom ∈ packed.atoms, atom ∈ key.input.atoms) :
      Obs env U registry target locals σ (.lam annotation expression) (Profile.fn key output)
        (domainFootprint ++ externalFootprint)
  | pi {ambient : Profile n} {rows : List (Key n × Profile n)}
      {prototypeDomain prototypeBody : VExpr}
      (domain : CodeCert env U registry target locals σ A ambient domainFootprint)
      (guard : PiGuard env U target σ A B prototypeDomain prototypeBody)
      (bodies : PiRows env U registry target locals σ A B ambient rows rowFootprint) :
      Obs env U registry target locals σ (.forallE A B)
        (Profile.pi prototypeDomain prototypeBody ambient rows)
        (domainFootprint ++ rowFootprint)
  | union
      (left : Obs env U registry target locals σ expression leftDemand leftFootprint)
      (right : Obs env U registry target locals σ expression rightDemand rightFootprint) :
      Obs env U registry target locals σ expression (leftDemand.union rightDemand)
        (leftFootprint ++ rightFootprint)
  | view
      (source : Obs env U registry target locals σ expression (.singleton oldAtom) footprint)
      (view : AtomView env U registry target oldAtom newAtom) :
      Obs env U registry target locals σ expression (.singleton newAtom) footprint
  | pad
      (source : Obs env U registry target locals σ expression demand footprint) :
      Obs env U registry target locals σ expression demand.pad footprint
  | unpad
      (source : Obs env U registry target locals σ expression demand.pad footprint) :
      Obs env U registry target locals σ expression demand footprint
  | rowShift
      (source : Obs env U registry target locals σ expression (Profile.fn key output) footprint) :
      Obs env U registry target locals σ expression (Profile.fn key.pad (.pad output)) footprint

inductive CodeCert (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) : (locals : List Nat) → Subst → VExpr →
    {n : Nat} → Profile n → Footprint → Type where
  | seed (observation : Obs env U registry target locals σ expression profile footprint)
      (formed : profile.HasType (.sort true)) :
      CodeCert env U registry target locals σ expression profile footprint
  | union (left : CodeCert env U registry target locals σ expression leftDemand leftFootprint)
      (right : CodeCert env U registry target locals σ expression rightDemand rightFootprint) :
      CodeCert env U registry target locals σ expression (leftDemand.union rightDemand)
        (leftFootprint ++ rightFootprint)
  | pad (source : CodeCert env U registry target locals σ expression profile footprint) :
      CodeCert env U registry target locals σ expression profile.pad footprint
  | familyPad {family : FamilyData (Profile n)}
      (source : CodeCert env U registry target locals σ expression
        (Profile.singleton (n := n + 1) (.family family)) footprint) :
      CodeCert env U registry target locals σ expression
        (Profile.singleton (n := n + 2) (.family (family.map id Profile.pad))) footprint
  | unpad (source : CodeCert env U registry target locals σ expression profile.pad footprint) :
      CodeCert env U registry target locals σ expression profile footprint
  | down {profile : Profile (n + 1)}
      (source : CodeCert env U registry target locals σ expression profile footprint) :
      CodeCert env U registry target locals σ expression profile.down footprint
  | map {a b : Atom n} (view : AtomView env U registry target a b)
      (source : CodeCert env U registry target locals σ expression profile footprint) :
      CodeCert env U registry target locals σ expression (view.mapType profile) footprint
  | select {profile : Profile n} {atom : Atom n}
      (source : CodeCert env U registry target locals σ expression profile footprint)
      (member : atom ∈ profile.atoms) :
      CodeCert env U registry target locals σ expression (.singleton atom) footprint
  | focusMinimal {value focused : Profile n}
      (source : CodeCert env U registry target locals σ expression support footprint)
      (minimal : Minimal value focused) (bound : focused ≤ support) :
      CodeCert env U registry target locals σ expression focused footprint

/-- A Pi row uses the actual source codomain at its stored anchor. Its
certificate may need fewer local leaves than the function input: coverage
is literal atom membership, so it needs no semantic restriction oracle. -/
inductive PiRows (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) : (locals : List Nat) → Subst → VExpr → VExpr →
      {n : Nat} → Profile n → List (Key n × Profile n) → Footprint → Type where
  | nil : PiRows env U registry target locals σ A B ambient [] []
  | cons {key : Key n} {output packed ambient : Profile n}
      (guard : LambdaGuard env U registry target σ A key ambient)
      (body : CodeCert env U registry target (Locals.push locals) (σ.cons key.anchor)
        B output bodyFootprint)
      (normal : BinderPack n packed bodyFootprint externalFootprint)
      (covered : ∀ atom ∈ packed.atoms, atom ∈ key.input.atoms)
      (tail : PiRows env U registry target locals σ A B ambient rows tailFootprint) :
      PiRows env U registry target locals σ A B ambient ((key, output) :: rows)
        (externalFootprint ++ tailFootprint)
inductive NativeCaptures (env : VEnv) (U : Nat)
    (registry : CanonicalHead.Registry) (target : List VExpr)
    : {data : NativeRecursorData} → (program : SaturatedProgram data) →
    (witnesses : List VExpr) → Nat → Footprint → Footprint → Type where
  | prefix {data : NativeRecursorData} {program : SaturatedProgram data}
      {witnesses : List VExpr} (required : Footprint) :
      NativeCaptures env U registry target program witnesses 0 required
        (Footprint.sourceLift (.skipN .refl (program.prefixArgs.length - data.indexOffset)) required)
  | index {data : NativeRecursorData} {program : SaturatedProgram data}
      {witnesses : List VExpr} {templates : NativeIndexTemplates program}
      {naturalAvailable captureAvailable : Valuation} {input packed : Profile n}
      {required outside previousNative : Footprint} {value : VExpr}
      {naturalSupport declaredSupport : Profile n} {naturalFootprint declaredFootprint : Footprint}
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
        (declaredFootprint ++ outside) previousNative) :
      NativeCaptures env U registry target program witnesses (templates.field + 1) required
        (previousNative ++
          Footprint.sourceLift (.skipN .refl
            (program.prefixArgs.length - (data.indexOffset + templates.slot)))
            naturalFootprint ++
          [(program.prefixArgs.length - 1 - (data.indexOffset + templates.slot), ⟨n, input⟩)])
  | proof {data : NativeRecursorData} {program : SaturatedProgram data}
      {witnesses : List VExpr} {field : Nat} {domain witness : VExpr} {required outside native : Footprint}
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
      (previous : NativeCaptures env U registry target program witnesses field outside native) :
      NativeCaptures env U registry target program witnesses (field + 1) required native


inductive NativePlan (env : VEnv) (U : Nat)
    (registry : CanonicalHead.Registry) (target : List VExpr)
    : {data : NativeRecursorData} → {levels : List VLevel} →
    (signature : NativeConstantSignature data levels) →
    (arguments : List VExpr) → {n : Nat} → Profile n → Footprint → Type where
  | terminal {data : NativeRecursorData} {levels : List VLevel}
      {signature : NativeConstantSignature data levels} {arguments : List VExpr}
      {demand : Profile n} {nativeFootprint : Footprint}
      (program : SaturatedProgram data)
      (selected : data.saturatedProgram levels arguments = some program)
      (lhsClosed : program.equation.lhs.Closed)
      (rhsClosed : program.equation.rhs.Closed)
      (saturated : arguments.length = data.majorOffset + 1)
      (noTrailing : program.trailing = []) (prefix_eq : program.prefixArgs = arguments)
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
        program.instructions.length bodyFootprint nativeFootprint) :
      NativePlan env U registry target signature arguments demand nativeFootprint
  | binder {data : NativeRecursorData} {levels : List VLevel}
      {signature : NativeConstantSignature data levels} {arguments : List VExpr} {domain : VExpr} {key : Key n} {output : Atom n}
      {support packed : Profile n} {domainFootprint bodyFootprint outside : Footprint}
      (domainOrigin : signature.domains[arguments.length]? = some domain)
      (domainCode : CodeCert env U registry target (List.range arguments.length)
        (nativeCaptureSubst arguments) domain support domainFootprint)
      (guard : LambdaGuard env U registry target (nativeCaptureSubst arguments) domain key support)
      (body : NativePlan env U registry target signature (arguments ++ [key.anchor])
        (.singleton output) bodyFootprint)
      (pack : BinderPack n packed bodyFootprint outside)
      (covered : ∀ atom ∈ packed.atoms, atom ∈ key.input.atoms) :
      NativePlan env U registry target signature arguments (Profile.fn key output)
        (domainFootprint ++ outside)

/-- Actual terminal argument observations retain their finite leaves and
the admission at the frozen seed. Adapters record any finite input view. -/
inductive FamilyCaptures (env : VEnv) (U : Nat)
    (registry : CanonicalHead.Registry) (target : List VExpr) :
    (source : List VExpr) → (locals : List Nat) → (σ : Subst) →
    {n : Nat} → List VExpr → List (DataRequest (Profile n)) → Footprint → Type where
  | nil : FamilyCaptures env U registry target source locals σ (n := n) [] [] []
  | cons {key : DataRequest (Profile n)} {index : Nat} {A : VExpr} {rawInput : Profile n}
      (lookup : Lookup source index A)
      (value : Obs env U registry target locals σ (.bvar index) rawInput valueFootprint)
      (adapter : NormalProfileAdapter env U registry target rawInput key.input)
      (alignment : DomainChain env U registry target key.input key.domain (A.subst σ))
      (anchor : RankedData.RequestAdmission env U (relations env U registry n) target key (σ index) (σ index))
      (tail : FamilyCaptures env U registry target source locals σ expressions keys tailFootprint) :
      FamilyCaptures env U registry target source locals σ (.bvar index :: expressions) (key :: keys)
        (valueFootprint ++ tailFootprint)

/-- A bare family constant is observed through its literal declaration
telescope. Terminal leaves are the captured source variables, and binder
packs close their actual footprints before the head is replayed with app. -/
inductive FamilyPlan (env : VEnv) (U : Nat)
    (registry : CanonicalHead.Registry) (target : List VExpr) :
    (name : Name) → (levels : List VLevel) → {declaredType : VExpr} →
    (signature : ConstantTelescope declaredType) →
    (arguments : List VExpr) → {n : Nat} → Profile n → Footprint → Type where
  | terminal {name : Name} {levels : List VLevel} {declaredType : VExpr}
      {signature : ConstantTelescope declaredType} {arguments : List VExpr} {keys : List (DataRequest (Profile n))}
      (saturated : arguments.length = signature.domains.length)
      (resultSort : signature.result = .sort level)
      (relevance : Relevant level relevant)
      (captures : FamilyCaptures env U registry target signature.domains.reverse (List.range arguments.length)
        (nativeCaptureSubst arguments) (constantCaptureVariables arguments.length) keys footprint) :
      FamilyPlan env U registry target name levels signature arguments
        (n := n + 1) (.singleton (.family ⟨name, levels, relevant, keys⟩)) footprint
  | binder {name : Name} {levels : List VLevel} {declaredType : VExpr}
      {signature : ConstantTelescope declaredType}
      {arguments : List VExpr} {domain : VExpr} {key : Key n} {output : Atom n}
      {support packed : Profile n}
      (domainOrigin : signature.domains[arguments.length]? = some domain)
      (domainCode : CodeCert env U registry target (List.range arguments.length)
        (nativeCaptureSubst arguments) domain support domainFootprint)
      (guard : LambdaGuard env U registry target (nativeCaptureSubst arguments) domain key support)
      (body : FamilyPlan env U registry target name levels signature (arguments ++ [key.anchor])
        (.singleton output) bodyFootprint)
      (pack : BinderPack n packed bodyFootprint outside)
      (covered : ∀ atom ∈ packed.atoms, atom ∈ key.input.atoms) :
      FamilyPlan env U registry target name levels signature arguments (Profile.fn key output)
        (domainFootprint ++ outside)
  | view {name : Name} {levels : List VLevel} {declaredType : VExpr}
      {signature : ConstantTelescope declaredType}
      (source : FamilyPlan env U registry target name levels signature arguments
        (.singleton oldAtom) footprint)
      (view : AtomView env U registry target oldAtom newAtom) :
      FamilyPlan env U registry target name levels signature arguments (.singleton newAtom) footprint
  | pad {name : Name} {levels : List VLevel} {declaredType : VExpr}
      {signature : ConstantTelescope declaredType}
      (source : FamilyPlan env U registry target name levels signature arguments demand footprint) :
      FamilyPlan env U registry target name levels signature arguments demand.pad footprint


/-- A constructor telescope retains the literal declared family-result certificate. -/
inductive ConstructorPlan (env : VEnv) (U : Nat)
    (registry : CanonicalHead.Registry) (target : List VExpr) :
    (name : Name) → (levels : List VLevel) → {declaredType : VExpr} →
    (signature : ConstantTelescope declaredType) →
    (arguments : List VExpr) → {n : Nat} → Profile n → Footprint → Type where
  | terminal {name : Name} {levels : List VLevel} {declaredType : VExpr}
      {signature : ConstantTelescope declaredType} {arguments : List VExpr}
      {family : FamilyData (Profile n)} {keys : List (DataRequest (Profile n))}
      {familyLevels : List VLevel} {familyArguments : List VExpr}
      (saturated : arguments.length = signature.domains.length)
      (resultShape : signature.result = mkApps (.const family.name familyLevels) familyArguments)
      (relevant : family.relevant = true)
      (captures : FamilyCaptures env U registry target signature.domains.reverse (List.range arguments.length)
        (nativeCaptureSubst arguments) (constantCaptureVariables arguments.length) keys captureFootprint)
      (resultCode : CodeCert env U registry target (List.range arguments.length)
        (nativeCaptureSubst arguments) signature.result
        (Profile.singleton (n := n + 1) (.family family)) resultFootprint) :
      ConstructorPlan env U registry target name levels signature arguments
        (n := n + 1) (.singleton (.ctor ⟨name, levels, keys, family, relevant⟩))
        (captureFootprint ++ resultFootprint)
  | binder {name : Name} {levels : List VLevel} {declaredType : VExpr}
      {signature : ConstantTelescope declaredType}
      {arguments : List VExpr} {domain : VExpr} {key : Key n} {output : Atom n}
      {support packed : Profile n}
      (domainOrigin : signature.domains[arguments.length]? = some domain)
      (domainCode : CodeCert env U registry target (List.range arguments.length)
        (nativeCaptureSubst arguments) domain support domainFootprint)
      (guard : LambdaGuard env U registry target (nativeCaptureSubst arguments) domain key support)
      (body : ConstructorPlan env U registry target name levels signature (arguments ++ [key.anchor])
        (.singleton output) bodyFootprint)
      (pack : BinderPack n packed bodyFootprint outside)
      (covered : ∀ atom ∈ packed.atoms, atom ∈ key.input.atoms) :
      ConstructorPlan env U registry target name levels signature arguments (Profile.fn key output)
        (domainFootprint ++ outside)
  | view {name : Name} {levels : List VLevel} {declaredType : VExpr}
      {signature : ConstantTelescope declaredType}
      (source : ConstructorPlan env U registry target name levels signature arguments
        (.singleton oldAtom) footprint)
      (view : AtomView env U registry target oldAtom newAtom) :
      ConstructorPlan env U registry target name levels signature arguments (.singleton newAtom) footprint
  | pad {name : Name} {levels : List VLevel} {declaredType : VExpr}
      {signature : ConstantTelescope declaredType}
      (source : ConstructorPlan env U registry target name levels signature arguments demand footprint) :
      ConstructorPlan env U registry target name levels signature arguments demand.pad footprint

end

variable {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {target : List VExpr}
/-- Every finite family plan has one terminal or function demand; the view
and padding nodes preserve this literal singleton shape. -/
theorem FamilyPlan.singleton
    {name : Name} {levels : List VLevel} {declaredType : VExpr}
    {signature : ConstantTelescope declaredType} {arguments : List VExpr}
    {demand : Profile n} {footprint : Footprint}
    (tree : FamilyPlan env U registry target name levels signature arguments demand footprint) :
    ∃ atom, demand = Profile.singleton atom := by
  match tree with
  | .terminal .. => exact ⟨_, rfl⟩
  | .binder .. => exact ⟨_, rfl⟩
  | .view .. => exact ⟨_, rfl⟩
  | .pad source =>
    obtain ⟨atom, rfl⟩ := source.singleton
    exact ⟨.pad atom, Profile.pad_singleton atom⟩
termination_by sizeOf tree
decreasing_by all_goals simp_wf; omega

theorem FamilyPlan.singleton_of_mem
    {name : Name} {levels : List VLevel} {declaredType : VExpr}
    {signature : ConstantTelescope declaredType} {arguments : List VExpr}
    {demand : Profile n} {footprint : Footprint}
    (tree : FamilyPlan env U registry target name levels signature arguments demand footprint)
    {atom : Atom n} (member : atom ∈ demand.atoms) : demand = .singleton atom := by
  obtain ⟨chosen, rfl⟩ := tree.singleton
  cases List.mem_singleton.mp member
  rfl

theorem ConstructorPlan.singleton
    {name : Name} {levels : List VLevel} {declaredType : VExpr}
    {signature : ConstantTelescope declaredType} {arguments : List VExpr}
    {demand : Profile n} {footprint : Footprint}
    (tree : ConstructorPlan env U registry target name levels signature arguments demand footprint) :
    ∃ atom, demand = Profile.singleton atom := by
  match tree with
  | .terminal .. => exact ⟨_, rfl⟩
  | .binder .. => exact ⟨_, rfl⟩
  | .view .. => exact ⟨_, rfl⟩
  | .pad source =>
    obtain ⟨atom, rfl⟩ := source.singleton
    exact ⟨.pad atom, Profile.pad_singleton atom⟩
termination_by sizeOf tree
decreasing_by all_goals simp_wf; omega

theorem ConstructorPlan.singleton_of_mem
    {name : Name} {levels : List VLevel} {declaredType : VExpr}
    {signature : ConstantTelescope declaredType} {arguments : List VExpr}
    {demand : Profile n} {footprint : Footprint}
    (tree : ConstructorPlan env U registry target name levels signature arguments demand footprint)
    {atom : Atom n} (member : atom ∈ demand.atoms) : demand = .singleton atom := by
  obtain ⟨chosen, rfl⟩ := tree.singleton
  cases List.mem_singleton.mp member
  rfl

/-- A bare native head has at least its major binder left to supply. -/
theorem NativePlan.fn_profile
    {data : NativeRecursorData} {levels : List VLevel}
    {signature : NativeConstantSignature data levels} {demand : Profile n} {footprint : Footprint}
    (tree : NativePlan env U registry target signature [] demand footprint) :
    ∃ (rank : Nat) (bound : n = rank + 1) (key : Key rank) (output : Atom rank),
      bound ▸ demand = Profile.fn key output := by
  cases tree with
  | terminal program selected lhsClosed rhsClosed saturated => simp only [List.length_nil] at saturated; omega
  | binder domainOrigin domainCode guard body pack covered => exact ⟨_, rfl, _, _, rfl⟩
/-- Atom selection retains the identical finite native plan. -/
theorem NativePlan.singleton_of_mem
    {data : NativeRecursorData} {levels : List VLevel}
    {signature : NativeConstantSignature data levels} {demand : Profile n} {footprint : Footprint}
    (tree : NativePlan env U registry target signature [] demand footprint)
    {atom : Atom n} (member : atom ∈ demand.atoms) : demand = .singleton atom := by
  obtain ⟨rank, rfl, key, output, equality⟩ := tree.fn_profile
  change demand = Profile.fn key output at equality
  cases equality
  have same : atom = .fn key output := List.mem_singleton.mp member
  exact same ▸ rfl
private theorem levelsTrans {a b c : List VLevel}
    (first : List.Forall₂ (· ≈ ·) a b) (second : List.Forall₂ (· ≈ ·) b c) :
    List.Forall₂ (· ≈ ·) a c := by
  induction first generalizing c with
  | nil => cases second; exact .nil
  | cons h tail ih => cases second with
    | cons h' tail' => exact .cons (h.trans h') (ih tail')
/-- Universe packet transport preserves the exact original native plan and
all demands. It never requests interpretation of a reconstructed descendant. -/
noncomputable def Obs.constLevels
    {locals : List Nat} {σ : Subst} {name : Name} {levels levels' : List VLevel}
    {demand : Profile n} {footprint : Footprint}
    (observation : Obs env U registry target locals σ (.const name levels) demand footprint)
    (scopedLevels : ∀ level ∈ levels', level.WF U)
    (equivalent : List.Forall₂ (· ≈ ·) levels levels') :
    Obs env U registry target locals σ (.const name levels') demand footprint := by
  match observation with
  | .delta lookup nameEq registered seedWF seedLength _ seedEq bodyClosed typeClosed certificate typed body =>
    exact .delta lookup nameEq registered seedWF seedLength scopedLevels
      (levelsTrans seedEq equivalent) bodyClosed typeClosed certificate typed body
  | .native lookup notDefinition nameEq registered seedWF _ seedEq signature typeClosed typeCertificate typed tree =>
    exact .native lookup notDefinition nameEq registered seedWF scopedLevels
      (levelsTrans seedEq equivalent) signature typeClosed typeCertificate typed tree
  | .family lookup notDefinition notNative notQuotient seedWF seedLength _ seedEq
      signature typeClosed typeCertificate typed tree =>
    exact .family lookup notDefinition notNative notQuotient seedWF seedLength scopedLevels
      (levelsTrans seedEq equivalent) signature typeClosed typeCertificate typed tree
  | .constructor lookup notDefinition notNative notQuotient seedWF seedLength _ seedEq
      signature typeClosed typeCertificate typed tree =>
    exact .constructor lookup notDefinition notNative notQuotient seedWF seedLength scopedLevels
      (levelsTrans seedEq equivalent) signature typeClosed typeCertificate typed tree
  | .empty => exact .empty
  | .union left right =>
    exact .union (left.constLevels scopedLevels equivalent) (right.constLevels scopedLevels equivalent)
  | .view source transformation => exact .view (source.constLevels scopedLevels equivalent) transformation
  | .pad source => exact .pad (source.constLevels scopedLevels equivalent)
  | .unpad source => exact .unpad (source.constLevels scopedLevels equivalent)
  | .rowShift source => exact .rowShift (source.constLevels scopedLevels equivalent)
termination_by sizeOf observation
decreasing_by all_goals simp_wf; omega

end Lean4Lean.AnchoredSource.Adapted
