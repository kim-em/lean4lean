import Lean4Lean.Theory.Typing.AnchoredGeneralAdapterNormalization
import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceGradedCode
import Lean4Lean.Theory.Typing.AnchoredSortCodeGrades
import Lean4Lean.Theory.Typing.AnchoredAtomAction

/-! Finite formation queries retain the requested sort relevance. Native Pi
rows may themselves request proof-family codes; domain certificates use the same syntax at relevance `true`. This is an isolated syntax, not a production
observer migration or a claim that legacy fundamental transfer handles Pi. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false
mutual
inductive SortableCert (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) : (locals : List Nat) → Subst → VExpr → Bool →
    {n : Nat} → Profile n → Footprint → Type where
  | ofCode (source : CodeCert env U registry target locals σ expression profile footprint)
      (formed : profile.HasType (.sort relevant)) :
      SortableCert env U registry target locals σ expression relevant profile footprint
  | pi {ambient : Profile n} {rows : List (Key n × Profile n)}
      {prototypeDomain prototypeBody : VExpr}
      (domain : SortableCert env U registry target locals σ A true ambient domainFootprint)
      (guard : PiGuard env U target σ A B prototypeDomain prototypeBody)
      (bodies : SortableRows env U registry target locals σ A B relevant ambient rows rowFootprint) :
      SortableCert env U registry target locals σ (.forallE A B) relevant
        (Profile.pi prototypeDomain prototypeBody ambient rows)
        (domainFootprint ++ rowFootprint)
  | observe (observation : SortableObs env U registry target locals σ expression profile footprint)
      (formed : profile.HasType (.sort relevant)) :
      SortableCert env U registry target locals σ expression relevant profile footprint
  | seed (observation : Obs env U registry target locals σ expression profile footprint)
      (formed : profile.HasType (.sort relevant)) :
      SortableCert env U registry target locals σ expression relevant profile footprint
  | union (left : SortableCert env U registry target locals σ expression relevant leftDemand leftFootprint)
      (right : SortableCert env U registry target locals σ expression relevant rightDemand rightFootprint) :
      SortableCert env U registry target locals σ expression relevant (leftDemand.union rightDemand)
        (leftFootprint ++ rightFootprint)
  | pad (source : SortableCert env U registry target locals σ expression relevant profile footprint) :
      SortableCert env U registry target locals σ expression relevant profile.pad footprint
  | sortPad
      (source : SortableCert env U registry target locals σ expression relevant
        (Profile.sort (n := n) flag) footprint) :
      SortableCert env U registry target locals σ expression relevant
        (Profile.sort (n := n + 1) flag) footprint
  | familyPad {family : FamilyData (Profile n)}
      (source : SortableCert env U registry target locals σ expression relevant
        (Profile.singleton (n := n + 1) (.family family)) footprint) :
      SortableCert env U registry target locals σ expression relevant
        (Profile.singleton (n := n + 2) (.family (family.map id Profile.pad))) footprint
  | unpad (source : SortableCert env U registry target locals σ expression relevant profile.pad footprint) :
      SortableCert env U registry target locals σ expression relevant profile footprint
  | down {profile : Profile (n + 1)}
      (source : SortableCert env U registry target locals σ expression relevant profile footprint) :
      SortableCert env U registry target locals σ expression relevant profile.down footprint
  | map {a b : Atom n} (view : AtomView env U registry target a b)
      (source : SortableCert env U registry target locals σ expression relevant profile footprint) :
      SortableCert env U registry target locals σ expression relevant (view.mapType profile) footprint
  | support (action : SupportAction env U registry target n)
      (source : SortableCert env U registry target locals σ expression relevant profile footprint) :
      SortableCert env U registry target locals σ expression relevant (action.apply profile) footprint
  | select {profile : Profile n} {atom : Atom n}
      (source : SortableCert env U registry target locals σ expression relevant profile footprint)
      (member : atom ∈ profile.atoms) :
      SortableCert env U registry target locals σ expression relevant (.singleton atom) footprint
  | focusMinimal {value focused : Profile n}
      (source : SortableCert env U registry target locals σ expression relevant support footprint)
      (minimal : Minimal value focused) (bound : focused ≤ support) :
      SortableCert env U registry target locals σ expression relevant focused footprint

/-- A Pi row uses the actual source codomain at its stored anchor. Its
certificate may need fewer local leaves than the function input: coverage
is literal atom membership, so it needs no semantic restriction oracle. -/
inductive SortableRows (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) : (locals : List Nat) → Subst → VExpr → VExpr → Bool →
      {n : Nat} → Profile n → List (Key n × Profile n) → Footprint → Type where
  | nil : SortableRows env U registry target locals σ A B relevant ambient [] []
  | cons {key : Key n} {output packed ambient : Profile n}
      (guard : LambdaGuard env U registry target σ A key ambient)
      (body : SortableCert env U registry target (Locals.push locals) (σ.cons key.anchor)
        B relevant output bodyFootprint)
      (normal : BinderPack n packed bodyFootprint externalFootprint)
      (covered : ∀ atom ∈ packed.atoms, atom ∈ key.input.atoms)
      (tail : SortableRows env U registry target locals σ A B relevant ambient rows tailFootprint) :
      SortableRows env U registry target locals σ A B relevant ambient ((key, output) :: rows)
        (externalFootprint ++ tailFootprint)
/-- Computational closure of formation queries. A native Boolean Pi query
may occur as an actual argument or lambda body without erasing its rows. -/
inductive SortableObs (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) : (locals : List Nat) → Subst → VExpr →
      {n : Nat} → Profile n → Footprint → Type where
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
      (typeCertificate : SortableCert env U registry target [] typeRealization
        (info.type.instL seedLevels) true typeSupport [])
      (typed : demand.HasType typeSupport)
      (tree : SortableFamilyPlan env U registry target name seedLevels signature [] demand []) :
      SortableObs env U registry target locals σ (.const name levels) demand []
  | legacy (observation : Obs env U registry target locals σ expression demand footprint) :
      SortableObs env U registry target locals σ expression demand footprint
  | code (relevant : Bool)
      (certificate : SortableCert env U registry target locals σ expression relevant demand footprint) :
      SortableObs env U registry target locals σ expression demand footprint
  | app {key : Key n} {output : Atom n}
      (fn : SortableObs env U registry target locals σ f (Profile.fn key output) fnFootprint)
      (arg : SortableObs env U registry target locals σ a rawInput argFootprint)
      (arguments : GeneralNormalProfileAdapter env U registry target rawInput key.input)
      (admitted : Admitted env U registry target key (a.subst σ) (a.subst σ)) :
      SortableObs env U registry target locals σ (.app f a) (.singleton output)
        (fnFootprint ++ argFootprint)
  | lam {key : Key n} {output : Atom n} {support packed : Profile n}
      (domain : SortableCert env U registry target locals σ annotation true support domainFootprint)
      (guard : LambdaGuard env U registry target σ annotation key support)
      (body : SortableObs env U registry target (Locals.push locals) (σ.cons key.anchor) expression
        (.singleton output) bodyFootprint)
      (normal : BinderPack n packed bodyFootprint externalFootprint)
      (covered : ∀ atom ∈ packed.atoms, atom ∈ key.input.atoms) :
      SortableObs env U registry target locals σ (.lam annotation expression) (Profile.fn key output)
        (domainFootprint ++ externalFootprint)
  | union
      (left : SortableObs env U registry target locals σ expression leftDemand leftFootprint)
      (right : SortableObs env U registry target locals σ expression rightDemand rightFootprint) :
      SortableObs env U registry target locals σ expression (leftDemand.union rightDemand)
        (leftFootprint ++ rightFootprint)
  | view
      (source : SortableObs env U registry target locals σ expression (.singleton oldAtom) footprint)
      (view : AtomView env U registry target oldAtom newAtom) :
      SortableObs env U registry target locals σ expression (.singleton newAtom) footprint
  | action
      (source : SortableObs env U registry target locals σ expression (.singleton oldAtom) footprint)
      (action : AtomAction env U registry target oldAtom newAtom) :
      SortableObs env U registry target locals σ expression (.singleton newAtom) footprint
  | pad
      (source : SortableObs env U registry target locals σ expression demand footprint) :
      SortableObs env U registry target locals σ expression demand.pad footprint
  | unpad
      (source : SortableObs env U registry target locals σ expression demand.pad footprint) :
      SortableObs env U registry target locals σ expression demand footprint
  | rowShift
      (source : SortableObs env U registry target locals σ expression (Profile.fn key output) footprint) :
      SortableObs env U registry target locals σ expression (Profile.fn key.pad (.pad output)) footprint

inductive SortableFamilyPlan (env : VEnv) (U : Nat)
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
      SortableFamilyPlan env U registry target name levels signature arguments
        (n := n + 1) (.singleton (.family ⟨name, levels, relevant, keys⟩)) footprint
  | binder {name : Name} {levels : List VLevel} {declaredType : VExpr}
      {signature : ConstantTelescope declaredType}
      {arguments : List VExpr} {domain : VExpr} {key : Key n} {output : Atom n}
      {support packed : Profile n}
      (domainOrigin : signature.domains[arguments.length]? = some domain)
      (domainCode : SortableCert env U registry target (List.range arguments.length)
        (nativeCaptureSubst arguments) domain true support domainFootprint)
      (guard : LambdaGuard env U registry target (nativeCaptureSubst arguments) domain key support)
      (body : SortableFamilyPlan env U registry target name levels signature (arguments ++ [key.anchor])
        (.singleton output) bodyFootprint)
      (pack : BinderPack n packed bodyFootprint outside)
      (covered : ∀ atom ∈ packed.atoms, atom ∈ key.input.atoms) :
      SortableFamilyPlan env U registry target name levels signature arguments (Profile.fn key output)
        (domainFootprint ++ outside)
  | view {name : Name} {levels : List VLevel} {declaredType : VExpr}
      {signature : ConstantTelescope declaredType}
      (source : SortableFamilyPlan env U registry target name levels signature arguments
        (.singleton oldAtom) footprint)
      (view : AtomView env U registry target oldAtom newAtom) :
      SortableFamilyPlan env U registry target name levels signature arguments (.singleton newAtom) footprint
  | pad {name : Name} {levels : List VLevel} {declaredType : VExpr}
      {signature : ConstantTelescope declaredType}
      (source : SortableFamilyPlan env U registry target name levels signature arguments demand footprint) :
      SortableFamilyPlan env U registry target name levels signature arguments demand.pad footprint



end

mutual
theorem SortableCert.formed
    (cert : SortableCert env U registry Γ locals σ expression relevant profile footprint) :
    profile.HasType (.sort relevant) := by
  match cert with
  | .ofCode source formed => exact formed
  | .pi domain guard bodies =>
    apply Profile.HasType.pi_iff.mpr
    exact ⟨Profile.WF.pi_iff.mpr ⟨domain.formed, fun key output member =>
      ⟨(bodies.typed member).1, (bodies.typed member).2.wf_value⟩⟩,
      fun key output member => (bodies.typed member).2⟩
  | .seed observation formed | .observe observation formed => exact formed
  | .union left right => exact left.formed.union right.formed
  | .pad source => exact source.formed.pad_sort
  | .sortPad source => exact source.formed.sortPad
  | .familyPad source => exact source.formed.familyPad
  | .unpad source => simpa only [Profile.down_sort] using source.formed.pad_inv
  | .down source => simpa only [Profile.down_sort] using source.formed.down
  | .map view source => exact view.mapType_sort source.formed
  | .support action source => exact action.preservesSort source.formed
  | .select source member => exact source.formed.singleton_of_mem member
  | .focusMinimal source minimal bound =>
    exact source.formed.restrict bound minimal.formation.wf_value
termination_by sizeOf cert

theorem SortableRows.typed
    {ambient : Profile n} {rows : List (Key n × Profile n)}
    (bodies : SortableRows env U registry Γ locals σ A B relevant ambient rows footprint)
    {key : Key n} {output : Profile n} (member : (key, output) ∈ rows) :
    key.input.HasType ambient ∧ output.HasType (.sort relevant) := by
  match bodies with
  | .nil => cases member
  | .cons guard body normal covered tail =>
    rcases List.mem_cons.mp member with equal | later
    · have formed := body.formed
      cases equal; exact ⟨guard.inputTyped, formed⟩
    · exact tail.typed later
termination_by sizeOf bodies
end

noncomputable def SortableCert.piLiteral
    (domain : SortableCert env U registry Γ locals σ A true ambient domainFootprint)
    (bodies : SortableRows env U registry Γ locals σ A B relevant ambient rows rowFootprint) :
    SortableCert env U registry Γ locals σ (.forallE A B) relevant
      (Profile.pi (A.subst σ) (B.subst σ.lift) ambient rows)
      (domainFootprint ++ rowFootprint) := .pi domain PiGuard.literal bodies

end Lean4Lean.AnchoredSource.Adapted
