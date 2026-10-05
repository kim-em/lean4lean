import Lean4Lean.Theory.Typing.AnchoredNativeInitialArguments
import Lean4Lean.Theory.Typing.AnchoredNativePlanBridge

/-! Install the concrete initial native construction in the actual mutual
source grammar. Scope is derived from registered equations and their original
raw typing; the initial all-index guard is produced before the observation. -/

namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics InductiveSignature NativeRecursorData
set_option backward.isDefEq.respectTransparency false

noncomputable def NativeCaptureSupport.toCaptures
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {target : List VExpr}
    {data : NativeRecursorData} {program : SaturatedProgram data} {witnesses : List VExpr}
    {index : Nat} {required native : Footprint}
    (support : NativeCaptureSupport env U registry target program witnesses index required native) :
    NativeCaptures env U registry target program witnesses index required native := by
  match support with
  | .prefix required => exact .prefix required
  | .index guard nativeValue copiedValue pack covered previous =>
    exact .index guard.naturalCertificate guard.naturalResources
      guard.declaredCertificate guard.declaredResources
      guard.naturalTyped guard.declaredTyped guard.alignment guard.declaredCode
      nativeValue copiedValue pack covered previous.toCaptures
  | .proof instruction captured sourceProof domainProof inhabitant pack previous =>
    exact .proof instruction captured sourceProof domainProof inhabitant pack previous.toCaptures
termination_by sizeOf support

noncomputable def NativeTelescopeTree.toPlan
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {target : List VExpr}
    {data : NativeRecursorData} {levels : List VLevel}
    {signature : NativeConstantSignature data levels}
    {arguments : List VExpr} {demand : Profile n} {footprint : Footprint}
    (henv : env.Ordered) (registered : NativeRecursorRegistered env data)
    (tree : NativeTelescopeTree env U registry target signature arguments demand footprint) :
    NativePlan env U registry target signature arguments demand footprint := by
  match tree with
  | .terminal leaf =>
    have selected := (saturatedProgram_spec leaf.selected).2.2.2.2.2.2.2.2.1
    have raw := henv.defEqWF (registered.singletonEquation selected)
    have lhsClosed : leaf.program.equation.lhs.Closed :=
      VExpr.WF.closedN henv ⟨_, raw.1⟩ trivial
    have rhsClosed : leaf.program.equation.rhs.Closed :=
      VExpr.WF.closedN henv ⟨_, raw.2⟩ trivial
    exact .terminal leaf.program leaf.selected lhsClosed rhsClosed leaf.saturated
      leaf.noTrailing leaf.prefix_eq leaf.witnesses leaf.witnessLength leaf.witnessPrefix
      leaf.argumentAlignment leaf.arguments_eq leaf.body leaf.captures.toCaptures
  | .binder origin domainCode guard body pack covered =>
    exact .binder origin domainCode guard (body.toPlan henv registered) pack covered
termination_by sizeOf tree

/-- Actual core observation; there is no remaining external-wrapper premise. -/
noncomputable def NativeConstantObservation.source
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {target : List VExpr}
    {name : Name} {levels : List VLevel} {demand : Profile n}
    (henv : env.Ordered) (levelsWF : ∀ level ∈ levels, level.WF U)
    (native : NativeConstantObservation env U registry target name levels demand)
    (locals : List Nat) (σ : Subst) :
    Obs env U registry target locals σ (.const name levels) demand [] := by
  have typeClosed : native.signature.type.Closed := by
    obtain ⟨u, typeWF⟩ := henv.constWF (native.registered.recursorType native.signature.typeOrigin)
    exact VExpr.WF.closedN henv ⟨_, typeWF⟩ trivial
  exact .native native.lookup native.notDefinition native.name_eq native.registered
    levelsWF levelsWF (Lean4Lean.List.Forall₂.rfl (fun _ _ => by rfl))
    native.signature typeClosed native.typeCertificate native.typed
    (native.tree.toPlan henv native.registered)

noncomputable def NativeInitialTree.source
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {target : List VExpr}
    {data : NativeRecursorData} {levels : List VLevel} {name : Name}
    {signature : NativeConstantSignature data levels} {demand : Profile n}
    (henv : env.Ordered) (levelsWF : ∀ level ∈ levels, level.WF U)
    (lookup : registry.natives name = some data)
    (notDefinition : registry.definitions name = none)
    (name_eq : data.name = name) (registered : NativeRecursorRegistered env data)
    (formed : OnCtx signature.domains.reverse (env.IsType U))
    {typeSupport : Profile n} {typeRealization : Subst}
    (typeCertificate : CodeCert env U registry target [] typeRealization
      (signature.type.instL levels) typeSupport [])
    (typed : demand.HasType typeSupport)
    (tree : NativeInitialTree env U registry target signature [] demand [])
    (locals : List Nat) (σ : Subst) :
    Obs env U registry target locals σ (.const name levels) demand [] :=
  (tree.observation lookup notDefinition name_eq registered formed typeCertificate typed).source
    henv levelsWF locals σ

end Lean4Lean.AnchoredSource.Adapted
