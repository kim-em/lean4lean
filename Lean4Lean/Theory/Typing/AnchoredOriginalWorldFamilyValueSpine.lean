import Lean4Lean.Theory.Typing.AnchoredOriginalWorldFunctionApplicationOrigin
import Lean4Lean.Theory.Typing.AnchoredOriginalRichFamilyDemand

/-! Parse every function prefix of a family application into its actual
original argument queries. The constant leaf retains the full query and world
annotation, including canonical wrappers and the original header sites. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1200000

inductive WorldFamilyValueSpine
    (root : EndpointRef sourceEnv U source rootExpression rootType)
    (env : VEnv) (registry : CanonicalHead.Registry) (target : List VExpr)
    (locals : List Nat) (σ : Subst)
    {strata : EquationStratification env}
    (controls : OriginalWorldControls strata controlSource)
    (frontier : List (World strata.rules.length)) (name : Name) (levels : List VLevel) :
    VExpr → {n : Nat} → Atom n → Footprint → Type where
  | constant {node : EndpointState sourceEnv U source (.const name levels) assigned}
      (query : RichObs sourceEnv env U registry target node locals σ demand footprint)
      (location : Located root node) (selected : atom ∈ demand.atoms)
      (ends : FamilyEndDemand atom)
      (nonsortable : ∀ flag, ¬ (Profile.singleton atom).HasType (.sort flag))
      (ready : ControlledStoredQuery controls frontier (.observation query)) :
      WorldFamilyValueSpine root env registry target locals σ controls frontier name levels
        (.const name levels) atom footprint
  | app (origin : RichAppOrigin root env registry target source locals σ f a)
      (function : WorldFamilyValueSpine root env registry target locals σ controls frontier name levels
        f (n := origin.rank+1) (.fn origin.key origin.output) origin.functionFootprint)
      (path : GeneralOutputPath env U registry target origin.output atom)
      (included : List.Subset (origin.functionFootprint ++ origin.argumentFootprint) footprint)
      (argumentReady : ControlledStoredQuery controls frontier (.observation origin.argument)) :
      WorldFamilyValueSpine root env registry target locals σ controls frontier name levels
        (.app f a) atom footprint

theorem RichObs.familyValueSpineControlled
    {strata : EquationStratification env}
    {controls : OriginalWorldControls strata controlSource}
    {frontier : List (World strata.rules.length)}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (formed : OnCtx target (env.IsType U))
    {root : EndpointRef sourceEnv U source rootExpression rootType}
    {node : EndpointState sourceEnv U source expression assigned}
    {demand : Profile n}
    (query : RichObs sourceEnv env U registry target node locals σ demand footprint)
    (location : Located root node)
    (head : expression.getAppFnArgs.1 = .const name levels)
    (member : atom ∈ demand.atoms) (ends : FamilyEndDemand atom)
    (nonsortable : ∀ flag, ¬ (Profile.singleton atom).HasType (.sort flag))
    (ready : ControlledStoredQuery controls frontier (.observation query)) :
    Nonempty (WorldFamilyValueSpine root env registry target locals σ controls frontier
      name levels expression atom footprint) := by
  match expression with
  | .const found foundLevels =>
    simp only [getAppFnArgs_const] at head
    cases head
    exact ⟨.constant query location member ends nonsortable ready⟩
  | .app f a =>
    obtain ⟨origin, children, ⟨path⟩, included, worlds, depth⟩ :=
      ready.annotation.applicationOriginNonsortable location member nonsortable
    let fnReady : ControlledStoredQuery controls frontier (.observation origin.function) := {
      annotation := children.function
      within := fun control active =>
        Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (depth _)) (ready.within control active)
      sponsored := fun world present => ready.sponsored world (worlds (List.mem_append_left _ present)) }
    let argReady : ControlledStoredQuery controls frontier (.observation origin.argument) := {
      annotation := children.argument
      within := fun control active =>
        Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (depth _)) (ready.within control active)
      sponsored := fun world present => ready.sponsored world (worlds (List.mem_append_right _ present)) }
    have fnNonsortable : ∀ flag, ¬ (Profile.fn origin.key origin.output).HasType (.sort flag) := by
      intro flag sorted
      obtain ⟨cover, member, impossible⟩ := sorted.2.2 _ (List.mem_singleton_self _)
      cases List.mem_singleton.mp member
      contradiction
    have outputEnds : FamilyEndDemand origin.output := ends.outputBack henv hscoped formed path
    obtain ⟨function⟩ := origin.function.familyValueSpineControlled henv hscoped formed
      (.appFunction origin.location) (by simpa only [getAppFnArgs_app] using head)
      (List.mem_singleton_self _) outputEnds fnNonsortable fnReady
    exact ⟨.app origin function path included argReady⟩
  | .bvar _ | .sort _ | .lam _ _ | .forallE _ _ | .proj _ _ _ | .elim _ _ _ =>
    simp [getAppFnArgs, getAppFnArgs.go] at head
termination_by sizeOf expression

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
