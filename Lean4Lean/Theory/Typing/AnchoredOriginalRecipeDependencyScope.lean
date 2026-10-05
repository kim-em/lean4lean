import Lean4Lean.Theory.Typing.AnchoredOriginalRecipeDependencyStructure

namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open private traceRename from Lean4Lean.Theory.Typing.AnchoredOriginalRecipeDependencyModel
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1200000

/-- Composition of the actual finite transfer with earlier pending resource
programs. Each leaf replacement is itself a finite trace, never a value. -/
theorem RecipeResourceTransfer.dependencyReplay
    (transfer : RecipeResourceTransfer env U registry target locals σ required footprint)
    (resources : ∀ index need, (index, need) ∈ footprint →
      RecipeVariableDependency env U registry target available index need.profile) :
    ∀ index need, (index, need) ∈ required →
      RecipeVariableDependency env U registry target available index need.profile := by
  induction transfer with
  | nil => intro _ _ member; cases member
  | cons query tail ih =>
    intro index need member
    rcases List.mem_cons.mp member with equal | member
    · cases equal
      exact SortableVariableTrace.replayDependency (.legacy query.variableTrace)
        (fun i requested selected => resources i requested (List.mem_append_left _ selected))
    · exact ih (fun i requested selected => resources i requested (List.mem_append_right _ selected))
        index need member

theorem RecipeVariableDependency.reindex
    (same : ∀ need, need ∈ first index ↔ need ∈ second other)
    (dependency : RecipeVariableDependency env U registry target first index profile) :
    RecipeVariableDependency env U registry target second other profile := by
  obtain ⟨fp, ⟨trace⟩, resources⟩ := dependency
  refine ⟨fp.map (fun entry => (other, entry.2)), traceRename trace (fun _ => other), ?_⟩
  intro i need member
  obtain ⟨⟨oldIndex, oldNeed⟩, original, equal⟩ := List.mem_map.mp member
  cases equal
  have indexEq := trace.indices original
  subst oldIndex
  exact (same oldNeed).mp (resources index oldNeed original)

private theorem piAt
    {firstDomain secondDomain firstBody secondBody : {n : Nat} → Profile n → Valuation → Prop}
    (domain : ∀ {n} (p : Profile n), firstDomain p first ↔ secondDomain p second)
    (body : ∀ {n} (p : Profile n) head,
      firstBody p (Valuation.push head first) ↔ secondBody p (Valuation.push head second))
    {atom : Atom n} :
    RecipePiDependency firstDomain firstBody first atom ↔
      RecipePiDependency secondDomain secondBody second atom := by
  induction n with
  | zero => rfl
  | succ n ih =>
    cases atom with
    | pi A B support rows => simp only [RecipePiDependency, domain, body]
    | pad atom => exact ih
    | _ => rfl

/-- Source-variable renaming changes only the corresponding finite table
indices, also beneath every pending Pi binder. -/
theorem RecipeDependencyProfile.sourceLift
    (rename : Lift) {profile : Profile n} :
    RecipeDependencyProfile env U registry target (expression.lift' rename) profile available ↔
      RecipeDependencyProfile env U registry target expression profile
        (fun index => available (rename.liftVar index)) := by
  induction expression generalizing n available rename with
  | bvar index =>
    simp only [VExpr.lift', RecipeDependencyProfile]
    constructor
    · exact RecipeVariableDependency.reindex (fun _ => Iff.rfl)
    · exact RecipeVariableDependency.reindex (fun _ => Iff.rfl)
  | forallE A B domainIH bodyIH =>
    simp only [VExpr.lift', RecipeDependencyProfile]
    have bodies : ∀ {n} (p : Profile n) head,
        RecipeDependencyProfile env U registry target (B.lift' rename.cons) p
          (Valuation.push head available) ↔
        RecipeDependencyProfile env U registry target B p
          (Valuation.push head (fun index => available (rename.liftVar index))) := by
      intro n p head
      have answer := bodyIH (n := n) (profile := p) (available := Valuation.push head available) rename.cons
      have table : (fun index => Valuation.push head available (rename.cons.liftVar index)) =
          Valuation.push head (fun index => available (rename.liftVar index)) := by
        funext index
        cases index <;> rfl
      rw [table] at answer
      exact answer
    constructor <;> intro evidence atom member
    · exact (piAt (fun p => domainIH rename) bodies).mp (evidence atom member)
    · exact (piAt (fun p => domainIH rename) bodies).mpr (evidence atom member)
  | _ => simp only [VExpr.lift', RecipeDependencyProfile]

/-- The fixed-body recipe introduces no dependency on its discarded binder.
This follows from syntactic lifting, including nested Pi binders. -/
theorem RecipeDependencyProfile.dropUnusedHead
    {profile : Profile n}
    (dependency : RecipeDependencyProfile env U registry target expression.lift profile
      (Valuation.push head available)) :
    RecipeDependencyProfile env U registry target expression profile available := by
  rw [VExpr.lift_eq_lift'] at dependency
  exact (RecipeDependencyProfile.sourceLift (.skip .refl)).mp dependency

theorem recipeDependencyInputs.closed (closed : available.AtomClosed) :
    (Valuation.push (recipeDependencyInputs profile) available).AtomClosed :=
  Valuation.push_atomized_closed closed [⟨_, profile⟩]

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
