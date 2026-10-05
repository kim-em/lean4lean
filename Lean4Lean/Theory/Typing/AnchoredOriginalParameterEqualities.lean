import Lean4Lean.Theory.Typing.AnchoredOriginalDerivation
import Lean4Lean.Theory.Typing.ConstantHeaderProvenance

/-! Original finite declaration-parameter equality trees. The two legs are
retained separately at their actual checking environments. Reification uses
only Ordered strengthening, never uniqueness of typing or context-chain
transitivity. -/
namespace Lean4Lean.AnchoredSource.OriginalClosureMeasure
open VExpr VEnv
set_option backward.isDefEq.respectTransparency false

structure ParameterEqualityRoot (env : VEnv) (U : Nat) where
  source : List VExpr
  context : ContextDerivation env U source
  left : VExpr
  right : VExpr
  assigned : VExpr
  original : Derivation env U source left right assigned

inductive OriginalContextEquality (env : VEnv) (U : Nat) : List VExpr → List VExpr → Type where
  | nil : OriginalContextEquality env U [] []
  | cons (tail : OriginalContextEquality env U source destination)
      (original : Derivation env U source left right (.sort level)) :
      OriginalContextEquality env U (left :: source) (right :: destination)

namespace OriginalContextEquality

def context : OriginalContextEquality env U source destination → ContextDerivation env U source
  | .nil => .nil
  | .cons tail original => .cons tail.context (.left original)

def roots : OriginalContextEquality env U source destination → List (ParameterEqualityRoot env U)
  | .nil => []
  | .cons tail original => ⟨_, tail.context, _, _, _, original⟩ :: tail.roots

theorem roots_length (equalities : OriginalContextEquality env U source destination) :
    equalities.roots.length = source.length := by
  induction equalities <;> simp_all [roots]

theorem length_eq (equalities : OriginalContextEquality env U source destination) :
    source.length = destination.length := by
  induction equalities <;> simp_all

theorem reify (ordered : env.Ordered) (equality : IsDefEqCtx env U [] source destination) :
    Nonempty (OriginalContextEquality env U source destination) := by
  induction equality with
  | zero => exact ⟨.nil⟩
  | succ previous equality ih =>
    obtain ⟨tail⟩ := ih
    obtain ⟨original⟩ := Derivation.reify (equality.strong ordered previous.isType)
    exact ⟨.cons tail original⟩

/-- Each selected universe instance gets the original instantiated equality
proof, including its exact instantiated source prefix. No bound uniform in
all universe instances is asserted. -/
theorem reifyInstance (ordered : env.Ordered)
    (equality : IsDefEqCtx env sourceU [] source destination)
    (levelsWF : ∀ level ∈ levels, level.WF U) :
    Nonempty (OriginalContextEquality env U
      (source.map (VExpr.instL levels)) (destination.map (VExpr.instL levels))) := by
  induction equality with
  | zero => exact ⟨.nil⟩
  | succ previous equality ih =>
    obtain ⟨tail⟩ := ih
    obtain ⟨original⟩ := Derivation.reify ((equality.strong ordered previous.isType).instL levelsWF)
    exact ⟨.cons tail original⟩

/-- Compare the common original telescope at two equivalent universe
instances. Every cell keeps the LEFT instantiated original prefix and its
actual sort; no syntactic equality of the universe lists is assumed. -/
theorem universeInstance (ordered : env.Ordered)
    (equalities : OriginalContextEquality env sourceU source destination)
    (leftWF : ∀ level ∈ leftLevels, level.WF U)
    (rightWF : ∀ level ∈ rightLevels, level.WF U)
    (equivalent : List.Forall₂ (· ≈ ·) leftLevels rightLevels) :
    Nonempty (OriginalContextEquality env U
      (source.map (VExpr.instL leftLevels)) (source.map (VExpr.instL rightLevels))) := by
  induction equalities with
  | nil => exact ⟨.nil⟩
  | @cons source destination A B level previous original ih =>
    obtain ⟨tail⟩ := ih
    have typed := original.forget.hasType.1.instL leftWF
    have changed := EqUpToLevels.defeq ordered ordered.strong tail.context.forget typed
      (EqUpToLevels.refl tail.context.forget.levelWF typed).1
      (EqUpToLevels.instL_expr A leftWF rightWF equivalent)
    obtain ⟨cell⟩ := Derivation.reify changed
    exact ⟨.cons tail cell⟩

end OriginalContextEquality

/-- A raw normalization certificate is reified at the exact declaration
stage and universe instance; its original assigned type is preserved. -/
theorem ParameterEqualityRoot.normalizationInstance
    {left right assigned : VExpr}
    (ordered : env.Ordered)
    (equality : env.IsDefEq sourceU [] left right assigned)
    (levelsWF : ∀ level ∈ levels, level.WF U) :
    Nonempty (Derivation env U [] (left.instL levels) (right.instL levels) (assigned.instL levels)) :=
  Derivation.reify ((VEnv.IsDefEq.strong (Γ := []) ordered (by trivial) equality).instL levelsWF)

/-- Parameter conversion roots in the family-only stage are strictly earlier
than any registered projection: an actual constructor is fresh at that
stage and present in the final environment. No installation-order equality
between two independently supplied Ordered proofs is needed. -/
theorem parameterStage_count_lt
    {base env : VEnv} {name : Lean.Name} {value : VConstant}
    (earlier : base.Ordered) (later : env.Ordered) (below : base ≤ env)
    (fresh : base.constants name = none) (present : env.constants name = some value) :
    earlier.constantCount < later.constantCount := by
  let source := Classical.choice earlier.constantDomain
  let target := Classical.choice later.constantDomain
  have absent : name ∉ source.names := by
    intro member
    obtain ⟨old, lookup⟩ := (source.present name).mp member
    rw [fresh] at lookup
    cases lookup
  have unique : (name :: source.names).Nodup := List.nodup_cons.mpr ⟨absent, source.nodup⟩
  have bound := unique.length_le_of_subset (l₂ := target.names) (by
    intro selected member
    rcases List.mem_cons.mp member with rfl | member
    · exact (target.present selected).mpr ⟨value, present⟩
    · obtain ⟨old, lookup⟩ := (source.present selected).mp member
      exact (target.present selected).mpr ⟨old, below.constants lookup⟩)
  exact Nat.lt_of_succ_le bound

end Lean4Lean.AnchoredSource.OriginalClosureMeasure
