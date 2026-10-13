import Lean4Lean.Theory.Typing.Strengthening.DevelopmentRounds
import Lean4Lean.Theory.CanonicalEq

/-! # A recursive type family admitted by mutual definitions

The declaration `R f := (R f → Prop)` supplies typed self-application at a type
universe. It is used to test beta-only comparison repair, not as a counterexample
to strengthening. The declaration extends any well-formed environment at a fresh
name and preserves canonical Eq when present.
-/
namespace Lean4Lean.VEnv.Strengthening.RecursiveDomain
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Developments

def argType : VExpr := tower 1
def familyType : VExpr := .forallE argType (.sort (.succ .zero))
def familyValue (c : Name) : VExpr :=
  .lam argType (.forallE (.app (.const c []) (.bvar 0)) (.sort .zero))
def declaration (c : Name) : VDefVal where
  name := c
  uvars := 0
  type := familyType
  value := familyValue c

def stub (base : VEnv) (c : Name) : VEnv :=
  { base with constants := fun n => if c = n then some (declaration c).toVConstant else base.constants n }
def extended (base : VEnv) (c : Name) : VEnv := (stub base c).addDefEq (declaration c).toDefEq

theorem argType_typed (env : VEnv) (U : Nat) (Γ : List VExpr) :
    env.HasType U Γ argType (.sort (.succ .zero)) := tower_typed env U Γ 1

private theorem familyType_typed (env : VEnv) (U : Nat) (Γ : List VExpr) :
    env.HasType U Γ familyType (.sort (.imax (.succ .zero) (.succ (.succ .zero)))) :=
  .forallE (argType_typed env U Γ) (.sort (by trivial))

/-- The family can be typed in the temporary block environment before its equation
is installed, as required by `VDecl.WF.mutualDef`. -/
theorem family_typed {env : VEnv} (hc : env.constants c = some (declaration c).toVConstant)
    (U : Nat) (Γ : List VExpr) : env.HasType U Γ (.const c []) familyType := by
  have h := HasType.const (ls := []) hc (by simp) rfl (Γ := Γ) (U := U)
  simpa only [declaration, familyType, argType, tower, instL, List.map_nil, VLevel.inst] using h

private theorem value_typed {env : VEnv} (hc : env.constants c = some (declaration c).toVConstant) :
    env.HasType 0 [] (familyValue c) familyType := by
  have hv : env.HasType 0 [argType] (.bvar 0) argType := by
    have h : env.HasType 0 [argType] (.bvar 0) argType.lift := .bvar .zero
    simpa only [argType, lift, tower_liftN] using h
  have hD := (family_typed hc 0 [argType]).app hv
  have hPi := HasType.forallE hD (HasType.sort (l := .zero) (by trivial))
  have hPi' := (IsDefEq.sortDF (l := .imax (.succ .zero) (.succ .zero))
    (by trivial) (by trivial) VLevel.imax_self).defeq hPi
  exact .lam (argType_typed env 0 []) hPi'

private theorem add_block (hfresh : base.constants c = none) :
    base.addConsts [declaration c] = some (stub base c) := by
  simp [VEnv.addConsts, VEnv.addConst, declaration, hfresh, stub]

/-- The recursive family is an actual well-formed declaration, without assuming
its own equation while checking the value. -/
theorem declaration_wf (hfresh : base.constants c = none) :
    VDecl.WF base (.mutualDef [declaration c]) (extended base c) := by
  apply VDecl.WF.mutualDef (env' := stub base c)
  · intro ci hci
    simp only [List.mem_singleton] at hci
    subst ci
    exact ⟨_, familyType_typed base 0 []⟩
  · exact add_block hfresh
  · intro ci hci
    simp only [List.mem_singleton] at hci
    subst ci
    exact value_typed (by simp [stub])

/-- Installing this family preserves environment well-formedness. -/
theorem extended_wf (hbase : base.WF) (hfresh : base.constants c = none) : (extended base c).WF := by
  obtain ⟨ds, hds⟩ := hbase
  exact ⟨_, .decl (declaration_wf hfresh) hds⟩

theorem extended_le (hfresh : base.constants c = none) : base ≤ extended base c :=
  (declaration_wf hfresh).le

/-- The test declaration also preserves canonical equality, so its recursive
behavior is not an artifact of environments without Eq. -/
theorem extended_canonicalEq (heq : base.HasCanonicalEq) (hfresh : base.constants c = none) :
    (extended base c).HasCanonicalEq := heq.mono (extended_le hfresh)

/-- The defining equation available after the block is installed. -/
theorem equation (U : Nat) (Γ : List VExpr) :
    (extended base c).IsDefEq U Γ (.const c []) (familyValue c) familyType := by
  have h := IsDefEq.extra (env := extended base c) (Γ := Γ) (uvars := U)
    (df := (declaration c).toDefEq) (ls := []) (.inl rfl) (by simp) rfl
  simpa [VDefVal.toDefEq, declaration, familyType, familyValue, argType, tower,
    instL, VLevel.params, VLevel.inst] using h

end Lean4Lean.VEnv.Strengthening.RecursiveDomain
