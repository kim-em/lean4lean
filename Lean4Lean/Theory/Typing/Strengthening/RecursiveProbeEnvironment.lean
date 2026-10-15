import Lean4Lean.Theory.Typing.Strengthening.RecursiveDomainEnvironment

/-! # Recursive types retaining an arbitrary proposition parameter

The admitted family `R P := R P → (P → Prop)` supports non-proof diagonal
self-application while retaining `P` in its result type. It is used to test the
strength of common-mode paired substitution, not to assume strengthening.
-/
namespace Lean4Lean.VEnv.Strengthening.RecursiveProbe
open _root_.Lean4Lean _root_.Lean4Lean.VExpr

def familyType : VExpr := .forallE (.sort .zero) (.sort (.succ .zero))
def result (P : VExpr) : VExpr := .forallE P (.sort .zero)
def domain (c : Name) (P : VExpr) : VExpr := .app (.const c []) P
def unfolded (c : Name) (P : VExpr) : VExpr := .forallE (domain c P) (result P).lift

def familyValue (c : Name) : VExpr :=
  .lam (.sort .zero) (.forallE (domain c (.bvar 0)) (result (.bvar 1)))
def declaration (c : Name) : VDefVal where
  name := c
  uvars := 0
  type := familyType
  value := familyValue c

def stub (base : VEnv) (c : Name) : VEnv :=
  { base with constants := fun n => if c = n then some (declaration c).toVConstant else base.constants n }
def extended (base : VEnv) (c : Name) : VEnv := (stub base c).addDefEq (declaration c).toDefEq

/-- The result of a recursive loop is a function into Prop, hence lives in Type. -/
theorem result_typed {env : VEnv} (hP : env.HasType U Γ P (.sort .zero)) :
    env.HasType U Γ (result P) (.sort (.succ .zero)) :=
  (IsDefEq.sortDF (by trivial) (by trivial) VLevel.zero_imax).defeq
    (HasType.forallE hP (HasType.sort (by trivial)))

/-- The temporary block entry suffices to type the recursive family. -/
theorem family_typed {env : VEnv} (hc : env.constants c = some (declaration c).toVConstant)
    (U : Nat) (Γ : List VExpr) : env.HasType U Γ (.const c []) familyType := by
  have H := HasType.const (ls := []) hc (by simp) rfl (Γ := Γ) (U := U)
  simpa only [declaration, familyType, instL, List.map_nil, VLevel.inst] using H

private theorem value_typed {env : VEnv} (hc : env.constants c = some (declaration c).toVConstant) :
    env.HasType 0 [] (familyValue c) familyType := by
  have hP : env.HasType 0 [.sort .zero] (.bvar 0) (.sort .zero) := .bvar .zero
  have hD := (family_typed hc 0 [.sort .zero]).app hP
  have hP' : env.HasType 0 [domain c (.bvar 0), .sort .zero] (.bvar 1) (.sort .zero) :=
    .bvar (.succ .zero)
  have hPi := HasType.forallE hD (result_typed hP')
  have hPi' := (IsDefEq.sortDF (by trivial) (by trivial) VLevel.imax_self).defeq hPi
  exact .lam (HasType.sort (by trivial)) hPi'

/-- This recursive family is admitted without its equation while checking the
value, exactly as required by the mutual-definition rule. -/
theorem declaration_wf (hfresh : base.constants c = none) :
    VDecl.WF base (.mutualDef [declaration c]) (extended base c) := by
  apply VDecl.WF.mutualDef (env' := stub base c)
  · intro ci hci
    simp only [List.mem_singleton] at hci
    subst ci
    exact ⟨_, HasType.forallE (HasType.sort (by trivial)) (HasType.sort (by trivial))⟩
  · simp [VEnv.addConsts, VEnv.addConst, declaration, hfresh, stub]
  · intro ci hci
    simp only [List.mem_singleton] at hci
    subst ci
    exact value_typed (by simp [stub])

/-- Installing the parameter-retaining recursion preserves well-formedness. -/
theorem extended_wf (hbase : base.WF) (hfresh : base.constants c = none) : (extended base c).WF := by
  obtain ⟨ds, hds⟩ := hbase
  exact ⟨_, .decl (declaration_wf hfresh) hds⟩

/-- The test family can be installed in a canonical-Eq environment. -/
theorem extended_canonicalEq (heq : base.HasCanonicalEq) (hfresh : base.constants c = none) :
    (extended base c).HasCanonicalEq := heq.mono (declaration_wf hfresh).le

/-- The actual stored equation is available at every context and universe bound. -/
theorem equation (U : Nat) (Γ : List VExpr) :
    (extended base c).IsDefEq U Γ (.const c []) (familyValue c) familyType := by
  have H := IsDefEq.extra (env := extended base c) (Γ := Γ) (uvars := U)
    (df := (declaration c).toDefEq) (ls := []) (.inl rfl) (by simp) rfl
  simpa [VDefVal.toDefEq, declaration, familyType, familyValue, domain, result,
    instL, VLevel.params, VLevel.inst] using H

end Lean4Lean.VEnv.Strengthening.RecursiveProbe
