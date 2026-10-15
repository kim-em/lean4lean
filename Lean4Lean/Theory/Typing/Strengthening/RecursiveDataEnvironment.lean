import Lean4Lean.Theory.Typing.Strengthening.RecursiveProbeEnvironment

/-! # A recursive test family with a fixed data result

The admitted family is R P := R P → (P → S), where S is an existing monomorphic
constant of Type. Unlike the previous universe-result test, S need not be a
universe. Rigidity or structure hypotheses are supplied separately when needed;
this declaration alone does not assert consistency or absence of logical collapse.
-/
namespace Lean4Lean.VEnv.Strengthening.RecursiveData
open _root_.Lean4Lean _root_.Lean4Lean.VExpr

abbrev familyType : VExpr := RecursiveProbe.familyType
def result (d : Name) (P : VExpr) : VExpr := .forallE P (.const d [])
def domain (c : Name) (P : VExpr) : VExpr := .app (.const c []) P
def unfolded (c d : Name) (P : VExpr) : VExpr := .forallE (domain c P) (result d P).lift

def familyValue (c d : Name) : VExpr :=
  .lam (.sort .zero) (.forallE (domain c (.bvar 0)) (result d (.bvar 1)))
def declaration (c d : Name) : VDefVal where
  name := c
  uvars := 0
  type := familyType
  value := familyValue c d

def stub (base : VEnv) (c d : Name) : VEnv :=
  { base with constants := fun n => if c = n then some (declaration c d).toVConstant else base.constants n }
def extended (base : VEnv) (c d : Name) : VEnv := (stub base c d).addDefEq (declaration c d).toDefEq

/-- The fixed data type is available in every context from its ordinary entry. -/
theorem data_typed {env : VEnv} (hd : env.constants d = some ⟨0, .sort (.succ .zero)⟩)
    (U : Nat) (Γ : List VExpr) : env.HasType U Γ (.const d []) (.sort (.succ .zero)) := by
  have H := HasType.const (ls := []) hd (by simp) rfl (Γ := Γ) (U := U)
  simpa only [instL, VLevel.inst] using H

/-- A proposition-to-data function has a positive universe, retaining its syntax
under proof erasure even though its argument is a proof. -/
theorem result_typed {env : VEnv} (hd : env.constants d = some ⟨0, .sort (.succ .zero)⟩)
    (hP : env.HasType U Γ P (.sort .zero)) :
    env.HasType U Γ (result d P) (.sort (.succ .zero)) :=
  (IsDefEq.sortDF (by trivial) (by trivial) VLevel.zero_imax).defeq
    (HasType.forallE hP (data_typed hd U (P :: Γ)))

/-- The recursive family is typed using only its temporary constant entry. -/
theorem family_typed {env : VEnv} (hc : env.constants c = some (declaration c d).toVConstant)
    (U : Nat) (Γ : List VExpr) : env.HasType U Γ (.const c []) familyType := by
  have H := HasType.const (ls := []) hc (by simp) rfl (Γ := Γ) (U := U)
  simpa only [declaration, familyType, RecursiveProbe.familyType, instL, VLevel.inst] using H

private theorem value_typed {env : VEnv} (hc : env.constants c = some (declaration c d).toVConstant)
    (hd : env.constants d = some ⟨0, .sort (.succ .zero)⟩) :
    env.HasType 0 [] (familyValue c d) familyType := by
  have hP : env.HasType 0 [.sort .zero] (.bvar 0) (.sort .zero) := .bvar .zero
  have hD := (family_typed hc 0 [.sort .zero]).app hP
  have hP' : env.HasType 0 [domain c (.bvar 0), .sort .zero] (.bvar 1) (.sort .zero) := .bvar (.succ .zero)
  have hPi := HasType.forallE hD (result_typed hd hP')
  have hPi' := (IsDefEq.sortDF (by trivial) (by trivial) VLevel.imax_self).defeq hPi
  exact .lam (HasType.sort (by trivial)) hPi'

/-- The fixed-data recursion is admitted by the actual mutual-definition rule,
with the value checked before its equation is installed. -/
theorem declaration_wf (hfresh : base.constants c = none)
    (hd : base.constants d = some ⟨0, .sort (.succ .zero)⟩) :
    VDecl.WF base (.mutualDef [declaration c d]) (extended base c d) := by
  have hne : c ≠ d := by intro E; subst d; rw [hfresh] at hd; cases hd
  apply VDecl.WF.mutualDef (env' := stub base c d)
  · intro ci hci
    simp only [List.mem_singleton] at hci
    subst ci
    exact ⟨_, HasType.forallE (HasType.sort (by trivial)) (HasType.sort (by trivial))⟩
  · simp [VEnv.addConsts, VEnv.addConst, declaration, hfresh, stub]
  · intro ci hci
    simp only [List.mem_singleton] at hci
    subst ci
    exact value_typed (by simp [stub]) (by simp [stub, hne, hd])

/-- Installing the recursive family preserves well-formedness. -/
theorem extended_wf (hbase : base.WF) (hfresh : base.constants c = none)
    (hd : base.constants d = some ⟨0, .sort (.succ .zero)⟩) : (extended base c d).WF := by
  obtain ⟨ds, hds⟩ := hbase
  exact ⟨_, .decl (declaration_wf hfresh hd) hds⟩

/-- The actual fixed-data extension preserves canonical Eq. -/
theorem extended_canonicalEq (heq : base.HasCanonicalEq) (hfresh : base.constants c = none)
    (hd : base.constants d = some ⟨0, .sort (.succ .zero)⟩) :
    (extended base c d).HasCanonicalEq := heq.mono (declaration_wf hfresh hd).le

/-- The stored equation is available at every context and universe bound. -/
theorem equation (U : Nat) (Γ : List VExpr) :
    (extended base c d).IsDefEq U Γ (.const c []) (familyValue c d) familyType := by
  have H := IsDefEq.extra (env := extended base c d) (Γ := Γ) (uvars := U)
    (df := (declaration c d).toDefEq) (ls := []) (.inl rfl) (by simp) rfl
  simpa [VDefVal.toDefEq, declaration, familyType, RecursiveProbe.familyType, familyValue,
    domain, result, instL, VLevel.params, VLevel.inst] using H

end Lean4Lean.VEnv.Strengthening.RecursiveData
