import Lean4Lean.Theory.Typing.Strengthening.GuardedEtaSyntax

/-! # A recursive type with a function-valued result

`D := D → (Prop → Prop)` is admitted by the mutual-definition rule. Its value is
checked before installing the equation, and extending a canonical-Eq environment
preserves canonical Eq. The resulting loops test comparison repair only.
-/
namespace Lean4Lean.VEnv.Strengthening.GuardedEta
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Developments

def resultType : VExpr := .forallE prop prop
def domainValue (c : Name) : VExpr := .forallE (domain c) resultType
def declaration (c : Name) : VDefVal where
  name := c
  uvars := 0
  type := .sort (.succ .zero)
  value := domainValue c

def stub (base : VEnv) (c : Name) : VEnv :=
  { base with constants := fun n => if c = n then some (declaration c).toVConstant else base.constants n }
def extended (base : VEnv) (c : Name) : VEnv := (stub base c).addDefEq (declaration c).toDefEq

/-- The recursive constant is typed from the temporary block's constant entry. -/
theorem domain_typed {env : VEnv} (hc : env.constants c = some (declaration c).toVConstant)
    (U : Nat) (Γ : List VExpr) : env.HasType U Γ (domain c) (.sort (.succ .zero)) := by
  have h := HasType.const (ls := []) hc (by simp) rfl (Γ := Γ) (U := U)
  simpa only [declaration, domain, instL, VLevel.inst] using h

theorem result_typed (env : VEnv) (U : Nat) (Γ : List VExpr) :
    env.HasType U Γ resultType (.sort (.succ .zero)) := tower_typed env U Γ 1

private theorem value_typed {env : VEnv} (hc : env.constants c = some (declaration c).toVConstant) :
    env.HasType 0 [] (domainValue c) (.sort (.succ .zero)) := by
  have h := HasType.forallE (domain_typed hc 0 []) (result_typed env 0 [domain c])
  exact (IsDefEq.sortDF (l := .imax (.succ .zero) (.succ .zero)) (by trivial)
    (by trivial) VLevel.imax_self).defeq h

/-- No use of the new recursive equation is needed to type its defining value. -/
theorem declaration_wf (hfresh : base.constants c = none) :
    VDecl.WF base (.mutualDef [declaration c]) (extended base c) := by
  apply VDecl.WF.mutualDef (env' := stub base c)
  · intro ci hci
    simp only [List.mem_singleton] at hci
    subst ci
    exact ⟨_, HasType.sort (by trivial)⟩
  · simp [VEnv.addConsts, VEnv.addConst, declaration, hfresh, stub]
  · intro ci hci
    simp only [List.mem_singleton] at hci
    subst ci
    exact value_typed (by simp [stub])

theorem extended_wf (hbase : base.WF) (hfresh : base.constants c = none) : (extended base c).WF := by
  obtain ⟨ds, hds⟩ := hbase
  exact ⟨_, .decl (declaration_wf hfresh) hds⟩

theorem extended_canonicalEq (heq : base.HasCanonicalEq) (hfresh : base.constants c = none) :
    (extended base c).HasCanonicalEq := heq.mono (declaration_wf hfresh).le

/-- The recursive equation is available only after the declaration is installed. -/
theorem equation (U : Nat) (Γ : List VExpr) :
    (extended base c).IsDefEq U Γ (domain c) (domainValue c) (.sort (.succ .zero)) := by
  have h := IsDefEq.extra (env := extended base c) (Γ := Γ) (uvars := U)
    (df := (declaration c).toDefEq) (ls := []) (.inl rfl) (by simp) rfl
  simpa [VDefVal.toDefEq, declaration, domainValue, domain, resultType, prop,
    instL, VLevel.params, VLevel.inst] using h

end Lean4Lean.VEnv.Strengthening.GuardedEta
