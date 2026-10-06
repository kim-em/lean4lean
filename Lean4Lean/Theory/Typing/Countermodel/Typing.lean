import Lean4Lean.Theory.Typing.Countermodel.Syntax
import Lean4Lean.Theory.Typing.Lemmas

/-!
# Typing derivations for the countermodel environment

All derivations are generic in an environment `E` that contains the relevant
constants with the expected types, so the same proofs serve every stage of
the installation and the final environment.
-/

namespace Lean4Lean.Countermodel

open VEnv

/-! ## Generated recursor and iota rule, in closed form -/

def app4 (f a b c d : VExpr) : VExpr := .app (.app (.app (.app f a) b) c) d

def ruleRhsBody : VExpr := .app (.app (.bvar 2) (.bvar 1)) (.bvar 0)

namespace FamSpec
variable (sp : FamSpec)

/-- `fam a b c`. -/
def famApp (a b c : VExpr) : VExpr := .app (.app (.app sp.eFam a) b) c

/-- Motive type `(n : C) → (v : F n) → (w : F n) → fam n v w → Sort u`. -/
def motiveType : VExpr :=
  .forallE eC (.forallE (.app eF (.bvar 0)) (.forallE (.app eF (.bvar 1))
    (.forallE (sp.famApp (.bvar 2) (.bvar 1) (.bvar 0)) (.sort (.param 0)))))

/-- `ctor v h`. -/
def ctorApp (v h : VExpr) : VExpr := .app (.app sp.eCtor v) h

/-- Minor premise type, below the motive (index 0). -/
def minorType : VExpr :=
  .forallE eFc (.forallE (.app eP (.bvar 0))
    (app4 (.bvar 2) ec (.bvar 1) (.app sp.eMap (.bvar 1)) (sp.ctorApp (.bvar 1) (.bvar 0))))

def recType : VExpr :=
  .forallE sp.motiveType (.forallE sp.minorType (.forallE eC (.forallE (.app eF (.bvar 0))
    (.forallE (.app eF (.bvar 1)) (.forallE (sp.famApp (.bvar 2) (.bvar 1) (.bvar 0))
      (app4 (.bvar 5) (.bvar 3) (.bvar 2) (.bvar 1) (.bvar 0)))))))

def recVal : VConstVal := { name := sp.recName, uvars := 1, type := sp.recType }

theorem recursors_eq : sp.inst.recursors = [sp.recVal] := rfl

def eRec : VExpr := .const sp.recName [.param 0]

/-- The iota rule body below `M, minor, v, h`. -/
def ruleLhsBody : VExpr :=
  .app (app4 (.app sp.eRec (.bvar 3)) (.bvar 2) ec (.bvar 1) (.app sp.eMap (.bvar 1)))
    (sp.ctorApp (.bvar 1) (.bvar 0))

def ruleTypeBody : VExpr :=
  app4 (.bvar 3) ec (.bvar 1) (.app sp.eMap (.bvar 1)) (sp.ctorApp (.bvar 1) (.bvar 0))

def ruleDomains : List VExpr := [sp.motiveType, sp.minorType, eFc, .app eP (.bvar 0)]

def rule : VDefEq where
  uvars := 1
  lhs := VExpr.wrapLams sp.ruleDomains sp.ruleLhsBody
  rhs := VExpr.wrapLams sp.ruleDomains ruleRhsBody
  type := VExpr.wrapForalls sp.ruleDomains sp.ruleTypeBody

end FamSpec

/-! ## Typing combinators -/

/-- The base constants are present with their declared types. -/
structure Base (E : VEnv) : Prop where
  C : E.constants nC = some ⟨0, typeC⟩
  F : E.constants nF = some ⟨0, typeF⟩
  c : E.constants nc = some ⟨0, typec⟩
  P : E.constants nP = some ⟨0, typeP⟩

section
variable {E : VEnv} {U : Nat} {Γ : List VExpr}

theorem const0 {n : Name} {T : VExpr} (h : E.constants n = some ⟨0, T⟩)
    (hT : T.instL [] = T) : E.HasType U Γ (.const n []) T := by
  have := HasType.const (U := U) (Γ := Γ) (ls := []) h (by simp) rfl
  exact hT ▸ this

theorem app' {f a A B T : VExpr} (h1 : E.HasType U Γ f (.forallE A B))
    (h2 : E.HasType U Γ a A) (h : B.inst a = T) : E.HasType U Γ (.app f a) T :=
  h ▸ HasType.app h1 h2

variable (B : Base E)
include B

theorem tyC : E.HasType U Γ eC typeC := const0 B.C rfl
theorem tyc : E.HasType U Γ ec eC := const0 B.c rfl

theorem tyFapp {n : VExpr} (hn : E.HasType U Γ n eC) :
    E.HasType U Γ (.app eF n) (.sort lvl1) := app' (const0 B.F rfl) hn rfl

theorem tyFc : E.HasType U Γ eFc (.sort lvl1) := tyFapp B (tyc B)

theorem tyPapp {v : VExpr} (hv : E.HasType U Γ v eFc) :
    E.HasType U Γ (.app eP v) (.sort .zero) := app' (const0 B.P rfl) hv rfl

theorem tySort1 : E.HasType U Γ (.sort lvl1) (.sort (.succ lvl1)) :=
  HasType.sort (by simp [lvl1, VLevel.WF])

theorem tySort0 : E.HasType U Γ (.sort .zero) (.sort lvl1) :=
  HasType.sort (by simp [VLevel.WF])

end

namespace FamSpec
variable (sp : FamSpec) {E : VEnv} {U : Nat} {Γ : List VExpr}

/-- The family-specific constants are present with their declared types. -/
structure MapOK (E : VEnv) : Prop where
  map : E.constants sp.map = some ⟨0, typeMap⟩

structure FamOK (E : VEnv) : Prop where
  fam : E.constants sp.fam = some ⟨0, typeFam⟩

structure CtorOK (E : VEnv) : Prop where
  ctor : E.constants sp.ctor = some ⟨0, sp.ctorType⟩

structure RecOK (E : VEnv) : Prop where
  recursor : E.constants sp.recName = some ⟨1, sp.recType⟩

variable {sp}

theorem tyMapApp (hm : sp.MapOK E) {v : VExpr} (hv : E.HasType U Γ v eFc) :
    E.HasType U Γ (.app sp.eMap v) eFc := app' (const0 hm.map rfl) hv rfl

theorem tyFamApp (hf : sp.FamOK E) {n v w : VExpr} (hn : E.HasType U Γ n eC)
    (hv : E.HasType U Γ v (.app eF n)) (hw : E.HasType U Γ w (.app eF n)) :
    E.HasType U Γ (sp.famApp n v w) (.sort .zero) := by
  have h1 : E.HasType U Γ (.app sp.eFam n)
      (.forallE (.app eF n) (.forallE (.app eF n.lift) (.sort .zero))) :=
    app' (const0 hf.fam rfl) hn (by simp [VExpr.inst, eF])
  have h2 : E.HasType U Γ (.app (.app sp.eFam n) v)
      (.forallE (.app eF n) (.sort .zero)) :=
    app' h1 hv (by simp [VExpr.inst, VExpr.inst_lift, eF])
  exact app' h2 hw rfl

theorem tyCtorApp (hc : sp.CtorOK E) {v h : VExpr} (hv : E.HasType U Γ v eFc)
    (hh : E.HasType U Γ h (.app eP v)) :
    E.HasType U Γ (sp.ctorApp v h) (sp.famApp ec v (.app sp.eMap v)) := by
  have h1 : E.HasType U Γ (.app sp.eCtor v)
      (.forallE (.app eP v) (sp.famApp ec v.lift (.app sp.eMap v.lift))) :=
    app' (const0 hc.ctor rfl) hv (by simp [VExpr.inst, eP, famApp, ec, eFam, eMap, ctorResult])
  exact app' h1 hh (by simp [VExpr.inst, VExpr.inst_lift, famApp, ec, eFam, eMap])

end FamSpec

/-! ## The recursor type and its iota rule -/

namespace FamSpec
variable {sp : FamSpec} {E : VEnv}

/-- The index telescope `n : C, v : F n, w : F n`, innermost first. -/
def idxCtx (Γ : List VExpr) : List VExpr :=
  .app eF (.bvar 1) :: .app eF (.bvar 0) :: eC :: Γ

section
variable (B : Base E) (hf : sp.FamOK E)
include B hf

theorem ty_idx_n {U Γ} : E.HasType U (idxCtx Γ) (.bvar 2) eC :=
  HasType.bvar (.succ (.succ .zero))
theorem ty_idx_v {U Γ} : E.HasType U (idxCtx Γ) (.bvar 1) (.app eF (.bvar 2)) :=
  HasType.bvar (.succ .zero)
theorem ty_idx_w {U Γ} : E.HasType U (idxCtx Γ) (.bvar 0) (.app eF (.bvar 2)) :=
  HasType.bvar .zero

theorem ty_idx_fam {U Γ} :
    E.HasType U (idxCtx Γ) (sp.famApp (.bvar 2) (.bvar 1) (.bvar 0)) (.sort .zero) :=
  tyFamApp hf (ty_idx_n B hf) (ty_idx_v B hf) (ty_idx_w B hf)

/-- The index telescope is a well-formed context extension. -/
theorem ty_idx_F0 {U Γ} : E.HasType U (eC :: Γ) (.app eF (.bvar 0)) (.sort lvl1) :=
  tyFapp B (HasType.bvar .zero)
theorem ty_idx_F1 {U Γ} :
    E.HasType U (.app eF (.bvar 0) :: eC :: Γ) (.app eF (.bvar 1)) (.sort lvl1) :=
  tyFapp B (HasType.bvar (.succ .zero))

theorem ty_motive {Γ} : ∃ u, E.HasType 1 Γ sp.motiveType (.sort u) :=
  ⟨_, .forallE (tyC B) <| .forallE (ty_idx_F0 B hf) <| .forallE (ty_idx_F1 B hf) <|
    .forallE (ty_idx_fam B hf) (HasType.sort (by simp [VLevel.WF]))⟩

end
end FamSpec

namespace FamSpec
variable {sp : FamSpec} {E : VEnv}

section
variable (B : Base E) (hm : sp.MapOK E) (hf : sp.FamOK E) (hc : sp.CtorOK E)
include B hm hf hc

/-- Context of the minor premise body: `h : P v, v : F c, M`. -/
theorem ty_minor_body {Γ} :
    E.HasType 1 (.app eP (.bvar 0) :: eFc :: sp.motiveType :: Γ)
      (app4 (.bvar 2) ec (.bvar 1) (.app sp.eMap (.bvar 1)) (sp.ctorApp (.bvar 1) (.bvar 0)))
      (.sort (.param 0)) := by
  have hM : E.HasType 1 (.app eP (.bvar 0) :: eFc :: sp.motiveType :: Γ) (.bvar 2)
      sp.motiveType := HasType.bvar (.succ (.succ .zero))
  have hv : E.HasType 1 (.app eP (.bvar 0) :: eFc :: sp.motiveType :: Γ) (.bvar 1) eFc :=
    HasType.bvar (.succ .zero)
  have hh : E.HasType 1 (.app eP (.bvar 0) :: eFc :: sp.motiveType :: Γ) (.bvar 0)
      (.app eP (.bvar 1)) := HasType.bvar .zero
  exact HasType.app (HasType.app (HasType.app (HasType.app hM (tyc B)) hv)
    (tyMapApp hm hv)) (tyCtorApp hc hv hh)

theorem ty_minor {Γ} : ∃ u, E.HasType 1 (sp.motiveType :: Γ) sp.minorType (.sort u) :=
  ⟨_, .forallE (tyFc B) <| .forallE (tyPapp B (HasType.bvar .zero)) (ty_minor_body B hm hf hc)⟩

theorem recType_wf : E.IsType 1 [] sp.recType := by
  obtain ⟨_, hM⟩ := ty_motive (Γ := []) B hf
  obtain ⟨_, hm'⟩ := ty_minor (Γ := []) B hm hf hc
  have h5 : E.HasType 1 (sp.famApp (.bvar 2) (.bvar 1) (.bvar 0) :: idxCtx
      [sp.minorType, sp.motiveType]) (.bvar 5) sp.motiveType :=
    HasType.bvar (.succ (.succ (.succ (.succ (.succ .zero)))))
  have h3 : E.HasType 1 (sp.famApp (.bvar 2) (.bvar 1) (.bvar 0) :: idxCtx
      [sp.minorType, sp.motiveType]) (.bvar 3) eC :=
    HasType.bvar (.succ (.succ (.succ .zero)))
  have h2 : E.HasType 1 (sp.famApp (.bvar 2) (.bvar 1) (.bvar 0) :: idxCtx
      [sp.minorType, sp.motiveType]) (.bvar 2) (.app eF (.bvar 3)) :=
    HasType.bvar (.succ (.succ .zero))
  have h1 : E.HasType 1 (sp.famApp (.bvar 2) (.bvar 1) (.bvar 0) :: idxCtx
      [sp.minorType, sp.motiveType]) (.bvar 1) (.app eF (.bvar 3)) :=
    HasType.bvar (.succ .zero)
  have h0 : E.HasType 1 (sp.famApp (.bvar 2) (.bvar 1) (.bvar 0) :: idxCtx
      [sp.minorType, sp.motiveType]) (.bvar 0) (sp.famApp (.bvar 3) (.bvar 2) (.bvar 1)) :=
    HasType.bvar .zero
  have hbody : E.HasType 1 (sp.famApp (.bvar 2) (.bvar 1) (.bvar 0) :: idxCtx
      [sp.minorType, sp.motiveType]) (app4 (.bvar 5) (.bvar 3) (.bvar 2) (.bvar 1) (.bvar 0))
      (.sort (.param 0)) :=
    HasType.app (HasType.app (HasType.app (HasType.app h5 h3) h2) h1) h0
  exact ⟨_, .forallE hM <| .forallE hm' <| .forallE (tyC B) <| .forallE (ty_idx_F0 B hf) <|
    .forallE (ty_idx_F1 B hf) <| .forallE (ty_idx_fam B hf) hbody⟩

end
end FamSpec

namespace FamSpec
variable {sp : FamSpec} {E : VEnv}

/-- Context of the iota rule body: `h : P v, v : F c, minor, M`. -/
def ruleCtx (sp : FamSpec) : List VExpr := [.app eP (.bvar 0), eFc, sp.minorType, sp.motiveType]

section
variable (B : Base E) (hm : sp.MapOK E) (hf : sp.FamOK E) (hc : sp.CtorOK E)
include B hm hf hc

theorem ty_rule_vars :
    E.HasType 1 sp.ruleCtx (.bvar 3) sp.motiveType ∧
    E.HasType 1 sp.ruleCtx (.bvar 2) (sp.minorType.liftN 3) ∧
    E.HasType 1 sp.ruleCtx (.bvar 1) eFc ∧
    E.HasType 1 sp.ruleCtx (.bvar 0) (.app eP (.bvar 1)) :=
  ⟨HasType.bvar (.succ (.succ (.succ .zero))), HasType.bvar (.succ (.succ .zero)),
    HasType.bvar (.succ .zero), HasType.bvar .zero⟩

theorem ty_rule_domains : (∃ u, E.HasType 1 [] sp.motiveType (.sort u)) ∧
    (∃ u, E.HasType 1 [sp.motiveType] sp.minorType (.sort u)) ∧
    E.HasType 1 [sp.minorType, sp.motiveType] eFc (.sort lvl1) ∧
    E.HasType 1 [eFc, sp.minorType, sp.motiveType] (.app eP (.bvar 0)) (.sort .zero) :=
  ⟨ty_motive B hf, ty_minor B hm hf hc, tyFc B, tyPapp B (HasType.bvar .zero)⟩

theorem ty_rule_rhs : E.HasType 1 [] sp.rule.rhs sp.rule.type := by
  obtain ⟨_, h2, h1, h0⟩ := ty_rule_vars (sp := sp) B hm hf hc
  obtain ⟨⟨_, dM⟩, ⟨_, dm⟩, dv, dh⟩ := ty_rule_domains (sp := sp) B hm hf hc
  have hbody : E.HasType 1 sp.ruleCtx ruleRhsBody sp.ruleTypeBody :=
    HasType.app (HasType.app h2 h1) h0
  exact .lam dM <| .lam dm <| .lam dv <| .lam dh hbody

variable (hr : sp.RecOK E)
include hr

theorem ty_rule_lhs : E.HasType 1 [] sp.rule.lhs sp.rule.type := by
  obtain ⟨h3, h2, h1, h0⟩ := ty_rule_vars (sp := sp) B hm hf hc
  obtain ⟨⟨_, dM⟩, ⟨_, dm⟩, dv, dh⟩ := ty_rule_domains (sp := sp) B hm hf hc
  have hrec : E.HasType 1 sp.ruleCtx sp.eRec sp.recType :=
    HasType.const hr.recursor (by simp [VLevel.WF]) rfl
  have hbody : E.HasType 1 sp.ruleCtx sp.ruleLhsBody sp.ruleTypeBody :=
    HasType.app (HasType.app (HasType.app (HasType.app (HasType.app (HasType.app hrec h3) h2)
      (tyc B)) h1) (tyMapApp hm h1)) (tyCtorApp hc h1 h0)
  exact .lam dM <| .lam dm <| .lam dv <| .lam dh hbody

theorem rule_wf : sp.rule.WF E := ⟨ty_rule_lhs B hm hf hc hr, ty_rule_rhs B hm hf hc⟩

end
end FamSpec

/-! ## Declared types of the axioms, the families and the constructors -/

section
variable {E : VEnv} {U : Nat}

theorem typeC_wf : E.IsType U [] typeC := ⟨_, HasType.sort (by simp [lvl1, VLevel.WF])⟩

theorem typeF_wf (hC : E.constants nC = some ⟨0, typeC⟩) : E.IsType U [] typeF :=
  ⟨_, .forallE (const0 hC rfl) (HasType.sort (by simp [lvl1, VLevel.WF]))⟩

theorem typec_wf (hC : E.constants nC = some ⟨0, typeC⟩) : E.IsType U [] typec :=
  ⟨_, const0 hC rfl⟩

theorem tyFc' (hC : E.constants nC = some ⟨0, typeC⟩) (hF : E.constants nF = some ⟨0, typeF⟩)
    (hc : E.constants nc = some ⟨0, typec⟩) {Γ} : E.HasType U Γ eFc (.sort lvl1) :=
  app' (const0 hF rfl) (const0 hc rfl) rfl

theorem typeP_wf (hC : E.constants nC = some ⟨0, typeC⟩) (hF : E.constants nF = some ⟨0, typeF⟩)
    (hc : E.constants nc = some ⟨0, typec⟩) : E.IsType U [] typeP :=
  ⟨_, .forallE (tyFc' hC hF hc) (HasType.sort (by simp [VLevel.WF]))⟩

theorem typeMap_wf (hC : E.constants nC = some ⟨0, typeC⟩) (hF : E.constants nF = some ⟨0, typeF⟩)
    (hc : E.constants nc = some ⟨0, typec⟩) : E.IsType U [] typeMap :=
  ⟨_, .forallE (tyFc' hC hF hc) (tyFc' hC hF hc)⟩

variable (B : Base E)
include B

theorem ty_typeFam_body {Γ} : E.HasType U (eC :: Γ)
    (.forallE (.app eF (.bvar 0)) (.forallE (.app eF (.bvar 1)) (.sort .zero)))
    (.sort (.imax lvl1 (.imax lvl1 lvl1))) :=
  .forallE (tyFapp B (HasType.bvar .zero)) <|
    .forallE (tyFapp B (HasType.bvar (.succ .zero))) (tySort0 B)

theorem typeFam_wf : E.HasType U [] typeFam (.sort (.imax lvl1 (.imax lvl1 (.imax lvl1 lvl1)))) :=
  .forallE (tyC B) (ty_typeFam_body B)

theorem FamSpec.ctorType_wf {sp : FamSpec} (hm : sp.MapOK E) (hf : sp.FamOK E) :
    E.IsType U [] sp.ctorType := by
  have hv : E.HasType U [.app eP (.bvar 0), eFc] (.bvar 1) eFc := HasType.bvar (.succ .zero)
  have hres : E.HasType U [.app eP (.bvar 0), eFc] sp.ctorResult (.sort .zero) :=
    FamSpec.tyFamApp hf (tyc B) hv (FamSpec.tyMapApp hm hv)
  exact ⟨_, .forallE (tyFc B) <| .forallE (tyPapp B (HasType.bvar .zero)) hres⟩

end
end Lean4Lean.Countermodel
