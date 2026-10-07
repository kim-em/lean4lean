import Lean4Lean.Theory.Typing.Env

/-!
# Concrete syntax of the strengthening countermodel

The environment of `docs/inductives/STRENGTHENING.md`:

```text
C : Type
F : C → Type
c : C
P : F c → Prop
leftMap rightMap : F c → F c
inductive I : (n : C) → F n → F n → Prop
  | mk (v : F c) (h : P v) : I c v (leftMap v)
inductive J : (n : C) → F n → F n → Prop
  | mk (v : F c) (h : P v) : J c v (rightMap v)
```

Both families are installed by `VDecl.induct` with the native recursors and
iota rules produced by the signature generator (`InductiveSignature.Instance`).
The abstract `.elim` schema route cannot be used: `CaseSchema.Permission`
requires `target ≈ 0` for a `Prop` family, so it gives no large elimination.

The two families differ only in the name of the family, its constructor and
the index map, so everything is stated for a `FamSpec`.
-/

namespace Lean4Lean.Countermodel

open InductiveSignature

/-! ## Names and closed constants -/

def nC : Name := `CM.C
def nF : Name := `CM.F
def nc : Name := `CM.c
def nP : Name := `CM.P
def nL : Name := `CM.leftMap
def nR : Name := `CM.rightMap

def eC : VExpr := .const nC []
def eF : VExpr := .const nF []
def ec : VExpr := .const nc []
def eP : VExpr := .const nP []

/-- `F c`. -/
def eFc : VExpr := .app eF ec

def lvl1 : VLevel := .succ .zero

def typeC : VExpr := .sort lvl1
def typeF : VExpr := .forallE eC (.sort lvl1)
def typec : VExpr := eC
def typeP : VExpr := .forallE eFc (.sort .zero)
def typeMap : VExpr := .forallE eFc eFc

/-- `(n : C) → F n → F n → Prop`, the common type of both families. -/
def typeFam : VExpr :=
  .forallE eC (.forallE (.app eF (.bvar 0)) (.forallE (.app eF (.bvar 1)) (.sort .zero)))

/-- The data distinguishing the two singleton families. -/
structure FamSpec where
  fam : Name
  ctor : Name
  map : Name

def specI : FamSpec := ⟨`CM.I, `CM.I.mk, nL⟩
def specJ : FamSpec := ⟨`CM.J, `CM.J.mk, nR⟩

namespace FamSpec
variable (sp : FamSpec)

def recName : Name := sp.fam.str "rec"
def eFam : VExpr := .const sp.fam []
def eCtor : VExpr := .const sp.ctor []
def eMap : VExpr := .const sp.map []

/-- The constructor result `fam c v (map v)` below the binders `v` (index 1)
and `h` (index 0). -/
def ctorResult : VExpr :=
  .app (.app (.app sp.eFam ec) (.bvar 1)) (.app sp.eMap (.bvar 1))

/-- `(v : F c) → P v → fam c v (map v)`. -/
def ctorType : VExpr :=
  .forallE eFc (.forallE (.app eP (.bvar 0)) sp.ctorResult)

/-! ## Signature and generator instance -/

def sigCtor : Constructor 1 :=
  Constructor.mk sp.ctor ⟨0, Nat.zero_lt_one⟩
    [.external eFc, .external (.app eP (.bvar 0))]
    [ec, .bvar 1, .app sp.eMap (.bvar 1)]

def sigFamily : Family :=
  { name := sp.fam
    indices := [eC, .app eF (.bvar 0), .app eF (.bvar 1)]
    resultLevel := .zero }

def sig : InductiveSignature where
  uvars := 0
  params := []
  families := #[sp.sigFamily]
  constructors := #[sp.sigCtor]

/-- The recursor eliminates into `Sort u` for the fresh universe `u = param 0`. -/
def inst : Instance sp.sig where
  uvars := 1
  levels := []
  targetLevel := .param 0
  recursorName := fun _ => sp.recName

/-! ## Source declaration and compiled block -/

def ctorVal : VConstVal := { name := sp.ctor, uvars := 0, type := sp.ctorType }

def indType : VInductiveType where
  name := sp.fam
  uvars := 0
  type := typeFam
  numIndices := 3
  resultLevel := .zero
  ctors := [sp.ctorVal]

def decl : VInductDecl where
  uvars := 0
  nparams := 0
  types := [sp.indType]
  isUnsafe := false

def block : VInductBlock where
  types := sp.decl.typeConstants
  ctors := sp.decl.constructorConstants
  recursors := sp.inst.recursors
  rules := sp.inst.equations
  projections := sp.decl.projectionEntries
  eliminators := [(sp.fam, InductiveSignature.CaseSchema.ofCompilation sp.decl sp.sig [])]

end FamSpec

/-! ## The environment chain -/

def E1 : VEnv := (VEnv.empty.addConst nC ⟨0, typeC⟩).getD .empty
def E2 : VEnv := (E1.addConst nF ⟨0, typeF⟩).getD .empty
def E3 : VEnv := (E2.addConst nc ⟨0, typec⟩).getD .empty
def E4 : VEnv := (E3.addConst nP ⟨0, typeP⟩).getD .empty
def E5 : VEnv := (E4.addConst nL ⟨0, typeMap⟩).getD .empty
def E6 : VEnv := (E5.addConst nR ⟨0, typeMap⟩).getD .empty
def E7 : VEnv := (VInductBlock.install E6 specI.block).getD .empty
def E8 : VEnv := (VInductBlock.install E7 specJ.block).getD .empty

/-- The countermodel environment. -/
abbrev envCM : VEnv := E8

theorem E1_eq : VEnv.empty.addConst nC ⟨0, typeC⟩ = some E1 := rfl
theorem E2_eq : E1.addConst nF ⟨0, typeF⟩ = some E2 := rfl
theorem E3_eq : E2.addConst nc ⟨0, typec⟩ = some E3 := rfl
theorem E4_eq : E3.addConst nP ⟨0, typeP⟩ = some E4 := rfl
theorem E5_eq : E4.addConst nL ⟨0, typeMap⟩ = some E5 := rfl
theorem E6_eq : E5.addConst nR ⟨0, typeMap⟩ = some E6 := rfl
theorem E7_eq : VInductBlock.install E6 specI.block = some E7 := rfl
theorem E8_eq : VInductBlock.install E7 specJ.block = some E8 := rfl

end Lean4Lean.Countermodel
