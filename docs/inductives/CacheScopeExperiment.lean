import Lean4Lean.TypeChecker
import Lean4Lean.Theory.Typing.Basic
/-! # Conversion facts outliving a binder scope

Design evidence, not a module of the library. Run with

    lake env lean docs/inductives/CacheScopeExperiment.lean

Output before the checker scoped its binders (2026-10-06): "L4L whole term
accepted", "C++ unseeded declaration rejected", "C++ whole declaration
accepted", and the cache experiment `(false, (true, true, true, true), false,
true, false)`. Since `withLocalDecl`/`withLetDecl` restore the caches and the
equivalence manager on scope exit (`TypeChecker.State.leaveScope`), the output
is "L4L whole term rejected" (the C++ lines are unchanged) and the cache
experiment `(false, (true, true, true, true), false, false, false)`.

Using the two singleton families of `SingletonStrengthening.lean`, the closed
definition `result : SJ := let seed : (q : P v) → Type 1 := fun q => …; let
ret : SJ := zz; ret` (with `zz : SI` an axiom) is accepted by both the C++
kernel and the Lean4Lean checker, while the same definition without the `seed`
binding is rejected. The `seed` body forces the comparisons `SI ≡ … ≡ SJ`
inside the scope of `q`; the persistent equivalence manager and caches then
answer `SI ≡ SJ` outside that scope, where the declarative theory cannot derive
it (see STRENGTHENING.md). The implemented conversion is therefore not local to
the context, so no cache invariant of the form "every entry is derivable in the
current context" holds for the current executable. Script originally written by
the Astra reviewer and reproduced locally.
-/

/-!
Run with `lake env lean docs/inductives/SingletonStrengthening.lean`.

Source admissibility and the exact declarative equality chain for the
strengthening countermodel in STRENGTHENING.md. The opaque axioms below are
object-language source declarations, not new axioms in the verification
development. This file is not imported by the checker or theory.

The final theorem checks the combination of the branch's actual inference
rules. Neither it nor the source declarations formalize the complete
VEnv.WF installation or the semantic interpretation of all abstract terms.
-/
namespace InductiveStrengtheningPressure

axiom C : Type
axiom F : C → Type
axiom c : C
axiom P : F c → Prop
axiom leftMap : F c → F c
axiom rightMap : F c → F c

inductive I : (n : C) → F n → F n → Prop where
  | mk (v : F c) (h : P v) : I c v (leftMap v)

inductive J : (n : C) → F n → F n → Prop where
  | mk (v : F c) (h : P v) : J c v (rightMap v)

#check I.rec
#check J.rec

def left (K : (v : F c) → P v → Type) (v : F c)
    (p : I c v (leftMap v)) : Type :=
  I.rec (motive := fun _ _ _ _ => Type) K p

def right (K : (v : F c) → P v → Type) (v : F c)
    (p : J c v (rightMap v)) : Type :=
  J.rec (motive := fun _ _ _ _ => Type) K p

-- Each constructor computation is literal iota.
example (K : (v : F c) → P v → Type) (v : F c) (q : P v) :
    left K v (I.mk v q) = K v q := rfl

example (K : (v : F c) → P v → Type) (v : F c) (q : P v) :
    right K v (J.mk v q) = K v q := rfl

-- Each major replacement is definitionally proof irrelevant.
example (v : F c) (q : P v) (p : I c v (leftMap v)) : p = I.mk v q := rfl
example (v : F c) (q : P v) (p : J c v (rightMap v)) : p = J.mk v q := rfl

-- This Lean equality proof records the congruence/transitivity chain;
-- it is not a claim that kernel reduction directly compares the endpoints.
theorem withProof (K : (v : F c) → P v → Type) (v : F c)
    (p : I c v (leftMap v)) (r : J c v (rightMap v)) (q : P v) :
    left K v p = right K v r := by
  calc
    left K v p = left K v (I.mk v q) := congrArg (left K v) (show p = I.mk v q from rfl)
    _ = K v q := rfl
    _ = right K v (J.mk v q) := rfl
    _ = right K v r := congrArg (right K v) (show J.mk v q = r from rfl)

open Lean Lean.Elab.Command in
run_elab do
  for name in [``I.rec, ``J.rec] do
    let some (.recInfo info) := (← getEnv).find? name | throwError "not a recursor"
    unless info.levelParams.length == 1 && info.numParams == 0 &&
        info.numIndices == 3 && info.numMinors == 1 do
      throwError "unexpected source recursor metadata"
    logInfo m!"{name}: large singleton elimination accepted, three indices, zero parameters; isK={info.k}"

end InductiveStrengtheningPressure

namespace InductiveStrengtheningPressure.Abstract
open Lean4Lean
open Lean4Lean.VEnv

/-- The exact declarative chain, at a shared sort, uses no inversion,
uniqueness, strengthening, or equality datatype. In the source example
`ctorI` and `ctorJ` contain the fresh proof, but the two endpoints do not.

This checks the inference-rule combination. The natural typing/iota
premises come from the declared recursors; this theorem alone does not
construct the full finite installation/WF derivation for those declarations. -/
theorem proofMajorJoin {env : VEnv} {U : Nat} {Γ : List VExpr}
    {familyI familyJ p r ctorI ctorJ recI recJ result : VExpr} {u : VLevel}
    (hi : HasType env U Γ familyI (.sort .zero))
    (hj : HasType env U Γ familyJ (.sort .zero))
    (hp : HasType env U Γ p familyI) (hr : HasType env U Γ r familyJ)
    (hci : HasType env U Γ ctorI familyI) (hcj : HasType env U Γ ctorJ familyJ)
    (hfi : HasType env U Γ recI (.forallE familyI (.sort u)))
    (hfj : HasType env U Γ recJ (.forallE familyJ (.sort u)))
    (hii : IsDefEq env U Γ (.app recI ctorI) result (.sort u))
    (hij : IsDefEq env U Γ (.app recJ ctorJ) result (.sort u)) :
    IsDefEq env U Γ (.app recI p) (.app recJ r) (.sort u) := by
  have left : IsDefEq env U Γ (.app recI p) (.app recI ctorI) (.sort u) :=
    .appDF hfi (.proofIrrel hi hp hci)
  have right : IsDefEq env U Γ (.app recJ r) (.app recJ ctorJ) (.sort u) :=
    .appDF hfj (.proofIrrel hj hr hcj)
  exact (left.trans hii).trans (right.trans hij).symm

#print axioms proofMajorJoin
end InductiveStrengtheningPressure.Abstract


namespace InductiveStrengtheningPressure
axiom KK : (v : F c) → P v → Type
axiom vv : F c
axiom pp : I c vv (leftMap vv)
axiom rr : J c vv (rightMap vv)
open Lean in
run_elab do
  let si := mkAppN (mkConst ``left) #[mkConst ``KK, mkConst ``vv, mkConst ``pp]
  let sj := mkAppN (mkConst ``right) #[mkConst ``KK, mkConst ``vv, mkConst ``rr]
  let host := (← getEnv).toKernelEnv
  let empty := (← Lean.mkEmptyEnvironment).toKernelEnv
  let build : Except Kernel.Exception Kernel.Environment := do
    let mut env := empty
    for n in [``C, ``F, ``c, ``P, ``leftMap, ``rightMap] do
      let some (.axiomInfo v) := host.find? n | throw (.other "missing axiom")
      env ← Kernel.Environment.addDeclCore env 0 50000 (.axiomDecl v) none
    for (n, cn) in [(``I, ``I.mk), (``J, ``J.mk)] do
      let some iv := host.find? n | throw (.other "missing family")
      let some cv := host.find? cn | throw (.other "missing constructor")
      env ← Kernel.Environment.addDeclCore env 0 50000
        (.inductDecl [] 0 [{ name := n, type := iv.type, ctors := [{ name := cn, type := cv.type }] }] false) none
    for n in [``left, ``right] do
      let some (.defnInfo v) := host.find? n | throw (.other "missing definition")
      env ← Kernel.Environment.addDeclCore env 0 50000 (.defnDecl v) none
    for n in [``KK, ``vv, ``pp, ``rr] do
      let some (.axiomInfo v) := host.find? n | throw (.other "missing axiom")
      env ← Kernel.Environment.addDeclCore env 0 50000 (.axiomDecl v) none
    return env
  let .ok smallEnv := build | throwError "small environment rejected"
  logInfo m!"small environment checked by C++: Eq present = {smallEnv.contains ``Eq}"
  let zzName := Name.str `InductiveStrengtheningPressure "zz"
  let wrapped := Expr.letE `unused (mkSort (.succ .zero)) si si false
  let .ok smallEnv := Kernel.Environment.addDeclCore smallEnv 0 50000
    (.axiomDecl { name := zzName, levelParams := [], type := wrapped, isUnsafe := false }) none
    | throwError "z rejected"
  let q := mkFVar ⟨`test_q⟩
  let ci := mkAppN (mkConst ``I.mk) #[mkConst ``vv, q]
  let cj := mkAppN (mkConst ``J.mk) #[mkConst ``vv, q]
  let ii := mkAppN (mkConst ``left) #[mkConst ``KK, mkConst ``vv, ci]
  let jj := mkAppN (mkConst ``right) #[mkConst ``KK, mkConst ``vv, cj]
  let mid := mkAppN (mkConst ``KK) #[mkConst ``vv, q]
  let mut seedBody := si
  for (a,b) in [(jj,sj), (mid,jj), (ii,mid), (si,ii)] do
    let aty := Expr.forallE `x a a .default
    let bv := Expr.lam `x b (.bvar 0) .default
    seedBody := Expr.letE `f aty bv (seedBody.liftLooseBVars 0 1) false
  let qTy := mkApp (mkConst ``P) (mkConst ``vv)
  let seed := Expr.lam `q qTy (seedBody.abstract #[q]) .default
  let seedTy := Expr.forallE `q qTy (mkSort (.succ .zero)) .default
  let finalBody := Expr.letE `ret sj (mkConst zzName) (.bvar 0) false
  let term := Expr.letE `seed seedTy seed finalBody false
  let l4l := Lean4Lean.TypeChecker.M.run smallEnv .safe {} [] {} (Lean4Lean.TypeChecker.checkType term)
  match l4l with
  | .ok _ => logInfo "L4L whole term accepted"
  | .error _ => logInfo "L4L whole term rejected"
  let unseeded := Kernel.Environment.addDeclCore smallEnv 0 50000
    (.defnDecl { name := Name.str `InductiveStrengtheningPressure "unseeded", levelParams := [], type := sj, value := finalBody, hints := .opaque, safety := .safe }) none
  match unseeded with
  | .ok _ => logInfo "C++ unseeded declaration accepted"
  | .error _ => logInfo "C++ unseeded declaration rejected"
  let native := Kernel.Environment.addDeclCore smallEnv 0 50000
    (.defnDecl { name := Name.str `InductiveStrengtheningPressure "result", levelParams := [], type := sj, value := term, hints := .opaque, safety := .safe }) none
  match native with
  | .ok _ => logInfo "C++ whole declaration accepted"
  | .error _ => logInfo "C++ whole declaration rejected"
  let result := Lean4Lean.TypeChecker.M.run smallEnv .safe {} [] {} do
    let before ← Lean4Lean.TypeChecker.isDefEq si sj
    let saved ← get
    let links ← Lean4Lean.withLocalDecl `q .default (mkApp (mkConst ``P) (mkConst ``vv)) fun q => do
      let ci := mkAppN (mkConst ``I.mk) #[mkConst ``vv, q]
      let cj := mkAppN (mkConst ``J.mk) #[mkConst ``vv, q]
      let ii := mkAppN (mkConst ``left) #[mkConst ``KK, mkConst ``vv, ci]
      let jj := mkAppN (mkConst ``right) #[mkConst ``KK, mkConst ``vv, cj]
      let mid := mkAppN (mkConst ``KK) #[mkConst ``vv, q]
      let a ← Lean4Lean.TypeChecker.isDefEq si ii
      let b ← Lean4Lean.TypeChecker.isDefEq ii mid
      let c ← Lean4Lean.TypeChecker.isDefEq mid jj
      let d ← Lean4Lean.TypeChecker.isDefEq jj sj
      pure (a,b,c,d)
    let after ← Lean4Lean.TypeChecker.isDefEq si sj
    let wrapped := Expr.letE `unused (mkSort (.succ .zero)) si si false
    let afterWrap ← Lean4Lean.TypeChecker.isDefEq wrapped sj
    modify fun st => { st with inferTypeI := saved.inferTypeI, inferTypeC := saved.inferTypeC, whnfCoreCache := saved.whnfCoreCache, whnfCache := saved.whnfCache, eqvManager := saved.eqvManager }
    let afterRestore ← Lean4Lean.TypeChecker.isDefEq wrapped sj
    pure (before, links, after, afterWrap, afterRestore)
  match result with
  | .ok r => logInfo m!"cache experiment: {repr r}"
  | .error _ => throwError "checker exception"
end InductiveStrengtheningPressure
