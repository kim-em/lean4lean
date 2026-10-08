import Lean
import Lean4Lean.Theory.Typing.Lemmas

/-!
An accepted singleton family with a repeated TYPE index. Its constructor field
x is declared at A, but an occurrence supplies x at B and matching must align
B with A. The recursor returns x; applying that result witnesses a real function
demand, so a generic producer that first retags every capture cannot restrict
attention to bottom profiles or opaque data-index equalities.

The source checks establish acceptance, metadata, and concrete reduction.
The abstract certificate below additionally isolates the data-transfer demand
of canonical coverage, with its operational premises explicit. Neither part
constructs abstract finite installation or a complete logical relation.
In particular, the identity minor permits a different proof to reuse x at B
and cancel casts; this is not a counterexample to all adequacy architectures.
-/
namespace NativeTypeIndexPressure
universe u
noncomputable section

set_option inductive.autoPromoteIndices false in
inductive J : (A B : Type u) → B → Prop where
  | mk (A : Type u) (x : A) : J A A x

def select {A B : Type u} (x : B) (p : J A B x) : B :=
  J.rec (motive := fun _ B _ _ => B) (fun _ x => x) p

def leftType (U : Type) : Type 1 := U → Type
def rightType (U : Type) : Type 1 :=
  (fun X : Type 1 => X) (leftType U)
def supplied (U : Type) : rightType U := fun _ => Prop

-- The minor returns its data capture, and the outer observer APPLIES it.
-- Thus a nonbottom result demand requires a nonempty function demand.
-- This pressures a producer that first interprets every capture at its
-- declared field domain. It is not an impossibility result: this identity
-- minor also permits returning the original x:B relation by cast cancellation.
def observed (U : Type) (arg : U)
    (p : J (leftType U) (rightType U) (supplied U)) : Type :=
  select (supplied U) p arg

theorem observed_constructor (U : Type) (arg : U) :
    observed U arg (J.mk (leftType U) (supplied U)) = Prop := rfl

theorem observed_any_proof (U : Type) (arg : U)
    (p : J (leftType U) (rightType U) (supplied U)) :
    observed U arg p = Prop := by
  have hp : p = J.mk (leftType U) (supplied U) := Subsingleton.elim _ _
  cases hp
  rfl

open Lean Elab Command in
run_elab do
  let .inductInfo info ← getConstInfo ``J | throwError "not an inductive"
  unless info.numParams == 0 && info.numIndices == 3 do
    throwError "unexpected parameter/index metadata"
  let .ctorInfo ctor ← getConstInfo ``J.mk | throwError "not a constructor"
  unless ctor.numFields == 2 do throwError "unexpected field count"
  let .recInfo rec ← getConstInfo ``J.rec | throwError "not a recursor"
  unless !rec.k do throwError "unexpected K optimization"
  logInfo "Repeated type index J accepted: 0 parameters, 3 indices, 2 fields; native isK=false."

#print axioms observed_constructor
#print axioms observed_any_proof
end
end NativeTypeIndexPressure

/-!
The production-calculus certificate below isolates a second obligation. Write
`family : A → Prop`, `ctor : (x : A) → family x`, and
`selector : (x : A) → family x → A` for the signatures of a singleton and its
identity-minor selector. Their typings and the literal constructor-iota equation
are premises; this does not install a declaration or prove a general native
replay producer.

For ANY data equality `F ≡ G : A`, conversion types the literal major `ctor F`
at `family G`. Ordinary constructor iota retains its field `F`, whereas a fixed
plan capturing the occurrence index chooses `G`. Consequently, coverage of
those original observations by that plan owes observation transfer across the
arbitrary data equality, even if all proof fields have already been abstracted.
Taking `A` to be a universe or a function type makes this a relevant demand.
-/
namespace Lean4Lean.VEnv.NativeCoverageObligation
open VExpr
variable {env : VEnv} {U : Nat} {Γ : List VExpr}
  {A family ctor selector F G : VExpr}

/-- Retagging a constructor major uses only ordinary family congruence and
conversion. No type uniqueness or Pi inversion is needed. -/
theorem retagConstructor
    (hfamily : env.HasType U Γ family (.forallE A (.sort .zero)))
    (hctor : env.HasType U Γ ctor
      (.forallE A (.app family.lift (.bvar 0))))
    (H : env.IsDefEq U Γ F G A) :
    env.HasType U Γ (.app ctor F) (.app family G) := by
  have hm : env.HasType U Γ (.app ctor F) (.app family F) := by
    simpa [inst, instVar, inst_lift] using hctor.app H.hasType.1
  have hf : env.IsDefEq U Γ (.app family F) (.app family G) (.sort .zero) :=
    .appDF hfamily H
  exact hf.defeq hm

/-- At the converted occurrence index `G`, identity-minor iota still yields
the actual constructor field `F`. The iota premise is for the literal index
`F`; the converted-index equation is derived using production congruence. -/
theorem selectorAtConvertedIndex
    (hselector : env.HasType U Γ selector
      (.forallE A (.forallE (.app family.lift (.bvar 0)) A.lift.lift)))
    (hctor : env.HasType U Γ ctor
      (.forallE A (.app family.lift (.bvar 0))))
    (H : env.IsDefEq U Γ F G A)
    (hiota : env.IsDefEq U Γ
      (.app (.app selector F) (.app ctor F)) F A) :
    env.IsDefEq U Γ (.app (.app selector G) (.app ctor F)) F A := by
  have hm : env.HasType U Γ (.app ctor F) (.app family F) := by
    simpa [inst, instVar, inst_lift] using hctor.app H.hasType.1
  have hs : env.IsDefEq U Γ (.app selector F) (.app selector G)
      (.forallE (.app family F) A.lift) := by
    simpa [inst, instVar, inst_lift, ← lift_instN_lo] using
      (IsDefEq.appDF hselector H)
  have he : env.IsDefEq U Γ
      (.app (.app selector F) (.app ctor F))
      (.app (.app selector G) (.app ctor F)) A := by
    simpa only [inst_lift] using IsDefEq.appDF hs hm
  exact he.symm.trans hiota

/-- Exact operational consequence for one finite observation, represented by
`Observe`. `iotaExpand` is the ordinary constructor-iota expansion obligation
for this syntactic redex, including its occurrence typing; it is NOT a premise
that arbitrary declarative equalities preserve observations. `canonicalCover`
is the proposed replacement of that original observation by the occurrence
index capture. Both operational premises are deliberately explicit: the two
typing/equality theorems above do not themselves establish operational coverage.

Thus proving this coverage uniformly proves observation transfer across every
`H : F ≡ G : A`, beyond proof-only replacement. This is a necessity result for
that interface, not an impossibility result for a larger adequacy induction. -/
theorem canonicalCoverage_requires_dataTransfer
    (hfamily : env.HasType U Γ family (.forallE A (.sort .zero)))
    (hctor : env.HasType U Γ ctor
      (.forallE A (.app family.lift (.bvar 0))))
    (H : env.IsDefEq U Γ F G A)
    (Observe : VExpr → Prop)
    (iotaExpand :
      env.HasType U Γ (.app ctor F) (.app family G) →
      Observe F → Observe (.app (.app selector G) (.app ctor F)))
    (canonicalCover :
      env.HasType U Γ (.app ctor F) (.app family G) →
      Observe (.app (.app selector G) (.app ctor F)) → Observe G) :
    Observe F → Observe G := by
  have hm := retagConstructor hfamily hctor H
  exact fun hobs => canonicalCover hm (iotaExpand hm hobs)

#print axioms retagConstructor
#print axioms selectorAtConvertedIndex
#print axioms canonicalCoverage_requires_dataTransfer

end Lean4Lean.VEnv.NativeCoverageObligation
