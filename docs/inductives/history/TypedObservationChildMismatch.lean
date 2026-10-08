import Lean4Lean.Theory.Typing.Strong

/-! Indexing an observer by its outer assigned type does not determine the
types of its application children. This example uses only original Strong
rules in the empty environment. The two application derivations have the
same expression and literal result type, but different literal domains.
It rules out identifying those domains by syntactic equality; it does not
rule out a semantic coherence theorem transporting between them. -/
namespace Lean4Lean.TypedObservationChildMismatch
open VExpr VEnv

def prop : VExpr := .sort .zero
def type : VExpr := .sort (.succ .zero)
def expandedProp : VExpr := .app (.lam type (.bvar 0)) prop
def context : List VExpr := [prop, .forallE prop prop]

private theorem sort (Γ : List VExpr) (level : VLevel) (wf : level.WF 0) :
    VEnv.empty.IsDefEqStrong 0 Γ (.sort level) (.sort level) (.sort (.succ level)) :=
  .sortDF wf wf rfl

/-- A concrete, syntactically different choice of the same domain. -/
theorem domainConversion (Γ : List VExpr) :
    VEnv.empty.IsDefEqStrong 0 Γ prop expandedProp type := by
  have binder : VEnv.empty.IsDefEqStrong 0 (type :: Γ) (.bvar 0) (.bvar 0) type :=
    .bvar (u := .succ (.succ .zero)) (by simpa [type, VExpr.lift, VExpr.liftN] using
      (Lookup.zero (Γ := Γ) (ty := type))) trivial (sort _ _ trivial)
  have beta := IsDefEqStrong.beta (env := VEnv.empty) (uvars := 0)
    (u := .succ (.succ .zero)) (v := .succ (.succ .zero))
    (A := type) (B := type) (e := .bvar 0) (e' := prop)
    (Γ := Γ) (by trivial) (by trivial)
    (sort _ _ trivial) (sort _ _ trivial) binder (sort _ _ trivial)
    (by simpa [type, VExpr.inst] using sort Γ (.succ .zero) trivial)
    (by simpa [prop, type, VExpr.inst] using sort Γ .zero trivial)
  simpa [expandedProp, type, prop, VExpr.inst] using beta.symm

private theorem functionType (Γ : List VExpr) :
    VEnv.empty.IsDefEqStrong 0 Γ (.forallE prop prop) (.forallE prop prop)
      (.sort (.imax (.succ .zero) (.succ .zero))) :=
  .forallEDF trivial trivial (sort _ _ trivial) (sort _ _ trivial) (sort _ _ trivial)

theorem contextWellFormed : CtxStrong VEnv.empty 0 context :=
  ⟨⟨trivial, _, functionType []⟩, _, sort _ _ trivial⟩

private theorem function :
    VEnv.empty.IsDefEqStrong 0 context (.bvar 1) (.bvar 1) (.forallE prop prop) :=
  .bvar (u := .imax (.succ .zero) (.succ .zero)) (by simpa [context, prop, VExpr.lift, VExpr.liftN] using
    (Lookup.succ (A := prop) (Lookup.zero (Γ := []) (ty := .forallE prop prop))))
    ⟨trivial, trivial⟩ (functionType _)

private theorem argument :
    VEnv.empty.IsDefEqStrong 0 context (.bvar 0) (.bvar 0) prop :=
  .bvar (u := .succ .zero) (by simpa [context, prop, VExpr.lift, VExpr.liftN] using
    (Lookup.zero (Γ := [.forallE prop prop]) (ty := prop))) trivial (sort _ _ trivial)

/-- Both internal type choices actually inhabit original application-rule
premises. The outer expression and its assigned type are identical. -/
theorem applicationChildMismatch :
    prop ≠ expandedProp ∧
    VEnv.empty.IsDefEqStrong 0 context (.bvar 1) (.bvar 1) (.forallE prop prop) ∧
    VEnv.empty.IsDefEqStrong 0 context (.bvar 1) (.bvar 1) (.forallE expandedProp prop) ∧
    VEnv.empty.IsDefEqStrong 0 context (.bvar 0) (.bvar 0) prop ∧
    VEnv.empty.IsDefEqStrong 0 context (.bvar 0) (.bvar 0) expandedProp ∧
    VEnv.empty.IsDefEqStrong 0 context (.app (.bvar 1) (.bvar 0))
      (.app (.bvar 1) (.bvar 0)) prop := by
  have domains := domainConversion context
  have functions : VEnv.empty.IsDefEqStrong 0 context
      (.forallE prop prop) (.forallE expandedProp prop)
      (.sort (.imax (.succ .zero) (.succ .zero))) :=
    .forallEDF trivial trivial domains (sort _ _ trivial) (sort _ _ trivial)
  have otherFunction := IsDefEqStrong.defeqDF (u := .imax (.succ .zero) (.succ .zero)) ⟨trivial, trivial⟩ functions function
  have otherArgument := IsDefEqStrong.defeqDF (u := .succ .zero) (by trivial) domains argument
  have applied := IsDefEqStrong.appDF (env := VEnv.empty) (uvars := 0)
    (u := .succ .zero) (v := .succ .zero) (Γ := context)
    (A := expandedProp) (B := prop) (f := .bvar 1) (f' := .bvar 1)
    (a := .bvar 0) (a' := .bvar 0) (by trivial) (by trivial)
    domains.hasType.2 (sort _ _ trivial) otherFunction otherArgument
    (by simpa [prop, VExpr.inst] using sort context .zero trivial)
  refine ⟨(by intro equal; cases equal), function, otherFunction, argument,
    otherArgument, by simpa [prop, VExpr.inst] using applied⟩

end Lean4Lean.TypedObservationChildMismatch
