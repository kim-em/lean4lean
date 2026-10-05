import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceSyntax

/-! Exact certificate footprints need not be minimal field dependencies.
Even the literal declaration template `(fun _ : A => Sort v) parameter`
admits both a parameter-free certificate and one retaining any actually
admitted parameter query. Thus recording only that channels were obtained
from a field-domain certificate does not rule out independent surplus. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

private theorem emptyInputAdmission
    {key : Key (n + 1)}
    (admitted : Admitted env U registry target key left right) :
    Admitted env U registry target ({ key with input := .empty } : Key (n + 1)) left right := by
  obtain ⟨anchor, pair, support, typed, formed, code, _, _⟩ := admitted
  exact ⟨anchor, pair, support, Profile.HasType.empty typed.wf_type, formed, code,
    (fun _ member => nomatch member), (fun _ member => nomatch member)⟩

/-- Both certificates have exactly the same literal source template and
output support. Their distinct parameter footprints are real source syntax,
not a claimed interpretation of a newly synthesized typing derivation. -/
theorem CodeCert.fieldTemplate_surplus
    {env : VEnv} {U n : Nat} {registry : CanonicalHead.Registry}
    {target : List VExpr} {locals : List Nat} {σ : Subst}
    {annotation : VExpr} {key : Key (n + 1)} {support : Profile (n + 1)}
    (domain : CodeCert env U registry target locals σ annotation support [])
    (guard : LambdaGuard env U registry target σ annotation key support)
    (admitted : Admitted env U registry target key (σ 0) (σ 0))
    {level : VLevel} (relevant : Relevant level true) :
    Nonempty (CodeCert env U registry target locals σ
      (.app (.lam annotation (.sort level)) (.bvar 0)) (.sort (n := n + 1) true)
      [(0, ⟨n + 1, key.input⟩)]) ∧
    Nonempty (CodeCert env U registry target locals σ
      (.app (.lam annotation (.sort level)) (.bvar 0)) (.sort (n := n + 1) true) []) := by
  have function : Obs env U registry target locals σ (.lam annotation (.sort level))
      (Profile.fn key (AtomData.sort true)) [] :=
    .lam domain guard (.sort relevant) .nil (fun _ member => nomatch member)
  have emptyGuard : LambdaGuard env U registry target σ annotation
      { key with input := .empty } support := {
    guard with
    inputTyped := Profile.HasType.empty guard.formed.wf_value
    anchor := emptyInputAdmission guard.anchor }
  have emptyFunction : Obs env U registry target locals σ (.lam annotation (.sort level))
      (Profile.fn ({ key with input := .empty } : Key (n + 1)) (AtomData.sort true)) [] :=
    .lam domain emptyGuard (.sort relevant) .nil (fun _ member => nomatch member)
  exact ⟨⟨.seed (.app function (.var locals σ 0 key.input)
      (ProfileAdapter.refl _) admitted) (Profile.HasType.sort true)⟩,
    ⟨.seed (.app emptyFunction .empty (ProfileAdapter.refl _)
      (emptyInputAdmission admitted)) (Profile.HasType.sort true)⟩⟩

end Lean4Lean.AnchoredSource.Adapted

namespace Lean4Lean.VEnv
open VExpr

/-- The counterexample template has actual original Strong formation at
the parameter context. Its binder genuinely ignores the parameter. -/
theorem originalIgnoredParameterType
    {env : VEnv} {U : Nat} (henv : env.Ordered)
    {annotation : VExpr} {u v : VLevel}
    (uWF : u.WF U) (vWF : v.WF U)
    (formation : env.IsDefEqStrong U [] annotation annotation (.sort u)) :
    env.IsDefEqStrong U [annotation]
      (.app (.lam annotation (.sort v)) (.bvar 0))
      (.app (.lam annotation (.sort v)) (.bvar 0)) (.sort (.succ v)) := by
  have closed : annotation.Closed := (formation.defeq.closedN' henv.closed trivial).1
  have domain := formation.weak0 henv (Γ := [annotation])
  have sort (Γ : List VExpr) (level : VLevel) (wf : level.WF U) :
      env.IsDefEqStrong U Γ (.sort level) (.sort level) (.sort (.succ level)) :=
    .sortDF wf wf (by rfl)
  have fn : env.IsDefEqStrong U [annotation]
      (.lam annotation (.sort v)) (.lam annotation (.sort v))
      (.forallE annotation (.sort (.succ v))) :=
    .lamDF (v := .succ (.succ v)) uWF vWF domain (sort _ _ vWF) (sort _ _ vWF)
      (sort _ _ vWF) (sort _ _ vWF)
  have lookup : Lookup [annotation] 0 annotation := by
    simpa only [closed.lift_eq] using Lookup.zero (Γ := []) (ty := annotation)
  exact .appDF (v := .succ (.succ v)) uWF vWF domain (sort _ _ vWF) fn
    (.bvar lookup uWF domain) (sort _ _ vWF)

end Lean4Lean.VEnv
