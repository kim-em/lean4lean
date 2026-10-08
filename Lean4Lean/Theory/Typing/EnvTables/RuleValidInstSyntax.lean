import Lean4Lean.Theory.Typing.Strong
import Lean4Lean.Theory.VEnv
import Lean4Lean.Theory.VLevel
import Lean4Lean.Theory.Typing.EnvTables.EnvSigSyntax
import Lean4Lean.Theory.Typing.HeadInversionDefs
import Lean4Lean.Theory.Typing.EnvTables.EnvSigCtor
import Lean4Lean.Theory.Typing.ConstructorRigidity

/-!
# Syntax of restored generated equations and recursor types

The generated equation of a constructor (`Instance.equation`, native or abstract head) and the
generated recursor type (`Instance.recursorType`), after restoration:

* `restored_equation_syntax`: the left side is a lambda telescope `Ds` over the head applied to the
  prefix variables, the restored indices and the restored major; the right side is a lambda
  telescope over the same `Ds`; the type is the Pi telescope over `Ds` of the owner's motive
  applied to the same indices and major; the motive's binder domain is a telescope ending in the
  target sort.
* `restored_recursorType_syntax`: the recursor type is a Pi telescope whose last domain is the
  restored owner family applied to the parameters and the index variables.
-/

namespace Lean4Lean.EnvTables
open Lean4Lean InductiveSignature

theorem restoration_wrapForalls_forall₂ {r : Restoration} :
    ∀ {domains : List VExpr} {body output : VExpr},
      r.expr (VExpr.wrapForalls domains body) = some output →
      ∃ domains' body', output = VExpr.wrapForalls domains' body' ∧
        List.Forall₂ (fun d d' => r.expr d = some d') domains domains' ∧ r.expr body = some body'
  | [], _, output, H => ⟨[], output, rfl, .nil, H⟩
  | d :: ds, body, output, H => by
    change (do let d' ← r.expr d; let t' ← r.expr (VExpr.wrapForalls ds body)
               pure (.forallE d' t')) = some output at H
    simp only [bind, Option.bind_eq_some_iff] at H
    obtain ⟨d', hd, out, hout, H⟩ := H
    cases H
    obtain ⟨ds', body', rfl, hrel, hb⟩ := restoration_wrapForalls_forall₂ (domains := ds) hout
    exact ⟨d' :: ds', body', rfl, .cons hd hrel, hb⟩

end Lean4Lean.EnvTables
