import Lean4Lean.Theory.Typing.AnchoredConstantSyntax
import Lean4Lean.Theory.Typing.AnchoredNativePartialTelescope

/-! A literal constant telescope preserves its original prefix formation
and pairs supplied arguments at its actual residual type. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv InductiveSignature
open private eta_spine capture_vars from Lean4Lean.Theory.Typing.AnchoredNativePartialTelescope
set_option backward.isDefEq.respectTransparency false

namespace ConstantTelescope
variable (signature : ConstantTelescope declaredType)

theorem prefixResidual_cons (origin : signature.domains[count]? = some domain) :
    wrapForalls (signature.domains.drop count) signature.result =
      .forallE domain (wrapForalls (signature.domains.drop (count + 1)) signature.result) := by
  obtain ⟨bound, same⟩ := List.getElem?_eq_some_iff.mp origin
  rw [List.drop_eq_getElem_cons bound, same]
  rfl

theorem prefixContext_cons (origin : signature.domains[count]? = some domain) :
    (signature.domains.take (count + 1)).reverse = domain :: (signature.domains.take count).reverse := by
  rw [List.take_add_one, origin]
  simp

theorem prefixPayload {P : List VExpr → VExpr → VExpr → Prop}
    (root : ∃ u, P [] declaredType (.sort u)) (tree : SourcePiFormation P [] declaredType)
    (count : Nat) :
    ((∃ u, P (signature.domains.take count).reverse
      (wrapForalls (signature.domains.drop count) signature.result) (.sort u)) ∧
      SourcePiFormation P (signature.domains.take count).reverse
        (wrapForalls (signature.domains.drop count) signature.result)) ∧
    (∀ (bound : count < signature.domains.length),
      (∃ u, P (signature.domains.take count).reverse signature.domains[count] (.sort u)) ∧
      SourcePiFormation P (signature.domains.take count).reverse signature.domains[count]) := by
  rw [signature.type_eq] at root tree
  have all := tree.telescope root
  have split : wrapForalls signature.domains signature.result =
      wrapForalls (signature.domains.take count)
        (wrapForalls (signature.domains.drop count) signature.result) := by
    rw [← wrapForalls_append, List.take_append_drop]
  rw [split] at root tree
  exact ⟨by simpa only [List.append_nil] using (tree.telescope root).2,
    fun bound => by simpa only [List.append_nil] using all.1 count bound⟩

end ConstantTelescope

namespace ConstantTelescope

theorem prefixFormation
    {sourceEnv : VEnv} {U : Nat} {declaredType : VExpr} {level : VLevel}
    (signature : ConstantTelescope declaredType)
    (original : sourceEnv.IsDefEqStrong U [] declaredType declaredType (.sort level)) (count : Nat) :
    (∃ u, sourceEnv.IsDefEqStrong U (signature.domains.take count).reverse
      (wrapForalls (signature.domains.drop count) signature.result)
      (wrapForalls (signature.domains.drop count) signature.result) (.sort u)) ∧
    (∀ (bound : count < signature.domains.length),
      ∃ u, sourceEnv.IsDefEqStrong U (signature.domains.take count).reverse
        signature.domains[count] signature.domains[count] (.sort u)) := by
  have payload := signature.prefixPayload ⟨level, original⟩ original.sourcePiFormation.1 count
  exact ⟨payload.1.1, fun bound => (payload.2 bound).1⟩

theorem prefixCtxStrong
    {sourceEnv : VEnv} {U : Nat} {declaredType : VExpr} {level : VLevel}
    (signature : ConstantTelescope declaredType)
    (original : sourceEnv.IsDefEqStrong U [] declaredType declaredType (.sort level))
    (count : Nat) : CtxStrong sourceEnv U (signature.domains.take count).reverse := by
  induction count with
  | zero => trivial
  | succ count ih =>
    by_cases bound : count < signature.domains.length
    · have origin := List.getElem?_eq_getElem bound
      rw [signature.prefixContext_cons origin]
      exact ⟨ih, (signature.prefixFormation original count).2 bound⟩
    · rw [List.take_of_length_le (by omega)] at ih ⊢
      exact ih

/-- The lookup gives the actual head type. No inversion of an assigned
application type is used to recover the declared argument telescope. -/
theorem prefixArgumentsEqual
    {env : VEnv} {U : Nat} {target : List VExpr}
    (henv : env.Ordered) (hTarget : OnCtx target (env.IsType U))
    {name : Name} {levels : List VLevel} {declaredType : VExpr}
    (signature : ConstantTelescope declaredType)
    (constant : env.HasType U [] (.const name levels) declaredType)
    {count : Nat} (bound : count ≤ signature.domains.length)
    {left right : List VExpr}
    (leftLength : left.length = count) (rightLength : right.length = count)
    (arguments : Ctx.SubstEq env U target (nativeCaptureSubst left)
      (nativeCaptureSubst right) (signature.domains.take count).reverse) :
    env.IsDefEq U target (mkApps (.const name levels) left)
      (mkApps (.const name levels) right)
      ((wrapForalls (signature.domains.drop count) signature.result).subst (nativeCaptureSubst left)) ∧
    TypeConversion env U target
      ((wrapForalls (signature.domains.drop count) signature.result).subst (nativeCaptureSubst left))
      ((wrapForalls (signature.domains.drop count) signature.result).subst (nativeCaptureSubst right)) := by
  have declared : env.HasType U [] (.const name levels)
      (wrapForalls (signature.domains.take count)
        (wrapForalls (signature.domains.drop count) signature.result)) := by
    rw [← wrapForalls_append, List.take_append_drop, ← signature.type_eq]
    exact constant
  obtain ⟨context, opened⟩ := HasType.native_open henv (by trivial) declared
  have taken : (signature.domains.take count).length = count := by
    simp only [List.length_take, Nat.min_eq_left bound]
  simp only [List.append_nil, eta_spine, liftN, taken] at context opened
  have raw := opened.substDF henv context hTarget arguments
  simp only [subst_mkApps, subst_const, ← leftLength, capture_vars] at raw
  rw [leftLength, ← rightLength, capture_vars] at raw
  obtain ⟨u, formed⟩ := opened.isType henv context
  exact ⟨by simpa only [rightLength] using raw,
    .single (formed.substDF henv context hTarget arguments)⟩

end ConstantTelescope
end Lean4Lean.AnchoredSource.Adapted
