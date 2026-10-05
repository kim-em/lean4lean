import Lean4Lean.Theory.Typing.SourcePiFormation
import Lean4Lean.Theory.Typing.NativeTelescope
import Lean4Lean.Theory.Typing.NativeRuleRegistration
import Lean4Lean.Theory.Typing.AnchoredNativePrefixPlan
import Lean4Lean.Theory.Inductive.NativeCommonPrefix

/-! Partial native telescopes retain the registered suffix literally. Source
formation is read from original Pi payloads; raw prefix application uses direct
opening and paired substitution, without uniqueness or Pi injectivity. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv InductiveSignature NativeRecursorData
open private telescope_eq from Lean4Lean.Theory.Inductive.NativeCommonPrefix
set_option backward.isDefEq.respectTransparency false

private theorem split_telescope (domains : List VExpr) (result : VExpr) (count : Nat) :
    wrapForalls domains result =
      wrapForalls (domains.take count) (wrapForalls (domains.drop count) result) := by
  rw [← wrapForalls_append, List.take_append_drop]

/-- A partial residual and the next binder are original source Pi payloads.
The predicate can retain raw Strong derivations together with their already
proved relative semantic results. -/
theorem NativeConstantSignature.prefixPayload
    {data : NativeRecursorData} {levels : List VLevel}
    (signature : NativeConstantSignature data levels)
    {P : List VExpr → VExpr → VExpr → Prop}
    (root : ∃ u, P [] (signature.type.instL levels) (.sort u))
    (tree : SourcePiFormation P [] (signature.type.instL levels))
    (count : Nat) :
    ((∃ u, P (signature.domains.take count).reverse
      (wrapForalls (signature.domains.drop count) signature.result) (.sort u)) ∧
      SourcePiFormation P (signature.domains.take count).reverse
        (wrapForalls (signature.domains.drop count) signature.result)) ∧
    (∀ (bound : count < signature.domains.length),
      (∃ u, P (signature.domains.take count).reverse signature.domains[count] (.sort u)) ∧
      SourcePiFormation P (signature.domains.take count).reverse signature.domains[count]) := by
  rw [telescope_eq signature.telescope] at root tree
  have all := tree.telescope root
  rw [split_telescope signature.domains signature.result count] at root tree
  exact ⟨by simpa only [List.append_nil] using (tree.telescope root).2,
    fun bound => by simpa only [List.append_nil] using all.1 count bound⟩

/-- The registered residual's formation at any supplied prefix is extracted
from original Strong children, even when the whole type's sort was converted. -/
theorem NativeConstantSignature.prefixFormation
    {sourceEnv : VEnv} {U : Nat} {data : NativeRecursorData} {levels : List VLevel}
    (signature : NativeConstantSignature data levels)
    (original : sourceEnv.IsDefEqStrong U [] (signature.type.instL levels)
      (signature.type.instL levels) (.sort level)) (count : Nat) :
    (∃ u, sourceEnv.IsDefEqStrong U (signature.domains.take count).reverse
      (wrapForalls (signature.domains.drop count) signature.result)
      (wrapForalls (signature.domains.drop count) signature.result) (.sort u)) ∧
    (∀ (bound : count < signature.domains.length),
      ∃ u, sourceEnv.IsDefEqStrong U (signature.domains.take count).reverse
        signature.domains[count] signature.domains[count] (.sort u)) := by
  have payload := signature.prefixPayload ⟨level, original⟩ original.sourcePiFormation.1 count
  exact ⟨payload.1.1, fun bound => (payload.2 bound).1⟩

/-- The next registered domain is the literal head of the remaining telescope. -/
theorem NativeConstantSignature.prefixResidual_cons
    {data : NativeRecursorData} {levels : List VLevel}
    (signature : NativeConstantSignature data levels)
    (origin : signature.domains[count]? = some domain) :
    wrapForalls (signature.domains.drop count) signature.result =
      .forallE domain (wrapForalls (signature.domains.drop (count + 1)) signature.result) := by
  obtain ⟨bound, same⟩ := List.getElem?_eq_some_iff.mp origin
  rw [List.drop_eq_getElem_cons bound, same]
  rfl

/-- The next original source context is the same literal extension used by
paired substitution and fitting, with no context conversion inserted. -/
theorem NativeConstantSignature.prefixContext_cons
    {data : NativeRecursorData} {levels : List VLevel}
    (signature : NativeConstantSignature data levels)
    (origin : signature.domains[count]? = some domain) :
    (signature.domains.take (count + 1)).reverse = domain :: (signature.domains.take count).reverse := by
  rw [List.take_add_one, origin]
  simp

/-- The instantiated residual's codomain advances by the actual appended
argument; this holds for arbitrary dependent suffix syntax. -/
theorem NativeConstantSignature.prefixResidual_inst
    {data : NativeRecursorData} {levels : List VLevel}
    (signature : NativeConstantSignature data levels)
    (arguments : List VExpr) (value : VExpr) (count : Nat) :
    ((wrapForalls (signature.domains.drop (count + 1)) signature.result).subst
      (nativeCaptureSubst arguments).lift).inst value =
      (wrapForalls (signature.domains.drop (count + 1)) signature.result).subst
        (nativeCaptureSubst (arguments ++ [value])) := by
  rw [nativeCaptureSubst_append, inst_lift_cons]

private theorem eta_spine (n : Nat) (fn : VExpr) :
    nativeEtaBody n fn = mkApps (fn.liftN n) (vars n 0) := by
  induction n generalizing fn with
  | zero => simp [nativeEtaBody, vars, mkApps, liftN_zero]
  | succ n ih =>
    rw [nativeEtaBody, ih]
    have hv : vars (n+1) 0 = .bvar n :: vars n 0 := by
      simp only [vars, List.range_succ, List.reverse_append, List.reverse_singleton,
        List.singleton_append, List.map_cons, Nat.zero_add]
    rw [hv]
    simp only [lift, liftN, liftN_liftN, Nat.add_comm 1]
    rfl

private theorem capture_vars (arguments : List VExpr) :
    (vars arguments.length 0).map (·.subst (nativeCaptureSubst arguments)) = arguments := by
  apply List.ext_getElem
  · simp [vars]
  · intro i hi hi'
    have hj : arguments.length - 1 - i < arguments.length := by omega
    have he : arguments.length - 1 - (arguments.length - 1 - i) = i := by omega
    simp [vars, List.getElem_reverse, instantiateParams, subst, hj, he]

/-- Pair an arbitrary supplied native prefix at its exact remaining dependent
telescope. The result path is obtained from that residual's own formation,
not by comparing the endpoint typings. -/
theorem NativeConstantSignature.prefixArgumentsEqual
    {env : VEnv} {U : Nat} {target : List VExpr}
    (henv : env.Ordered) (hTarget : OnCtx target (env.IsType U))
    {data : NativeRecursorData} {levels : List VLevel}
    (signature : NativeConstantSignature data levels)
    (registered : NativeRecursorRegistered env data)
    (levelsWF : ∀ level ∈ levels, level.WF U) (levelLength : levels.length = data.uvars)
    {count : Nat} (bound : count ≤ signature.domains.length)
    {left right : List VExpr}
    (leftLength : left.length = count) (rightLength : right.length = count)
    (arguments : Ctx.SubstEq env U target (nativeCaptureSubst left)
      (nativeCaptureSubst right) (signature.domains.take count).reverse) :
    env.IsDefEq U target (mkApps (.const data.name levels) left)
      (mkApps (.const data.name levels) right)
      ((wrapForalls (signature.domains.drop count) signature.result).subst (nativeCaptureSubst left)) ∧
    TypeConversion env U target
      ((wrapForalls (signature.domains.drop count) signature.result).subst (nativeCaptureSubst left))
      ((wrapForalls (signature.domains.drop count) signature.result).subst (nativeCaptureSubst right)) := by
  have constant : env.HasType U [] (.const data.name levels)
      (wrapForalls (signature.domains.take count)
        (wrapForalls (signature.domains.drop count) signature.result)) := by
    rw [← split_telescope, ← telescope_eq signature.telescope]
    exact .const (registered.recursorType signature.typeOrigin) levelsWF levelLength
  obtain ⟨context, opened⟩ := HasType.native_open henv (by trivial) constant
  have taken : (signature.domains.take count).length = count := by
    simp only [List.length_take, Nat.min_eq_left bound]
  simp only [List.append_nil, eta_spine, liftN, taken] at context opened
  have raw := opened.substDF henv context hTarget arguments
  simp only [subst_mkApps, subst_const, ← leftLength, capture_vars] at raw
  rw [leftLength, ← rightLength, capture_vars] at raw
  obtain ⟨u, formed⟩ := opened.isType henv context
  exact ⟨by simpa only [rightLength] using raw,
    .single (formed.substDF henv context hTarget arguments)⟩

end Lean4Lean.AnchoredSource.Adapted
