import Lean4Lean.Theory.Typing.AnchoredDataRelations
import Lean4Lean.Theory.Typing.AnchoredNativePrefixFits
import Lean4Lean.Theory.Typing.AnchoredNativePrefixPlan
import Lean4Lean.Theory.Typing.ProjectionLemmas

/-! Primitive projections of a literal constructor are produced from its
original declared argument substitution. Dependent field types are moved
along the preceding argument pairs, never recovered by type uniqueness. -/

namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

theorem Ctx.SubstEq.nativeTake
    {env : VEnv} {U : Nat} {target domains : List VExpr} {left right : List VExpr}
    (leftLength : left.length = domains.length) (rightLength : right.length = domains.length)
    (raw : Ctx.SubstEq env U target (nativeCaptureSubst left)
      (nativeCaptureSubst right) domains.reverse)
    {count : Nat} (bound : count ≤ domains.length) :
    Ctx.SubstEq env U target (nativeCaptureSubst (left.take count))
      (nativeCaptureSubst (right.take count)) (domains.take count).reverse := by
  have split : domains.reverse =
      (domains.drop count).reverse ++ (domains.take count).reverse := by
    rw [← List.reverse_append, List.take_append_drop]
  rw [split] at raw
  have restricted := Ctx.SubstEq.nativePrefix raw
  have leftShift : Subst.lift_l (.skipN .refl (domains.length - count))
      (nativeCaptureSubst left) = nativeCaptureSubst (left.take count) := by
    simpa only [leftLength] using nativeCaptureSubst_prefix left count (by omega)
  have rightShift : Subst.lift_l (.skipN .refl (domains.length - count))
      (nativeCaptureSubst right) = nativeCaptureSubst (right.take count) := by
    simpa only [rightLength] using nativeCaptureSubst_prefix right count (by omega)
  simpa only [List.length_reverse, List.length_drop, leftShift, rightShift] using restricted

theorem Ctx.SubstEq.nativeArgument
    {env : VEnv} {U : Nat} {target domains arguments : List VExpr}
    (length : arguments.length = domains.length)
    (raw : Ctx.SubstEq env U target (nativeCaptureSubst arguments)
      (nativeCaptureSubst arguments) domains.reverse)
    {position : Nat} (bound : position < domains.length) :
    ∃ level, env.HasType U (domains.take position).reverse domains[position] (.sort level) ∧
      env.HasType U target arguments[position]
        (domains[position].subst (nativeCaptureSubst (arguments.take position))) := by
  have initial := Ctx.SubstEq.nativeTake length length raw (count := position + 1) (by omega)
  have context : (domains.take (position + 1)).reverse =
      domains[position] :: (domains.take position).reverse := by
    rw [List.take_add_one, List.getElem?_eq_getElem bound]
    simp
  have values : arguments.take (position + 1) = arguments.take position ++ [arguments[position]] := by
    rw [List.take_add_one, List.getElem?_eq_getElem (by omega)]
    rfl
  rw [context, values, nativeCaptureSubst_append] at initial
  cases initial with
  | cons tail formation typed => exact ⟨_, formation, typed⟩

/-- The prefix reconstructed by primitive projections has the exact
declared dependent types. Each field also retains its actual `projDF`
origin and `projIota` equation at the original argument's assigned type. -/
theorem literalProjectionPrefix
    {env : VEnv} {U : Nat} {target : List VExpr}
    (henv : env.Ordered) (hTarget : OnCtx target (env.IsType U))
    {info : VProjectionInfo} {name : Name} {domains : List VExpr} {result : VExpr}
    (registered : env.projections name info)
    (shape : info.ctorType = wrapForalls domains result)
    {levels : List VLevel}
    (levelsWF : ∀ level ∈ levels, level.WF U)
    (levelCount : levels.length = info.uvars)
    (ctorClosed : info.ctorType.Closed)
    (relevant : (info.resultLevel.inst levels).IsNeverZero)
    {arguments indices : List VExpr}
    (argumentCount : arguments.length = domains.length)
    (paramBound : info.nparams ≤ domains.length)
    (indexCount : indices.length = info.nindices)
    (original : Ctx.SubstEq env U target (nativeCaptureSubst arguments)
      (nativeCaptureSubst arguments) (domains.map (·.instL levels)).reverse)
    (majorTyped : env.HasType U target (mkApps (.const info.ctorName levels) arguments)
      (mkApps (.const name levels) (arguments.take info.nparams ++ indices)))
    (count : Nat) (bound : info.nparams + count ≤ domains.length) :
    Ctx.SubstEq env U target
      (nativeCaptureSubst (arguments.take (info.nparams + count)))
      (nativeCaptureSubst (arguments.take info.nparams ++ (List.range count).map
        (fun index => .proj name index (mkApps (.const info.ctorName levels) arguments))))
      ((domains.map (·.instL levels)).take (info.nparams + count)).reverse ∧
    (∀ index (before : index < count),
      Nonempty (RankedData.ProjectionOrigin env U target info name index
        (mkApps (.const info.ctorName levels) arguments)
        (mkApps (.const name levels) (arguments.take info.nparams ++ indices))
        ((domains[info.nparams + index].instL levels).subst
          (nativeCaptureSubst (arguments.take (info.nparams + index))))) ∧
      env.IsDefEq U target (.proj name index (mkApps (.const info.ctorName levels) arguments))
        arguments[info.nparams + index]
        ((domains[info.nparams + index].instL levels).subst
          (nativeCaptureSubst (arguments.take (info.nparams + index))))) := by
  have fullLength : arguments.length = (domains.map (·.instL levels)).length := by
    simpa only [List.length_map] using argumentCount
  have paramCount : (arguments.take info.nparams).length = info.nparams := by
    simp only [List.length_take, Nat.min_eq_left (show info.nparams ≤ arguments.length by omega)]
  induction count with
  | zero =>
    constructor
    · simpa only [Nat.add_zero, List.range_zero, List.map_nil, List.append_nil] using
        Ctx.SubstEq.nativeTake fullLength fullLength original
          (count := info.nparams) (by simpa only [List.length_map] using paramBound)
    · intro index impossible
      omega
  | succ count ih =>
    obtain ⟨previous, previousOrigins⟩ := ih (by omega)
    have fieldBound : info.nparams + count < domains.length := by omega
    obtain ⟨fieldLevel, sourceFormation, fieldTyped⟩ :=
      Ctx.SubstEq.nativeArgument fullLength original
        (position := info.nparams + count) (by simpa only [List.length_map] using fieldBound)
    simp only [List.getElem_map] at sourceFormation fieldTyped
    have domainEq := sourceFormation.substDF henv previous.wf hTarget previous
    simp only [subst_sort] at domainEq
    have selected := info.fieldType_eq_instOuter shape levelCount paramCount fieldBound
      (typeName := name) (major := mkApps (.const info.ctorName levels) arguments)
    rw [instOuter_eq_subst] at selected
    change info.fieldType name levels (arguments.take info.nparams) count
      (mkApps (.const info.ctorName levels) arguments) =
      some ((domains[info.nparams + count].instL levels).subst
        (nativeCaptureSubst (arguments.take info.nparams ++ (List.range count).map
          (fun index => .proj name index (mkApps (.const info.ctorName levels) arguments))))) at selected
    have projectionTyped := IsDefEq.projDF registered levelsWF levelCount paramCount indexCount
      selected domainEq.hasType.2 majorTyped majorTyped ctorClosed (Or.inl relevant)
    have iota := IsDefEq.projIota registered projectionTyped
      (List.getElem?_eq_getElem (show info.nparams + count < arguments.length by omega))
      (.defeqDF domainEq fieldTyped)
    have atOriginal := IsDefEq.defeqDF domainEq.symm iota
    constructor
    · have context : ((domains.map (·.instL levels)).take (info.nparams + (count + 1))).reverse =
          domains[info.nparams + count].instL levels ::
            ((domains.map (·.instL levels)).take (info.nparams + count)).reverse := by
        rw [show info.nparams + (count + 1) = (info.nparams + count) + 1 by omega,
          List.take_add_one, List.getElem?_eq_getElem (by simpa only [List.length_map] using fieldBound)]
        simp
      have oldValues : arguments.take (info.nparams + (count + 1)) =
          arguments.take (info.nparams + count) ++ [arguments[info.nparams + count]] := by
        rw [show info.nparams + (count + 1) = (info.nparams + count) + 1 by omega,
          List.take_add_one, List.getElem?_eq_getElem (by omega)]
        rfl
      rw [context, oldValues, List.range_succ, List.map_append, List.map_singleton,
        ← List.append_assoc, nativeCaptureSubst_append, nativeCaptureSubst_append]
      exact .cons previous sourceFormation atOriginal.symm
    · intro index before
      by_cases earlier : index < count
      · exact previousOrigins index earlier
      · have same : index = count := by omega
        subst index
        refine ⟨⟨{
          registered := registered
          levels := levels
          levelsWF := levelsWF
          levelCount := levelCount
          params := arguments.take info.nparams
          paramCount := paramCount
          indexArgs := indices
          indexCount := indexCount
          sourceMajor := mkApps (.const info.ctorName levels) arguments
          fieldType := _
          fieldLevel := fieldLevel
          selected := selected
          formation := domainEq.hasType.2
          familyPath := .refl
          majorEq := majorTyped
          ctorClosed := ctorClosed
          guard := .inl relevant
          fieldPath := .single domainEq.symm }⟩, atOriginal⟩

end Lean4Lean.AnchoredSource.Adapted
