import Lean4Lean.Theory.Typing.NativeRuleRegistration
import Lean4Lean.Theory.Typing.AnchoredNativeSyntaxTransport
import Lean4Lean.Theory.Inductive.NativeCommonPrefix

/-! The generated recursor result at its equation argument tuple is the
literal declared equation result. Restoration and level instantiation retain
this identity; no comparison of independently assigned types is used. -/
namespace Lean4Lean.InductiveSignature
open VExpr NativeRecursorData
open private restoration_vars from Lean4Lean.Theory.Inductive.CaseReductionLemmas
open private registeredInstance from Lean4Lean.Theory.Typing.NativeRuleRegistration
set_option backward.isDefEq.respectTransparency false

private theorem restore_foralls {r : Restoration}
    {domains : List VExpr} {body restored : VExpr}
    (h : r.expr (wrapForalls domains body) = some restored) :
    ∃ domains' body', r.expr body = some body' ∧
      restored = wrapForalls domains' body' ∧ domains'.length = domains.length := by
  induction domains generalizing restored with
  | nil => exact ⟨[], restored, h, rfl, rfl⟩
  | cons domain rest ih =>
    change (do let d ← r.expr domain; let b ← r.expr (wrapForalls rest body)
               pure (.forallE d b)) = some restored at h
    simp only [bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
    obtain ⟨d, hd, b, hb, rfl⟩ := h
    obtain ⟨ds, b', hbody, rfl, hlen⟩ := ih hb
    exact ⟨d :: ds, b', hbody, rfl, by simp [hlen]⟩

private theorem takeForalls_wrap (domains : List VExpr) (body : VExpr) :
    NativeRecursorData.takeForalls domains.length (wrapForalls domains body) = some (domains, body) := by
  induction domains with
  | nil => rfl
  | cons d ds ih =>
    change (do let (ds', body') ← NativeRecursorData.takeForalls ds.length (wrapForalls ds body)
               pure (d :: ds', body')) = some (d :: ds, body)
    rw [ih]
    rfl

private theorem restore_motive (r : Restoration) (motive indices : Nat) :
    r.expr (mkApps (.bvar motive) (vars indices 1 ++ [.bvar 0])) =
      some (mkApps (.bvar motive) (vars indices 1 ++ [.bvar 0])) := by
  change Restoration.expr.go r _ [] = _
  rw [restoration_mkApps]
  simp only [List.mapM_append, restoration_vars, List.mapM_cons, List.mapM_nil,
    Restoration.expr, Restoration.expr.go, mkApps, List.foldl_nil,
    bind, Option.bind_some, List.append_nil]
  rfl

private theorem restored_recursor_result
    {s : InductiveSignature} {g : Instance s} {r : Restoration}
    {owner : Fin s.families.size} {type result : VExpr} {domains : List VExpr}
    {levels : List VLevel}
    (restored : r.expr (g.recursorType owner) = some type)
    (parsed : NativeRecursorData.takeForalls
      (s.params.length + s.families.size + s.constructors.size + s.families[owner].indices.length + 1)
      (type.instL levels) = some (domains, result)) :
    result = mkApps (.bvar (s.families[owner].indices.length + 1 + s.constructors.size +
      (s.families.size - 1 - owner.val))) (vars s.families[owner].indices.length 1 ++ [.bvar 0]) := by
  unfold Instance.recursorType at restored
  obtain ⟨ds, b, hb, ht, hd⟩ := restore_foralls restored
  simp only [insertBinders, List.length_map, List.length_zipIdx] at hb
  have resultEq := Option.some.inj ((restore_motive r _ _).symm.trans hb)
  subst b
  have len : ds.length = s.params.length + s.families.size + s.constructors.size +
      s.families[owner].indices.length + 1 := by
    simpa only [List.length_append, Instance.params, Instance.motives, Instance.minors,
      insertBinders, List.length_map, List.length_zipIdx, Array.length_toList,
      List.length_singleton] using hd
  have levelsWrap : (wrapForalls ds (mkApps (.bvar
      (s.families[owner].indices.length + 1 + s.constructors.size + (s.families.size - 1 - owner.val)))
      (vars s.families[owner].indices.length 1 ++ [.bvar 0]))).instL levels =
      wrapForalls (ds.map (·.instL levels)) (mkApps (.bvar
      (s.families[owner].indices.length + 1 + s.constructors.size + (s.families.size - 1 - owner.val)))
      (vars s.families[owner].indices.length 1 ++ [.bvar 0])) := by
    have hw : ∀ (ds : List VExpr) (body : VExpr), (wrapForalls ds body).instL levels =
        wrapForalls (ds.map (·.instL levels)) (body.instL levels) := by
      intro ds body
      induction ds with
      | nil => rfl
      | cons d ds ih => exact congrArg (VExpr.forallE (d.instL levels)) ih
    rw [hw]
    simp [instL_mkApps, vars, List.map_map, Function.comp_def, instL]
  rw [ht, levelsWrap, ← len, ← List.length_map (f := fun e : VExpr => e.instL levels),
    takeForalls_wrap] at parsed
  exact (congrArg Prod.snd (Option.some.inj parsed)).symm

private theorem restored_native_payload {r : Restoration} {name : Name} {levels : List VLevel}
    {pre nf offset : Nat} {suffix : List VExpr} {lhs type : VExpr}
    (separate : ∀ h ∈ r.heads, h.auxiliary ≠ name)
    (hl : r.expr (mkApps (.const name levels) (vars pre nf ++ suffix)) = some lhs)
    (ht : r.expr (mkApps (.bvar (nf + offset)) suffix) = some type) :
    ∃ suffix', lhs = mkApps (.const (r.recursorName name) levels) (vars pre nf ++ suffix') ∧
      type = mkApps (.bvar (nf + offset)) suffix' := by
  have noneHead : r.heads.find? (fun h => h.auxiliary == name) = none := by
    apply List.find?_eq_none.mpr
    intro head hh
    simpa using separate head hh
  change Restoration.expr.go r _ [] = _ at hl ht
  rw [restoration_mkApps] at hl ht
  simp only [List.mapM_append, restoration_vars, bind, Option.bind_some] at hl
  cases hs : suffix.mapM r.expr with
  | none => simp [hs] at hl
  | some args =>
    simp only [hs, Option.bind_some, List.append_nil, Restoration.expr.go, noneHead] at hl ht
    exact ⟨args, (Option.some.inj hl).symm, (Option.some.inj ht).symm⟩

private theorem extract_wrap_const {name : Name} {levels : List VLevel} {lhs rhs type : VExpr}
    (hhead : lhs.getAppFnArgs.1 = .const name levels) (domains : List VExpr) :
    CaseSchema.EquationBody.extract (wrapLams domains lhs) (wrapLams domains rhs)
      (wrapForalls domains type) = some ⟨domains, lhs, rhs, type⟩ := by
  induction domains with
  | nil => cases lhs <;> first | rfl | cases hhead
  | cons d ds ih =>
    change (do
      if d ≠ d ∨ d ≠ d then none else
      let body ← CaseSchema.EquationBody.extract (wrapLams ds lhs) (wrapLams ds rhs)
        (wrapForalls ds type)
      pure { body with domains := d :: body.domains }) = _
    simp [ih]

private theorem restored_equation_result
    {s : InductiveSignature} {g : Instance s} {r : Restoration}
    {index : Fin s.constructors.size} {equation : VDefEq} {body : CaseSchema.EquationBody}
    (separate : ∀ h ∈ r.heads, h.auxiliary ≠ g.recursorName s.constructors[index].owner)
    (restored : r.equation (g.equation index) = some equation)
    (extracted : CaseSchema.EquationBody.extract equation.lhs equation.rhs equation.type = some body) :
    ∃ suffix,
      body.lhs = mkApps (.const (r.recursorName (g.recursorName s.constructors[index].owner))
        (VLevel.params g.uvars))
        (vars (s.params.length + s.families.size + s.constructors.size)
          s.constructors[index].fields.length ++ suffix) ∧
      body.type = mkApps (.bvar (s.constructors[index].fields.length + s.constructors.size +
        (s.families.size - 1 - s.constructors[index].owner.val))) suffix := by
  have parts := Restoration.equation_parts restored
  obtain ⟨ds, lhs, rhs, type, hl, hr, ht, heql, heqr, heqt, hlen⟩ :=
    restored_common_telescope parts.1 parts.2.1 parts.2.2
  obtain ⟨suffix, hlhs, htype⟩ := restored_native_payload (lhs := lhs) (type := type)
    (pre := s.params.length + s.families.size + s.constructors.size)
    (nf := s.constructors[index].fields.length)
    (offset := s.constructors.size + (s.families.size - 1 - s.constructors[index].owner.val))
    separate
    (by simpa only [Instance.equation, Instance.recursorHead, Nat.add_assoc, List.append_assoc] using hl)
    (by simpa only [Instance.equation, Nat.add_assoc] using ht)
  have hhead : lhs.getAppFnArgs.1 = .const
      (r.recursorName (g.recursorName s.constructors[index].owner)) (VLevel.params g.uvars) := by
    rw [hlhs, spine_mkApps_exact _ _ rfl]
  have exactBody : body = ⟨ds, lhs, rhs, type⟩ := by
    rw [heql, heqr, heqt, extract_wrap_const hhead] at extracted
    exact (Option.some.inj extracted).symm
  cases exactBody
  exact ⟨suffix, hlhs, by simpa only [Nat.add_assoc] using htype⟩

private theorem substitute_motive_result
    (pre nf offset indices : Nat) (suffix : List VExpr) (σ : Subst)
    (hoffset : offset < pre) (hlen : suffix.length = indices + 1) :
    instantiateParams
      (mkApps (.bvar (indices + 1 + offset)) (vars indices 1 ++ [.bvar 0]))
      ((vars pre nf ++ suffix).map (·.subst σ)) =
      (mkApps (.bvar (nf + offset)) suffix).subst σ := by
  let args := (vars pre nf ++ suffix).map (·.subst σ)
  have argsLen : args.length = pre + (indices + 1) := by simp [args, vars, hlen]
  have hhead : instantiateParams (.bvar (indices + 1 + offset)) args = σ (nf + offset) := by
    have hi : indices + 1 + offset < args.length := by omega
    have hj : args.length - 1 - (indices + 1 + offset) = pre - 1 - offset := by omega
    simp only [instantiateParams, subst_bvar, dif_pos hi, hj]
    simp only [args, List.getElem_map]
    have hshort : pre - 1 - offset < (vars pre nf).length := by
      simp only [vars, List.length_map, List.length_reverse, List.length_range]
      omega
    rw [List.getElem_append_left hshort]
    simp only [vars, List.getElem_map, List.getElem_reverse, List.length_range,
      List.getElem_range, subst_bvar]
    congr 1
    omega
  have hargs : (vars indices 1 ++ [VExpr.bvar 0]).map (fun e => instantiateParams e args) =
      suffix.map (·.subst σ) := by
    apply List.ext_getElem
    · simp [vars, hlen]
    · intro i hi hj
      have iBound : i < indices + 1 := by simpa only [List.length_map, hlen] using hj
      simp only [List.getElem_map]
      by_cases hsmall : i < indices
      · rw [List.getElem_append_left (by simpa [vars] using hsmall)]
        simp only [vars, List.getElem_map, List.getElem_reverse, List.length_range, List.getElem_range]
        have hindex : 1 + (indices - 1 - i) < args.length := by omega
        have heq : args.length - 1 - (1 + (indices - 1 - i)) = pre + i := by omega
        simp only [instantiateParams, subst_bvar, dif_pos hindex, heq, args, List.getElem_map]
        rw [List.getElem_append_right (by simp [vars])]
        simp only [vars, List.length_map, List.length_reverse, List.length_range, Nat.add_sub_cancel_left]
      · have he : i = indices := by omega
        subst i
        rw [List.getElem_append_right (by simp [vars])]
        simp only [vars, List.length_map, List.length_reverse, List.length_range,
          Nat.sub_self, List.getElem_cons_zero]
        have hzero : 0 < args.length := by omega
        have heq : args.length - 1 - 0 = pre + indices := by omega
        simp only [instantiateParams, subst_bvar, dif_pos hzero, heq, args, List.getElem_map]
        rw [List.getElem_append_right (by simp [vars])]
        simp only [vars, List.length_map, List.length_reverse, List.length_range, Nat.add_sub_cancel_left]
  change (mkApps _ _).subst _ = _
  rw [subst_mkApps, subst_mkApps]
  exact congr (congrArg mkApps hhead) hargs

private theorem vars_instL (count below : Nat) (levels : List VLevel) :
    (vars count below).map (·.instL levels) = vars count below := by
  simp only [vars, List.map_map, instL, Function.comp_def]

private theorem restored_result_bridge
    {s : InductiveSignature} {g : Instance s} {r : Restoration}
    {owner : Fin s.families.size} {index : Fin s.constructors.size}
    {type result : VExpr} {domains : List VExpr} {levels : List VLevel}
    {equation : VDefEq} {body : CaseSchema.EquationBody}
    (ownerEq : s.constructors[index].owner = owner)
    (separate : ∀ h ∈ r.heads, h.auxiliary ≠ g.recursorName owner)
    (recursor : r.expr (g.recursorType owner) = some type)
    (equationRestored : r.equation (g.equation index) = some equation)
    (extracted : CaseSchema.EquationBody.extract equation.lhs equation.rhs equation.type = some body)
    (parsed : NativeRecursorData.takeForalls
      (s.params.length + s.families.size + s.constructors.size + s.families[owner].indices.length + 1)
      (type.instL levels) = some (domains, result))
    (arity : (body.lhs.instL levels).getAppFnArgs.2.length =
      s.params.length + s.families.size + s.constructors.size + s.families[owner].indices.length + 1)
    (σ : Subst) :
    instantiateParams result (((body.lhs.instL levels).getAppFnArgs.2).map (·.subst σ)) =
      (body.type.instL levels).subst σ := by
  have resultEq := restored_recursor_result recursor parsed
  obtain ⟨suffix, hlhs, htype⟩ := restored_equation_result
    (by simpa only [ownerEq] using separate) equationRestored extracted
  rw [ownerEq] at hlhs htype
  have arguments : (body.lhs.instL levels).getAppFnArgs.2 =
      vars (s.params.length + s.families.size + s.constructors.size)
        s.constructors[index].fields.length ++ suffix.map (·.instL levels) := by
    rw [hlhs, instL_mkApps]
    simp only [instL, List.map_append, vars_instL, VExpr.getAppFnArgs_mkApps_const]
  have suffixLength : (suffix.map (·.instL levels)).length = s.families[owner].indices.length + 1 := by
    rw [arguments] at arity
    simp only [List.length_append, vars, List.length_map, List.length_reverse, List.length_range] at arity ⊢
    omega
  have offsetBound : s.constructors.size + (s.families.size - 1 - owner.val) <
      s.params.length + s.families.size + s.constructors.size := by
    have := owner.isLt
    omega
  rw [resultEq, arguments, htype, instL_mkApps]
  simp only [instL]
  simpa only [Nat.add_assoc] using substitute_motive_result
    (s.params.length + s.families.size + s.constructors.size)
    s.constructors[index].fields.length
    (s.constructors.size + (s.families.size - 1 - owner.val))
    s.families[owner].indices.length (suffix.map (·.instL levels)) σ offsetBound suffixLength

private theorem singleton_origin {data : NativeRecursorData} {equation : VDefEq}
    (selected : data.singletonEquation = some equation) :
    ∃ index : Fin data.schema.signature.constructors.size,
      data.schema.signature.constructors[index].owner = data.owner ∧
      data.schema.restoration.equation (data.nativeInstance.equation index) = some equation := by
  unfold NativeRecursorData.singletonEquation at selected
  dsimp only at selected
  split at selected <;> try contradiction
  rename_i index hfilter
  refine ⟨index, ?_, selected⟩
  have member : index ∈ (List.finRange data.schema.signature.constructors.size).filter
      (fun i => data.schema.signature.constructors[i].owner == data.owner) := by
    rw [hfilter]
    exact .head _
  simpa only [beq_iff_eq] using (List.mem_filter.mp member).2

/-- Exact registered generation identifies the equation's declared result
with the recursor result at its complete reconstructed argument tuple. -/
theorem NativeRecursorData.saturatedProgram_resultBridge
    {env : VEnv} {data : NativeRecursorData} {program : SaturatedProgram data}
    {levels : List VLevel} {arguments : List VExpr}
    {type result : VExpr} {domains : List VExpr}
    (registered : VEnv.NativeRecursorRegistered env data)
    (selected : data.saturatedProgram levels arguments = some program)
    (registeredType : data.recursorType = some type)
    (telescope : NativeRecursorData.takeForalls (data.majorOffset + 1)
      (type.instL levels) = some (domains, result))
    (σ : Subst) :
    instantiateParams result (((program.equationBody.lhs.instL levels).getAppFnArgs.2).map (·.subst σ)) =
      (program.equationBody.type.instL levels).subst σ := by
  obtain ⟨base, installBase, source, expanded, auxiliaries, block, installed, hdata, hprior, hr, hi, he⟩ :=
    registeredInstance registered
  have spec := saturatedProgram_spec selected
  obtain ⟨index, ownerEq, equation⟩ := singleton_origin spec.2.2.2.2.2.2.2.2.1
  have separate : ∀ head ∈ data.schema.restoration.heads,
      head.auxiliary ≠ data.nativeInstance.recursorName data.owner := by
    rw [hr]
    exact hdata.heads_not_recursors data.owner
  apply restored_result_bridge ownerEq separate registeredType equation
    spec.2.2.2.2.2.2.2.2.2.1 telescope
  have hlen := AnchoredSource.Adapted.nativeEquationArguments_length
    (witnesses := []) selected
  simp only [AnchoredSource.Adapted.nativeEquationArguments, List.length_map, spec.1] at hlen
  exact hlen

end Lean4Lean.InductiveSignature

namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv InductiveSignature NativeRecursorData

/-- The signature and selected equation agree at arbitrary witnessed captures.
This is syntax equality and needs neither capture typing nor type uniqueness. -/
theorem NativeConstantSignature.equationResult
    {env : VEnv} {data : NativeRecursorData} {program : SaturatedProgram data}
    {levels : List VLevel} {arguments : List VExpr}
    (signature : NativeConstantSignature data levels)
    (registered : NativeRecursorRegistered env data)
    (selected : data.saturatedProgram levels arguments = some program)
    (witnesses : List VExpr) :
    signature.result.subst (nativeCaptureSubst (nativeEquationArguments program witnesses)) =
      (program.equationBody.type.instL levels).subst (nativeCaptureSubst witnesses) := by
  have result := saturatedProgram_resultBridge registered selected signature.typeOrigin
    signature.telescope (nativeCaptureSubst witnesses)
  change instantiateParams signature.result (nativeEquationArguments program witnesses) = _
  simpa only [nativeEquationArguments, (saturatedProgram_spec selected).1] using result

end Lean4Lean.AnchoredSource.Adapted
