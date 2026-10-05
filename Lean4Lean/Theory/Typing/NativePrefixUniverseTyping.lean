import Lean4Lean.Theory.Typing.NativePrefixUniverses
import Lean4Lean.Theory.Typing.NativeDeltaReduction

/-! Universe specialization of the checked singleton replay. Zero-source
unfolding is stable under specialization, although its complementary
nonzero iota guard need not be. -/

namespace Lean4Lean.VEnv
open VExpr InductiveSignature InductiveSignature.NativeRecursorData

theorem nativeEtaBody_instL (n : Nat) (source : VExpr) (packed : List VLevel) :
    (nativeEtaBody n source).instL packed = nativeEtaBody n (source.instL packed) := by
  induction n generalizing source with
  | zero => rfl
  | succ n ih => simp only [nativeEtaBody, VExpr.instL, VExpr.instL_liftN, ih]

theorem NativeSpineMatch.instL (hw : ∀ level ∈ packed, level.WF U')
    (H : NativeSpineMatch env U Γ actual expected) :
    NativeSpineMatch env U' (Γ.map (VExpr.instL packed)) (actual.instL packed) (expected.instL packed) := by
  obtain ⟨name, levels, levels', args, args', rfl, rfl, hw₀, hw₁, heq, hargs⟩ := H
  refine ⟨name, levels.map (·.inst packed), levels'.map (·.inst packed), args.map (VExpr.instL packed),
    args'.map (VExpr.instL packed), VExpr.instL_mkApps .., VExpr.instL_mkApps ..,
    List.forall_mem_map.2 (fun _ _ => .inst hw),
    List.forall_mem_map.2 (fun _ _ => .inst hw), ?_, ?_⟩
  · apply List.forall₂_map_left_iff.mpr
    apply List.forall₂_map_right_iff.mpr
    exact Lean4Lean.List.Forall₂.imp (fun _ _ h => VLevel.inst_congr_l h) heq
  · apply List.forall₂_map_left_iff.mpr
    apply List.forall₂_map_right_iff.mpr
    induction hargs with
    | nil => exact .nil
    | cons h hs ih => exact .cons (h.instL hw) ih

theorem NativePrefixReplay.instL (hw : ∀ level ∈ packed, level.WF U')
    (H : NativePrefixReplay env U Γ source program) :
    NativePrefixReplay env U' (Γ.map (VExpr.instL packed)) (source.instL packed) (program.instL packed) := by
  refine {
    source_typed := ?_
    remaining_nonempty := ?_
    equation_present := H.equation_present
    equation_body := H.equation_body
    levels_wf := ?_
    levels_length := ?_
    captures_length := ?_
    captures_typed := ?_
    major_prop := ?_
    native_lhs := ?_ }
  · rw [PrefixProgram.type_instL]
    exact H.source_typed.instL hw
  · intro hnil
    apply H.remaining_nonempty
    exact List.map_eq_nil_iff.mp hnil
  · simp only [PrefixProgram.instL, List.mem_map]
    intro level ⟨old, _, heq⟩
    subst level
    exact VLevel.WF.inst hw
  · simpa only [PrefixProgram.instL, List.length_map] using H.levels_length
  · simpa only [PrefixProgram.instL, List.length_map] using H.captures_length
  · intro j hj hd
    have hj' : j < program.captures.length := by simpa only [PrefixProgram.instL, List.length_map] using hj
    have ht := (H.captures_typed j hj' hd).instL hw
    simp only [PrefixProgram.instL, List.getElem_map]
    simp only [List.map_append, List.map_reverse, ← instantiateParams_eq_instOuter,
      instantiateParams_instL, VExpr.instL_instL, List.map_take] at ht
    simp only [instantiateParams_eq_instOuter] at ht
    exact ht
  · obtain ⟨proposition, hp, hm, hc⟩ := H.major_prop
    refine ⟨proposition.instL packed, ?_, ?_, ?_⟩
    · simpa only [PrefixProgram.instL, List.map_append, List.map_reverse, VExpr.instL, VLevel.inst] using hp.instL hw
    · simpa only [PrefixProgram.instL, List.map_append, List.map_reverse, VExpr.instL] using hm.instL hw
    · simpa only [PrefixProgram.instL, List.map_append, List.map_reverse, VExpr.instL] using hc.instL hw
  · have hmatch := H.native_lhs.instL hw
    simp only [PrefixProgram.instL, List.length_map]
    simpa only [List.map_append, List.map_reverse, VExpr.instL, VExpr.instL_liftN,
      nativeEtaBody_instL, ← instantiateParams_eq_instOuter, instantiateParams_instL,
      VExpr.instL_instL] using hmatch

theorem NativeDeltaRule.instL {levels packed : List VLevel}
    (hw : ∀ level ∈ packed, level.WF U')
    (H : NativeDeltaRule env U registry Γ recName levels args rhs) :
    NativeDeltaRule env U' registry (Γ.map (VExpr.instL packed)) recName
      (levels.map (·.inst packed)) (args.map (VExpr.instL packed)) (rhs.instL packed) := by
  cases H with
  | intro hl hr hn hlarge hlevels hz hg replay =>
    have hg' := prefixProgram_instL hg hw
    have replay' := replay.instL hw
    simp only [VExpr.instL_mkApps, VExpr.instL] at replay'
    rw [← PrefixProgram.rhs_instL]
    refine .intro hl hr hn hlarge ?_ ?_ hg' replay'
    · simp only [List.mem_map]
      intro level ⟨old, _, heq⟩
      subst level
      exact VLevel.WF.inst hw
    · simpa only [NativeRecursorData.sourceLevel, VLevel.inst_inst, VLevel.inst]
        using VLevel.inst_congr_l (ls := packed) hz

end Lean4Lean.VEnv
