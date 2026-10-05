import Lean4Lean.Theory.Typing.NativePrefixSpecialization
import Lean4Lean.Theory.Typing.SingletonReconstructionLemmas
import Lean4Lean.Theory.Typing.NativeDeltaReduction
import Lean4Lean.Theory.Typing.QuotPrefixReduction
import Batteries.Tactic.OpenPrivate

namespace Lean4Lean.InductiveSignature.CaseSchema
open VExpr VEnv
open private instantiateParams_inst from Lean4Lean.Theory.Typing.NativePrefixSpecialization

theorem singletonReconstructAt_inst {schema : CaseSchema} {params : List VExpr}
    {owner : Fin schema.signature.families.size}
    (H : schema.singletonReconstructAt block owner U levels sorts params indices major = some ctor) :
    schema.singletonReconstructAt block owner U levels sorts
      (params.map (·.inst arg k)) (indices.map (·.inst arg k)) (major.inst arg k) =
      some (ctor.inst arg k) := by
  unfold singletonReconstructAt at H ⊢
  split at H <;> try contradiction
  rename_i hguard
  rw [if_neg hguard]
  simp only [bind, Option.bind_eq_some_iff] at H
  obtain ⟨data, hdata, H⟩ := H
  simp only [bind, hdata, Option.bind_some, List.length_map]
  split at H <;> try contradiction
  rename_i harity
  rw [if_neg harity]
  simp only [Option.bind_eq_some_iff] at H
  obtain ⟨fields, hfields, hresult⟩ := H
  cases hresult
  simp only [hfields, Option.bind_some, Option.pure_def, Option.some.injEq]
  have hd := projectionData_scoped hdata
  have hclosed := data.reconstructionPrefix_closed hd (by simp)
    (by simpa using hd.fields) (by simp) hfields
  have hlen := data.reconstructionPrefix_length hfields
  simp only [List.length_nil, Nat.zero_add] at hlen
  have hp : params.length = data.params.length := by
    by_cases hp : params.length = data.params.length
    · exact hp
    · exact (harity (by simp [hp])).elim
  have hargs : data.constructor.ClosedN
      (params ++ fields.map (fun field => mkApps field.value (params ++ indices ++ [major]))).length := by
    simpa only [List.length_append, List.length_map, hp, hlen] using hd.constructor
  rw [instantiateParams_inst hargs]
  congr 1
  simp only [List.map_append, List.map_map, Function.comp_def, inst_mkApps,
    List.map_cons, List.map_nil]
  congr 1
  apply List.map_congr_left
  intro field hf
  rw [(hclosed field hf).instN_eq (Nat.zero_le _)]

end Lean4Lean.InductiveSignature.CaseSchema

namespace Lean4Lean.InductiveSignature.NativeRecursorData
open VExpr VEnv CaseSchema
variable {levels : List VLevel} {type : VExpr}

theorem supplyType_inst (H : supplyType args type = some output) :
    supplyType (args.map (·.inst arg k)) (type.inst arg k) = some (output.inst arg k) := by
  induction args generalizing type with
  | nil => cases H; rfl
  | cons a args ih =>
    cases type <;> try contradiction
    simp only [supplyType, List.map_cons, VExpr.inst, ← VExpr.inst0_inst_hi]
    exact ih H

theorem reconstruct_inst {data : NativeRecursorData}
    (H : data.reconstruct U levels targets args = some output) :
    data.reconstruct U levels targets (args.map (·.inst arg k)) = some (output.inst arg k) := by
  unfold reconstruct at H ⊢
  simp only [List.length_map]
  split at H <;> try contradiction
  rename_i hguard
  rw [if_neg hguard]
  simp only [bind, Option.bind_eq_some_iff] at H
  obtain ⟨major, hmajor, H⟩ := H
  simp only [List.getElem?_map, hmajor, Option.map_some, bind, Option.bind_some,
    ← List.map_take, ← List.map_drop]
  exact singletonReconstructAt_inst H

theorem reconstructCanonical_inst {data : NativeRecursorData}
    (H : data.reconstructCanonical U levels args = some output) :
    data.reconstructCanonical U levels (args.map (·.inst arg k)) = some (output.inst arg k) := by
  unfold reconstructCanonical at H ⊢
  simp only [bind, Option.bind_eq_some_iff] at H
  obtain ⟨source, hsource, H⟩ := H
  simp only [hsource]
  exact reconstruct_inst H


/-- Substitute an outer term through the remaining dependent telescope. -/
def PrefixProgram.instN (program : PrefixProgram) (arg : VExpr) (k : Nat) : PrefixProgram :=
  { program with
    domains := instDomains program.domains arg k
    result := program.result.inst arg (k + program.domains.length)
    constructor := program.constructor.inst arg (k + program.domains.length)
    captures := program.captures.map (·.inst arg (k + program.domains.length)) }

@[simp] theorem PrefixProgram.type_instN (program : PrefixProgram) :
    (program.instN arg k).type = program.type.inst arg k := by
  simp only [PrefixProgram.instN, PrefixProgram.type, wrapForalls_inst]

open private instantiateParams_inst from Lean4Lean.Theory.Typing.NativePrefixSpecialization

theorem PrefixProgram.rhs_instN (program : PrefixProgram)
    (hclosed : program.equationBody.rhs.ClosedN program.captures.length) :
    (program.instN arg k).rhs = program.rhs.inst arg k := by
  simp only [PrefixProgram.instN, PrefixProgram.rhs, wrapLams_inst,
    instantiateParams_inst (hclosed.instL (ls := program.levels))]

private theorem vars_inst_above (n k : Nat) (arg : VExpr) :
    (vars n 0).map (·.inst arg (k+n)) = vars n 0 := by
  conv => rhs; rw [← List.map_id (l := vars n 0)]
  apply List.map_congr_left
  intro e he
  simp only [vars, List.mem_map, List.mem_reverse, List.mem_range] at he
  obtain ⟨i, hi, rfl⟩ := he
  exact (show (VExpr.bvar (0+i)).ClosedN n from by simpa only [VExpr.ClosedN, Nat.zero_add] using hi).instN_eq (j := k+n) (by omega)

theorem prefixProgram_inst {data : NativeRecursorData} {nativeType : VExpr}
    (htype : data.recursorType = some nativeType) (hclosed : nativeType.Closed)
    (H : data.prefixProgram U levels args = some program) :
    data.prefixProgram U levels (args.map (·.inst arg k)) = some (program.instN arg k) := by
  unfold prefixProgram at H ⊢
  simp only [List.length_map]
  split at H <;> try contradiction
  rename_i hguard
  rw [if_neg hguard]
  simp only [bind, htype, Option.bind_some, Option.bind_eq_some_iff] at H
  obtain ⟨residual, hsupply, ⟨domains, result⟩, htake,
    constructor, hconstructor, source, hsource, fields, hfields,
    equation, hequation, body, hbody, H⟩ := H
  split at H <;> try contradiction
  rename_i hcaptureCount
  cases H
  have hlen := takeForalls_length htake
  have hsupply' := supplyType_inst (arg := arg) (k := k) hsupply
  rw [(hclosed.instL (ls := levels)).instN_eq (Nat.zero_le _)] at hsupply'
  have htake' := takeForalls_instDomains (arg := arg) (k := k) htake
  let remaining := data.majorOffset + 1 - args.length
  have hall :
      (args.map (·.inst arg k)).map (·.liftN remaining) ++ vars remaining 0 =
      (args.map (·.liftN remaining) ++ vars remaining 0).map (·.inst arg (k + remaining)) := by
    simp only [List.map_append, List.map_map, Function.comp_def, vars_inst_above,
      liftN_instN_lo _ _ _ _ _ (Nat.zero_le _), Nat.add_comm remaining k]
  have hconstructor' := reconstructCanonical_inst (arg := arg) (k := k + remaining) hconstructor
  rw [← hall] at hconstructor'
  dsimp only [remaining] at hconstructor'
  have hvarslen (n j : Nat) : (vars n j).length = n := by simp [vars]
  simp only [bind, htype, Option.bind_some, hsupply', htake', hconstructor', hsource,
    hfields, hequation, hbody, List.length_map, List.length_append, List.length_take,
    hvarslen] at hcaptureCount ⊢
  have hscoped := projectionData_scoped hsource
  have hselectors := source.reconstructionPrefix_closed hscoped (by simp)
    (by simpa using hscoped.fields) (by simp) hfields
  rw [if_neg hcaptureCount]
  simp only [Option.pure_def, Option.some.injEq, PrefixProgram.instN, PrefixProgram.mk.injEq,
    hlen, and_true, true_and]
  dsimp only [remaining] at hall
  rw [hall]
  simp only [List.map_append, List.map_map, Function.comp_def, List.map_take]
  congr 1
  apply List.map_congr_left
  intro field hf
  rw [inst_mkApps, (hselectors field hf).instN_eq (Nat.zero_le _)]
  have hn : args.length ≤ data.majorOffset := by
    by_cases hn : args.length ≤ data.majorOffset
    · exact hn
    · exact (hguard (by simp [show data.majorOffset < args.length by omega])).elim
  have hzero : (.bvar 0 : VExpr).inst arg (k + (data.majorOffset + 1 - args.length)) = .bvar 0 := by
    simp [VExpr.inst, instVar, show 0 < k + (data.majorOffset + 1 - args.length) by omega]
  simp only [List.map_append, List.map_take, List.map_drop, List.map_cons,
    List.map_nil, hzero, List.map_map, Function.comp_def]

end Lean4Lean.InductiveSignature.NativeRecursorData

namespace Lean4Lean.VEnv
open VExpr InductiveSignature InductiveSignature.NativeRecursorData
open private instantiateParams_inst from Lean4Lean.Theory.Typing.NativePrefixSpecialization

theorem nativeEtaBody_instN (source arg : VExpr) (n k : Nat) :
    (nativeEtaBody n source).inst arg (k+n) = nativeEtaBody n (source.inst arg k) := by
  induction n generalizing source k with
  | zero => rfl
  | succ n ih =>
    simp only [nativeEtaBody]
    rw [show k + (n+1) = (k+1)+n by omega, ih]
    congr 1
    simp only [VExpr.inst]
    rw [← lift_instN_lo]
    simp [instVar]

theorem NativeSpineMatch.instN (henv : env.WF)
    (W : Ctx.InstN Γ₀ arg A k Γ₁ Γ)
    (harg : HasType env U Γ₀ arg A) (H : NativeSpineMatch env U Γ₁ actual expected) :
    NativeSpineMatch env U Γ (actual.inst arg k) (expected.inst arg k) := by
  obtain ⟨name, levels, levels', args, args', rfl, rfl, hw, hw', heq, hargs⟩ := H
  refine ⟨name, levels, levels', args.map (·.inst arg k), args'.map (·.inst arg k),
    inst_mkApps .., inst_mkApps .., hw, hw', heq, ?_⟩
  apply List.forall₂_map_left_iff.mpr
  apply List.forall₂_map_right_iff.mpr
  exact Lean4Lean.List.Forall₂.imp (fun _ _ h => h.instN henv.ordered W harg) hargs

theorem NativePrefixReplay.instN (henv : env.WF)
    (W : Ctx.InstN Γ₀ arg A k Γ₁ Γ)
    (harg : HasType env U Γ₀ arg A) (H : NativePrefixReplay env U Γ₁ source program) :
    NativePrefixReplay env U Γ (source.inst arg k) (program.instN arg k) := by
  have Wext := Ctx.InstN.reverse program.domains W
  rw [Nat.add_comm program.domains.length k] at Wext
  have hscope := H.templateScope henv
  have hn : 0 < program.domains.length := List.length_pos_iff.mpr H.remaining_nonempty
  refine {
    source_typed := ?_
    remaining_nonempty := ?_
    equation_present := H.equation_present
    equation_body := H.equation_body
    levels_wf := H.levels_wf
    levels_length := H.levels_length
    captures_length := ?_
    captures_typed := ?_
    major_prop := ?_
    native_lhs := ?_ }
  · rw [PrefixProgram.type_instN]
    exact H.source_typed.instN henv.ordered W harg
  · intro he
    have he' := congrArg List.length he
    simp only [PrefixProgram.instN, instDomains_length, List.length_nil] at he'
    omega
  · simpa only [PrefixProgram.instN, List.length_map] using H.captures_length
  · intro j hj hd
    have hj₀ : j < program.captures.length := by simpa only [PrefixProgram.instN, List.length_map] using hj
    have ht := (H.captures_typed j hj₀ hd).instN henv.ordered Wext harg
    have hclosed : (program.equationBody.domains[j].instL program.levels).ClosedN
        (program.captures.take j).length := by
      simpa only [List.length_take, Nat.min_eq_left (Nat.le_of_lt hj₀)] using
        (hscope.2.2 j hd).instL (ls := program.levels)
    rw [← instantiateParams_eq_instOuter, instantiateParams_inst hclosed] at ht
    simp only [PrefixProgram.instN, List.getElem_map, List.map_take, instantiateParams_eq_instOuter] at ht ⊢
    exact ht
  · obtain ⟨proposition, hp, hm, hc⟩ := H.major_prop
    refine ⟨proposition.inst arg (k+program.domains.length), hp.instN henv.ordered Wext harg, ?_,
      hc.instN henv.ordered Wext harg⟩
    have hm' := hm.instN henv.ordered Wext harg
    simpa only [PrefixProgram.instN, VExpr.inst, instVar, if_pos (show 0 < k + program.domains.length by omega)] using hm'
  · have hm := H.native_lhs.instN henv Wext harg
    rw [← instantiateParams_eq_instOuter, instantiateParams_inst (hscope.1.instL (ls := program.levels))] at hm
    have hlength : k + program.domains.length = (k + (program.domains.length-1)) + 1 := by omega
    simp only [VExpr.inst] at hm
    rw [hlength, ← lift_instN_lo, nativeEtaBody_instN] at hm
    simpa only [PrefixProgram.instN, instDomains_length, instantiateParams_eq_instOuter, ← hlength] using hm

theorem NativeDeltaRule.instN {name : Name} {levels : List VLevel}
    (henv : env.WF) (W : Ctx.InstN Γ₀ arg A k Γ₁ Γ)
    (harg : HasType env U Γ₀ arg A)
    (H : NativeDeltaRule env U registry Γ₁ name levels args rhs) :
    NativeDeltaRule env U registry Γ name levels (args.map (·.inst arg k)) (rhs.inst arg k) := by
  cases H with
  | @intro data program hl hr hn ht hw hz hg replay =>
    have hex : ∃ type, data.recursorType = some type := by
      cases hh : data.recursorType with
      | some type => exact ⟨type, rfl⟩
      | none =>
        unfold prefixProgram at hg
        split at hg <;> simp [hh] at hg
    obtain ⟨type, htype⟩ := hex
    have hg' := prefixProgram_inst htype (hr.recursorType_closed henv htype) hg (arg := arg) (k := k)
    have replay' := replay.instN henv W harg
    simp only [inst_mkApps, VExpr.inst] at replay'
    rw [← PrefixProgram.rhs_instN program (replay.templateScope henv).2.1]
    exact .intro hl hr hn ht hw hz hg' replay'

end Lean4Lean.VEnv


namespace Lean4Lean.QuotPrefixProgram
open VExpr VEnv InductiveSignature InductiveSignature.NativeRecursorData

private theorem getD_map_inst (args : List VExpr) (i : Nat) (arg : VExpr) (k : Nat) :
    (args.map (·.inst arg k))[i]?.getD default = (args[i]?.getD default).inst arg k := by
  simp only [List.getElem?_map]
  cases args[i]? <;> rfl

theorem generate_inst {levels : List VLevel}
    (H : generate levels args = some program) :
    generate levels (args.map (·.inst arg k)) = some (program.instN arg k) := by
  unfold generate at H ⊢
  simp only [List.length_map]
  split at H <;> try contradiction
  rename_i hguard
  rw [if_neg hguard]
  simp only [bind, Option.bind_eq_some_iff] at H
  obtain ⟨residual, hsupply, ⟨domains, result⟩, htake, body, hbody, H⟩ := H
  cases H
  have hclosed : quotLiftConst.type.Closed := by decide
  have hsupply' := supplyType_inst (arg := arg) (k := k) hsupply
  rw [(hclosed.instL (ls := levels)).instN_eq (Nat.zero_le _)] at hsupply'
  have htake' := takeForalls_instDomains (arg := arg) (k := k) htake
  have hlen := takeForalls_length htake
  simp only [bind, hsupply', Option.bind_some, htake', hbody, Option.pure_def,
    Option.some.injEq, PrefixProgram.instN, PrefixProgram.mk.injEq, hlen]
  have hall : (args.map (fun e => (e.inst arg k).liftN (6 - args.length)) ++ vars (6 - args.length) 0) =
      (args.map (·.liftN (6 - args.length)) ++ vars (6 - args.length) 0).map
        (·.inst arg (k + (6 - args.length))) := by
    simp only [List.map_append, List.map_map, Function.comp_def, vars_inst_above,
      liftN_instN_lo _ _ _ _ _ (Nat.zero_le _), Nat.add_comm (6 - args.length) k]
  simp only [List.map_map, Function.comp_def]
  rw [hall]
  simp only [getD_map_inst]
  simp only [inst_mkApps, List.map_cons, List.map_nil, List.map_append,
    List.map_take, VExpr.inst, (witness_closed _).instN_eq (Nat.zero_le _), and_self]

end Lean4Lean.QuotPrefixProgram

namespace Lean4Lean.VEnv
open VExpr InductiveSignature.NativeRecursorData

theorem QuotDeltaRule.instN {levels : List VLevel}
    (henv : env.WF) (W : Ctx.InstN Γ₀ arg A k Γ₁ Γ)
    (harg : HasType env U Γ₀ arg A) (H : QuotDeltaRule env U Γ₁ levels args rhs) :
    QuotDeltaRule env U Γ levels (args.map (·.inst arg k)) (rhs.inst arg k) := by
  cases H with
  | @intro program hr hw hz hg replay =>
    have hg' := QuotPrefixProgram.generate_inst (arg := arg) (k := k) hg
    have replay' := replay.instN henv W harg
    simp only [inst_mkApps, VExpr.inst] at replay'
    rw [← PrefixProgram.rhs_instN program (replay.templateScope henv).2.1]
    exact .intro hr hw hz hg' replay'

end Lean4Lean.VEnv
