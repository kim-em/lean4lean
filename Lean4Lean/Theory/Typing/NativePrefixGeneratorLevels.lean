import Lean4Lean.Theory.Typing.NativePrefixLevelCongruence
import Lean4Lean.Theory.Inductive.QuotPrefixProgram
import Lean4Lean.Theory.Typing.SingletonReconstructionLevelCongruence

namespace Lean4Lean.InductiveSignature.NativeRecursorData
open VEnv VExpr

theorem supplyType_levels (ha : List.Forall₂ (EqUpToLevels U) args args')
    (ht : EqUpToLevels U type type') (H : supplyType args type = some output) :
    ∃ output', supplyType args' type' = some output' ∧ EqUpToLevels U output output' := by
  induction ha generalizing type type' output with
  | nil => cases H; exact ⟨_, rfl, ht⟩
  | cons ha hs ih =>
    cases ht <;> try contradiction
    rename_i hd hb
    exact ih (EqUpToLevels.instN ha hb) H

theorem takeForalls_levels (ht : EqUpToLevels U type type')
    (H : takeForalls count type = some (domains, result)) :
    ∃ domains' result', takeForalls count type' = some (domains', result') ∧
      List.Forall₂ (EqUpToLevels U) domains domains' ∧ EqUpToLevels U result result' := by
  induction count generalizing type type' domains result with
  | zero => cases H; exact ⟨[], _, rfl, .nil, ht⟩
  | succ n ih =>
    cases ht <;> try contradiction
    rename_i hd hb
    simp only [takeForalls, bind, Option.bind_eq_some_iff] at H
    obtain ⟨⟨ds, body⟩, htake, H⟩ := H
    cases H
    obtain ⟨ds', body', htake', hds, hbody⟩ := ih hb htake
    exact ⟨_, _, by simp only [takeForalls, bind, htake', Option.bind_some]; rfl, .cons hd hds, hbody⟩

end Lean4Lean.InductiveSignature.NativeRecursorData

namespace Lean4Lean.VEnv
open VExpr InductiveSignature

private theorem levels_getD {R : α → β → Prop} (H : List.Forall₂ R a b)
    (hd : R default₁ default₂) (i : Nat) : R (a[i]?.getD default₁) (b[i]?.getD default₂) := by
  induction H generalizing i with
  | nil => exact hd
  | cons h hs ih =>
    cases i with
    | zero => exact h
    | succ i => exact ih i

private theorem levels_take {R : α → β → Prop} (H : List.Forall₂ R a b) (n : Nat) :
    List.Forall₂ R (a.take n) (b.take n) := by
  induction H generalizing n with
  | nil => simp
  | cons h hs ih =>
    cases n with
    | zero => exact .nil
    | succ n => exact .cons h (ih n)

private theorem levels_drop {R : α → β → Prop} (H : List.Forall₂ R a b) (n : Nat) :
    List.Forall₂ R (a.drop n) (b.drop n) := by
  induction H generalizing n with
  | nil => simp
  | cons h hs ih =>
    cases n with
    | zero => exact .cons h hs
    | succ n => exact ih n

private theorem levels_append {R : α → β → Prop} (H : List.Forall₂ R a b)
    (H' : List.Forall₂ R a' b') : List.Forall₂ R (a ++ a') (b ++ b') := by
  induction H with
  | nil => exact H'
  | cons h hs ih => exact .cons h ih

private theorem levels_vars (n k : Nat) : List.Forall₂ (EqUpToLevels U) (vars n k) (vars n k) := by
  unfold vars
  apply Lean4Lean.List.Forall₂.rfl
  intro e he
  simp only [List.mem_reverse, List.mem_map] at he
  obtain ⟨i, _, rfl⟩ := he
  exact .bvar

private theorem levels_lift (H : List.Forall₂ (EqUpToLevels U) args args') (n : Nat) :
    List.Forall₂ (EqUpToLevels U) (args.map (·.liftN n)) (args'.map (·.liftN n)) := by
  apply List.forall₂_map_left_iff.mpr
  apply List.forall₂_map_right_iff.mpr
  exact Lean4Lean.List.Forall₂.imp (fun _ _ h => h.weakN) H

end Lean4Lean.VEnv

namespace Lean4Lean.QuotPrefixProgram
open VEnv VExpr InductiveSignature InductiveSignature.NativeRecursorData

theorem witness_levels (hl : l.WF U) (hl' : l'.WF U) (he : l ≈ l') :
    EqUpToLevels U (witness l) (witness l') := by
  have H := EqUpToLevels.instL_expr (witness (.param 0))
    (ls := [l]) (ls' := [l']) (by simpa) (by simpa) (.cons he .nil)
  simpa [witness, VExpr.instL_wrapLams, VExpr.instL_mkApps, VExpr.instL, VLevel.inst,
    VExpr.lift, VExpr.liftN] using H

theorem generate_levels {levels levels' : List VLevel}
    (hl : ∀ level ∈ levels, level.WF U) (hl' : ∀ level ∈ levels', level.WF U)
    (he : List.Forall₂ (· ≈ ·) levels levels')
    (ha : List.Forall₂ (EqUpToLevels U) args args')
    (H : generate levels args = some program) :
    ∃ program', generate levels' args' = some program' ∧ PrefixProgram.LevelEquiv U program program' := by
  have hlen := Lean4Lean.List.Forall₂.length_eq he
  have hargslen := Lean4Lean.List.Forall₂.length_eq ha
  unfold generate at H ⊢
  simp only [← hlen, ← hargslen]
  split at H <;> try contradiction
  rename_i hguard
  rw [if_neg hguard]
  simp only [bind, Option.bind_eq_some_iff] at H
  obtain ⟨residual, hsupply, ⟨domains, result⟩, htake, body, hbody, H⟩ := H
  cases H
  obtain ⟨residual', hsupply', hres⟩ := supplyType_levels ha
    (EqUpToLevels.instL_expr _ hl hl' he) hsupply
  obtain ⟨domains', result', htake', hdoms, hresult⟩ := takeForalls_levels hres htake
  let remaining := 6 - args.length
  have hall := levels_append (levels_lift ha remaining) (levels_vars (U := U) remaining 0)
  have hdefault : EqUpToLevels U (default : VExpr) default := .sort trivial trivial rfl
  have halpha := levels_getD hall hdefault 0
  have hrelation := levels_getD hall hdefault 1
  have hmajor := levels_getD hall hdefault 5
  have hlevel := levels_getD he (show VLevel.zero ≈ .zero from rfl) 0
  have hlevelWF : (levels[0]?.getD VLevel.zero).WF U := by
    cases hh : levels[0]? with
    | none => trivial
    | some u => exact hl u (List.mem_of_getElem? hh)
  have hlevelWF' : (levels'[0]?.getD VLevel.zero).WF U := by
    cases hh : levels'[0]? with
    | none => trivial
    | some u => exact hl' u (List.mem_of_getElem? hh)
  have hproof := EqUpToLevels.mkApps_args (witness_levels hlevelWF hlevelWF' hlevel)
    (.cons halpha (.cons hrelation (.cons hmajor .nil)))
  have hconstructor := EqUpToLevels.mkApps_args
    (EqUpToLevels.const (c := ``Quot.mk) (by simpa using hlevelWF) (by simpa using hlevelWF') (.cons hlevel .nil))
    (.cons halpha (.cons hrelation (.cons hproof .nil)))
  have hcaptures := levels_append (levels_take hall 5) (.cons hproof .nil)
  simp only [bind, hsupply', htake', hbody, Option.bind_some]
  exact ⟨_, rfl, ⟨hdoms, hresult, hconstructor, rfl, rfl, hcaptures, he, hl'⟩⟩

end Lean4Lean.QuotPrefixProgram


namespace Lean4Lean.InductiveSignature.NativeRecursorData
open VEnv VExpr CaseSchema

private theorem sourceLevels_related {levels levels' : List VLevel} (data : NativeRecursorData)
    (he : List.Forall₂ (· ≈ ·) levels levels') :
    List.Forall₂ (· ≈ ·) (data.sourceLevels levels) (data.sourceLevels levels') := by
  apply List.forall₂_map_left_iff.mpr
  apply List.forall₂_map_right_iff.mpr
  exact Lean4Lean.List.Forall₂.rfl fun _ _ => VLevel.inst_congr rfl he

private theorem sourceLevels_wf {levels : List VLevel} (data : NativeRecursorData)
    (hl : ∀ level ∈ levels, level.WF U) : ∀ level ∈ data.sourceLevels levels, level.WF U :=
  List.forall_mem_map.mpr fun _ _ => VLevel.WF.inst hl

theorem reconstruct_levels {data : NativeRecursorData} {levels levels' : List VLevel}
    (hl' : ∀ level ∈ levels', level.WF U)
    (he : List.Forall₂ (· ≈ ·) levels levels')
    (ha : List.Forall₂ (EqUpToLevels U) args args')
    (H : data.reconstruct U levels targets args = some output) :
    ∃ output', data.reconstruct U levels' targets args' = some output' ∧ EqUpToLevels U output output' := by
  have hlen := Lean4Lean.List.Forall₂.length_eq he
  have hargslen := Lean4Lean.List.Forall₂.length_eq ha
  unfold reconstruct at H ⊢
  simp only [← hlen, ← hargslen]
  split at H <;> try contradiction
  rename_i hguard
  rw [if_neg hguard]
  simp only [bind, Option.bind_eq_some_iff] at H
  obtain ⟨major, hmajor, H⟩ := H
  have hb : data.majorOffset < args.length := by
    simp at hguard
    omega
  have hb' : data.majorOffset < args'.length := by omega
  have hemajor := Lean4Lean.List.forall₂_getElem ha data.majorOffset hb hb'
  have hget : args'[data.majorOffset]? = some args'[data.majorOffset] := List.getElem?_eq_getElem hb'
  have hget₀ : major = args[data.majorOffset] := by
    rw [List.getElem?_eq_getElem hb] at hmajor
    exact Option.some.inj hmajor.symm
  subst major
  obtain ⟨out, hg, hout⟩ := singletonReconstructAt_levels H (sourceLevels_wf data hl')
    (sourceLevels_related data he) (levels_take ha _) (levels_take (levels_drop ha _) _) hemajor
  exact ⟨out, by simp only [bind, hget, Option.bind_some]; exact hg, hout⟩

theorem reconstructCanonical_levels {data : NativeRecursorData} {levels levels' : List VLevel}
    (hl : ∀ level ∈ levels, level.WF U) (hl' : ∀ level ∈ levels', level.WF U)
    (he : List.Forall₂ (· ≈ ·) levels levels')
    (ha : List.Forall₂ (EqUpToLevels U) args args')
    (H : data.reconstructCanonical U levels args = some output) :
    ∃ output', data.reconstructCanonical U levels' args' = some output' ∧ EqUpToLevels U output output' := by
  unfold reconstructCanonical at H ⊢
  simp only [bind, Option.bind_eq_some_iff] at H
  obtain ⟨source, hsource, H⟩ := H
  obtain ⟨source', hsource', hesource⟩ := projectionData_levels
    (sourceLevels_wf data hl) (sourceLevels_wf data hl') (sourceLevels_related data he) hsource
  simp only [bind, hsource', Option.bind_some, ← Lean4Lean.List.Forall₂.length_eq hesource.fields]
  exact reconstruct_levels hl' he ha H

theorem prefixProgram_levels {data : NativeRecursorData} {levels levels' : List VLevel}
    (hl : ∀ level ∈ levels, level.WF U) (hl' : ∀ level ∈ levels', level.WF U)
    (he : List.Forall₂ (· ≈ ·) levels levels')
    (ha : List.Forall₂ (EqUpToLevels U) args args')
    (H : data.prefixProgram U levels args = some program) :
    ∃ program', data.prefixProgram U levels' args' = some program' ∧ PrefixProgram.LevelEquiv U program program' := by
  have hlen := Lean4Lean.List.Forall₂.length_eq he
  have hargslen := Lean4Lean.List.Forall₂.length_eq ha
  unfold prefixProgram at H ⊢
  simp only [← hlen, ← hargslen]
  split at H <;> try contradiction
  rename_i hguard
  rw [if_neg hguard]
  simp only [bind, Option.bind_eq_some_iff] at H
  obtain ⟨nativeType, htype, residual, hsupply, ⟨domains, result⟩, htake,
    constructor, hconstructor, source, hsource, fields, hfields,
    equation, hequation, body, hbody, H⟩ := H
  split at H <;> try contradiction
  rename_i hcaptures
  cases H
  obtain ⟨residual', hsupply', hres⟩ := supplyType_levels ha
    (EqUpToLevels.instL_expr _ hl hl' he) hsupply
  obtain ⟨domains', result', htake', hdoms, hresult⟩ := takeForalls_levels hres htake
  let remaining := data.majorOffset + 1 - args.length
  have hall := levels_append (levels_lift ha remaining) (levels_vars (U := U) remaining 0)
  obtain ⟨constructor', hconstructor', heconstructor⟩ := reconstructCanonical_levels hl hl' he hall hconstructor
  obtain ⟨source', hsource', hesource⟩ := projectionData_levels
    (sourceLevels_wf data hl) (sourceLevels_wf data hl') (sourceLevels_related data he) hsource
  obtain ⟨fields', hfields', hefields⟩ := hesource.reconstructionPrefix
    (sourceLevels_wf data hl) (sourceLevels_wf data hl') (sourceLevels_related data he) hesource.fields .nil hfields
  have hfields'' := hfields'
  rw [Lean4Lean.List.Forall₂.length_eq hesource.fields] at hfields''
  have hprojectionArgs := levels_append (levels_append (levels_take hall data.numParams)
    (levels_take (levels_drop hall data.indexOffset) data.numIndices)) (.cons (.bvar (U := U) (i := 0)) .nil)
  have hfieldApps : List.Forall₂ (EqUpToLevels U)
      (fields.map fun field => VExpr.mkApps field.value
        ((args.map (·.liftN remaining) ++ vars remaining 0).take data.numParams ++
          ((args.map (·.liftN remaining) ++ vars remaining 0).drop data.indexOffset).take data.numIndices ++ [.bvar 0]))
      (fields'.map fun field => VExpr.mkApps field.value
        ((args'.map (·.liftN remaining) ++ vars remaining 0).take data.numParams ++
          ((args'.map (·.liftN remaining) ++ vars remaining 0).drop data.indexOffset).take data.numIndices ++ [.bvar 0])) := by
    clear hfields hfields' hfields'' hcaptures
    induction hefields with
    | nil => exact .nil
    | cons h hs ih => exact .cons (h.value.mkApps_args hprojectionArgs) ih
  have hecaptures := levels_append (levels_take hall data.indexOffset) hfieldApps
  dsimp only [remaining] at hconstructor'
  simp only [bind, htype, hsupply', htake', hconstructor', hsource', hfields'', hequation, hbody, Option.bind_some]
  have hcaplen := Lean4Lean.List.Forall₂.length_eq hecaptures
  dsimp only [remaining] at hcaplen
  rw [← hcaplen, if_neg hcaptures]
  exact ⟨_, rfl, ⟨hdoms, hresult, heconstructor, rfl, rfl, hecaptures, he, hl'⟩⟩

end Lean4Lean.InductiveSignature.NativeRecursorData
