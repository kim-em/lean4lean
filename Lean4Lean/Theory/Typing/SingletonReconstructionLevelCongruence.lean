import Lean4Lean.Theory.Typing.ProjectionLevelCongruence
import Lean4Lean.Theory.Inductive.SingletonReconstruction

/-! Equivalent occurrence universes and arguments preserve singleton
reconstruction. Field-sort annotations are held fixed, as required by the
program's literal-zero selector branch; canonical reconstruction supplies
zeros for these annotations. -/

namespace Lean4Lean.InductiveSignature.CaseSchema
open VExpr VEnv
variable {data data' : ProjectionData}

structure ProjectionFunction.LevelEquiv (U : Nat) (fn fn' : ProjectionFunction) : Prop where
  target : fn.targetLevel = fn'.targetLevel
  value : EqUpToLevels U fn.value fn'.value
  type : EqUpToLevels U fn.type fn'.type

private theorem levels_append {R : α → β → Prop}
    (H : List.Forall₂ R a b) (H' : List.Forall₂ R a' b') :
    List.Forall₂ R (a ++ a') (b ++ b') := by
  induction H with
  | nil => exact H'
  | cons h hs ih => exact .cons h ih

private theorem vars_levels (n k : Nat) : List.Forall₂ (EqUpToLevels U) (vars n k) (vars n k) := by
  apply List.forall₂_map_left_iff.mpr
  apply List.forall₂_map_right_iff.mpr
  exact Lean4Lean.List.Forall₂.rfl (fun _ _ => .bvar)

private theorem wrapLams_levels (H : List.Forall₂ (EqUpToLevels U) ds ds')
    (he : EqUpToLevels U e e') : EqUpToLevels U (wrapLams ds e) (wrapLams ds' e') := by
  induction H with
  | nil => exact he
  | cons h hs ih => exact .lam h ih

private theorem wrapForalls_levels (H : List.Forall₂ (EqUpToLevels U) ds ds')
    (he : EqUpToLevels U e e') : EqUpToLevels U (wrapForalls ds e) (wrapForalls ds' e') := by
  induction H with
  | nil => exact he
  | cons h hs ih => exact .forallE h ih

theorem ProjectionData.LevelEquiv.fieldIndex (H : data.LevelEquiv U data') :
    data.fieldIndex field = data'.fieldIndex field := by
  have hf := Lean4Lean.List.Forall₂.length_eq H.fields
  unfold ProjectionData.fieldIndex
  rw [hf]
  suffices ∀ start, ((data.constructorIndices.zipIdx start).find? (fun (index, _) =>
      match index with
      | .bvar i => i == data'.fields.length - 1 - field
      | _ => false)).map Prod.snd =
      ((data'.constructorIndices.zipIdx start).find? (fun (index, _) =>
      match index with
      | .bvar i => i == data'.fields.length - 1 - field
      | _ => false)).map Prod.snd from this 0
  intro start
  have hci := H.constructorIndices
  generalize data.constructorIndices = es at hci ⊢
  generalize data'.constructorIndices = es' at hci ⊢
  induction hci generalizing start with
  | nil => rfl
  | cons h hs ih =>
    cases h <;> simp [List.zipIdx_cons, List.find?, ih]
    split <;> simp_all

theorem ProjectionData.LevelEquiv.arguments (H : data.LevelEquiv U data') :
    data.arguments = data'.arguments := by
  simp [ProjectionData.arguments, Lean4Lean.List.Forall₂.length_eq H.params,
    Lean4Lean.List.Forall₂.length_eq H.indices]

private theorem arguments_levels (data : ProjectionData) :
    List.Forall₂ (EqUpToLevels U) data.arguments data.arguments :=
  levels_append (levels_append (vars_levels _ _) (vars_levels _ _)) (.cons .bvar .nil)

theorem ProjectionData.LevelEquiv.fieldTarget (H : data.LevelEquiv U data')
    (hd : EqUpToLevels U domain domain')
    (hp : List.Forall₂ (ProjectionFunction.LevelEquiv U) previous previous') :
    EqUpToLevels U (data.fieldTarget domain previous) (data'.fieldTarget domain' previous') := by
  apply hd.instantiateParams_args
  apply levels_append
  · rw [Lean4Lean.List.Forall₂.length_eq H.params, Lean4Lean.List.Forall₂.length_eq H.indices]
    exact vars_levels _ _
  · induction hp with
    | nil => exact .nil
    | cons h hs ih =>
      refine .cons (h.value.mkApps_args ?_) ih
      rw [H.arguments]
      exact arguments_levels _

theorem ProjectionData.LevelEquiv.indexSelector (H : data.LevelEquiv U data')
    (hd : EqUpToLevels U domain domain')
    (hp : List.Forall₂ (ProjectionFunction.LevelEquiv U) previous previous') :
    (data.indexSelector domain target previous index).LevelEquiv U
      (data'.indexSelector domain' target previous' index) := by
  have ht := H.fieldTarget hd hp
  have hds := levels_append (levels_append H.params H.indices) (.cons H.major .nil)
  refine ⟨rfl, wrapLams_levels hds ?_, wrapForalls_levels hds ht⟩
  rw [Lean4Lean.List.Forall₂.length_eq H.indices]
  exact .bvar

theorem ProjectionData.LevelEquiv.proofSelector (H : data.LevelEquiv U data')
    (hl : ∀ l ∈ levels, l.WF U) (hl' : ∀ l ∈ levels', l.WF U)
    (he : List.Forall₂ (· ≈ ·) levels levels')
    (hd : EqUpToLevels U domain domain')
    (hp : List.Forall₂ (ProjectionFunction.LevelEquiv U) previous previous') :
    (data.proofSelector block owner levels domain previous).LevelEquiv U
      (data'.proofSelector block owner levels' domain' previous') := by
  have ht := H.fieldTarget hd hp
  have hds := levels_append (levels_append H.params H.indices) (.cons H.major .nil)
  have hm := wrapLams_levels (levels_append H.indices (.cons H.major .nil)) ht
  have hminor : EqUpToLevels U
      (wrapLams data.fields (.bvar (data.fields.length - 1 - previous.length)))
      (wrapLams data'.fields (.bvar (data'.fields.length - 1 - previous'.length))) := by
    apply wrapLams_levels H.fields
    rw [Lean4Lean.List.Forall₂.length_eq H.fields, Lean4Lean.List.Forall₂.length_eq hp]
    exact .bvar
  refine ⟨rfl, wrapLams_levels hds ?_, wrapForalls_levels hds ht⟩
  apply EqUpToLevels.mkApps_args
  · exact .elim (by simpa using And.intro (show VLevel.WF U .zero from trivial) hl)
      (by simpa using And.intro (show VLevel.WF U .zero from trivial) hl') (.cons rfl he)
  · rw [← Lean4Lean.List.Forall₂.length_eq H.params, ← Lean4Lean.List.Forall₂.length_eq H.indices]
    exact levels_append (levels_append (levels_append (vars_levels _ _)
      (.cons hm.weakN (.cons hminor.weakN .nil))) (vars_levels _ _)) (.cons .bvar .nil)

theorem ProjectionData.LevelEquiv.reconstructionPrefix (H : data.LevelEquiv U data')
    (hl : ∀ l ∈ levels, l.WF U) (hl' : ∀ l ∈ levels', l.WF U)
    (he : List.Forall₂ (· ≈ ·) levels levels')
    (hd : List.Forall₂ (EqUpToLevels U) domains domains')
    (hp : List.Forall₂ (ProjectionFunction.LevelEquiv U) previous previous')
    (hg : data.reconstructionPrefix block owner levels domains targets previous = some output) :
    ∃ output', data'.reconstructionPrefix block owner levels' domains' targets previous' = some output' ∧
      List.Forall₂ (ProjectionFunction.LevelEquiv U) output output' := by
  induction targets generalizing domains domains' previous previous' with
  | nil => cases hd with
    | nil => cases hg; exact ⟨previous', rfl, hp⟩
    | cons => cases hg
  | cons target targets ih =>
    cases hd with
    | nil => cases hg
    | @cons domain domain' domains domains' hed heds =>
      simp only [ProjectionData.reconstructionPrefix] at hg ⊢
      rw [← Lean4Lean.List.Forall₂.length_eq hp, ← H.fieldIndex,
        ← Lean4Lean.List.Forall₂.length_eq H.indices]
      split at hg
      · rename_i index hindex
        split at hg <;> try contradiction
        rename_i hbound
        rw [if_pos hbound]
        exact ih heds (levels_append hp (.cons (H.indexSelector hed hp) .nil)) hg
      · rename_i hindex
        cases target <;> try contradiction
        exact ih heds (levels_append hp (.cons (H.proofSelector hl hl' he hed hp) .nil)) hg

/-- Transport actual successful reconstruction with its fixed sort annotations. -/
theorem singletonReconstructAt_levels {schema : CaseSchema} {params : List VExpr}
    {owner : Fin schema.signature.families.size}
    (hg : schema.singletonReconstructAt block owner U levels targets params indices major = some output)
    (hl' : ∀ l ∈ levels', l.WF U)
    (he : List.Forall₂ (· ≈ ·) levels levels')
    (hp : List.Forall₂ (EqUpToLevels U) params params')
    (hi : List.Forall₂ (EqUpToLevels U) indices indices')
    (hm : EqUpToLevels U major major') :
    ∃ output', schema.singletonReconstructAt block owner U levels' targets params' indices' major' = some output' ∧
      EqUpToLevels U output output' := by
  unfold singletonReconstructAt at hg ⊢
  split at hg <;> try contradiction
  rename_i hguard
  simp only [Bool.not_eq_true', Bool.not_eq_false, Bool.and_eq_true,
    List.all_eq_true, decide_eq_true_eq] at hguard
  have hlevels' : levels'.all (fun l => decide (l.WF U)) = true := by simpa using hl'
  have htargets : targets.all (fun l => decide (l.WF U)) = true := by simpa using hguard.2
  rw [hlevels', htargets]
  simp only [Bool.true_and, Bool.not_true, Bool.false_eq_true, if_false]
  simp only [bind, Option.bind_eq_some_iff] at hg
  obtain ⟨data, hdata, hg⟩ := hg
  obtain ⟨data', hdata', hed⟩ := projectionData_levels hguard.1 hl' he hdata
  simp only [bind, hdata', Option.bind_some,
    ← Lean4Lean.List.Forall₂.length_eq hp, ← Lean4Lean.List.Forall₂.length_eq hi,
    ← Lean4Lean.List.Forall₂.length_eq hed.params, ← Lean4Lean.List.Forall₂.length_eq hed.indices]
  split at hg <;> try contradiction
  rename_i harity
  rw [if_neg harity]
  simp only [Option.bind_eq_some_iff] at hg
  obtain ⟨fields, hf, hg⟩ := hg
  cases hg
  obtain ⟨fields', hf', hef⟩ := hed.reconstructionPrefix hguard.1 hl' he hed.fields .nil hf
  simp only [hf', Option.bind_some]
  refine ⟨_, rfl, hed.constructor.instantiateParams_args (levels_append hp ?_)⟩
  have hargs := levels_append (levels_append hp hi) (.cons hm .nil)
  clear hf hf'
  induction hef with
  | nil => exact .nil
  | cons h hs ih => exact .cons (h.value.mkApps_args hargs) ih

end Lean4Lean.InductiveSignature.CaseSchema
