import Lean4Lean.Theory.Typing.NativeRuleRegistration

namespace Lean4Lean.InductiveSignature.CaseSchema

theorem Certified.constructor_index_unique {schema : CaseSchema}
    (H : schema.Certified base source block)
    {owner : Fin schema.signature.families.size}
    {i j : Fin schema.signature.constructors.size}
    (hi : schema.signature.constructors[i].owner = owner)
    (hj : schema.signature.constructors[j].owner = owner)
    (hn : schema.restoration.headName schema.signature.constructors[i].name =
      schema.restoration.headName schema.signature.constructors[j].name) : i = j := by
  have hp := H.constructor_names_nodup owner
  simp only [view, List.toList_toArray, List.map_filterMap] at hp
  have hp := List.pairwise_filterMap.mp hp
  have hp := List.pairwise_iff_getElem.mp hp
  have hneq (a b : Fin schema.signature.constructors.size) (hab : a.val < b.val)
      (ha : schema.signature.constructors[a].owner = owner)
      (hb : schema.signature.constructors[b].owner = owner) :
      schema.restoration.headName schema.signature.constructors[a].name ≠
        schema.restoration.headName schema.signature.constructors[b].name := by
    have h := hp a.val b.val (by simp) (by simp) hab
    simp only [Array.getElem_toList] at h
    simp only [Fin.getElem_fin] at ha hb ⊢
    exact h _ (by simp [ha, caseConstructor]) _ (by simp [hb, caseConstructor])
  apply Fin.ext
  by_cases h : i.val = j.val
  · exact h
  · rcases Nat.lt_or_gt_of_ne h with h | h
    · exact (hneq i j h hi hj hn).elim
    · exact (hneq j i h hj hi hn.symm).elim

end Lean4Lean.InductiveSignature.CaseSchema

namespace Lean4Lean.VEnv
open InductiveSignature

/-- The same registered native owner has one constructor index for each
restored constructor name, including specialized container constructors. -/
theorem NativeRecursorRegistered.constructor_index_unique
    (H : NativeRecursorRegistered env data)
    {i j : Fin data.schema.signature.constructors.size}
    (hi : data.schema.signature.constructors[i].owner = data.owner)
    (hj : data.schema.signature.constructors[j].owner = data.owner)
    (hn : data.schema.restoration.headName data.schema.signature.constructors[i].name =
      data.schema.restoration.headName data.schema.signature.constructors[j].name) : i = j := by
  obtain ⟨base, installBase, source, expanded, g, auxiliaries, block, installed,
    hdata, hprior, _, hr, hf, _⟩ := H
  have hc : data.schema.Certified base source block :=
    ⟨expanded, g, auxiliaries, hdata, hprior, hr, hf⟩
  exact hc.constructor_index_unique hi hj hn

end Lean4Lean.VEnv
