import Lean4Lean.Theory.Typing.ShapeModel.EnvSigRules

/-!
# Coherence of the semantic signature of a well-formed environment
-/

namespace Lean4Lean.ShapeModel
open InductiveSignature

variable {env : VEnv}

theorem rule_pair (H : env.WF) (h₁ : EnvRule env r₁) (h₂ : EnvRule env r₂)
    (hh : r₁.head = r₂.head) : r₁ = r₂ ∨ RulePairSpine env r₁ r₂ := by
  cases hc : r₁.head with
  | const n => exact const_pair H h₁ h₂ hh hc
  | elim b o => exact elim_pair H h₁ h₂ hh hc

/-- The constructors of a registered structure's family: only the structure constructor
(under the schema compatibility of `SchemaStructCompat`). -/
theorem ctor_of_struct_family (H : env.WF) (hC : SchemaStructCompat env)
    (hproj : env.projections s info) (hc : IsCtor env c) (hf : ctorFamily env c = some s) :
    c = info.ctorName := by
  have fromTable : ctorOf env c ≠ none → c = info.ctorName := by
    intro h
    obtain ⟨k, hk⟩ := Option.ne_none_iff_exists'.mp h
    have hfam := (ctorOf_shape' H hk).family
    rw [hf] at hfam
    cases hfam
    have hmem := (famOf_mem_ctors H (famOf_projection H hproj)).mpr ⟨k, hk, rfl⟩
    simpa using hmem
  rcases hc with h | ⟨⟨key, schema, hreg, owner, rules, df, fn, ls, args, hgen, hdf, hm⟩, -⟩
  · exact fromTable h
  · rcases generic_major_origin H hreg hgen hdf hm with h | ⟨ho, hmem⟩
    · exact fromTable h
    · rw [hf] at ho
      rw [hC hreg hproj owner ho] at hmem
      simpa using hmem

theorem forall₂_equiv_refl : ∀ l : List VLevel, List.Forall₂ (· ≈ ·) l l
  | [] => .nil
  | _ :: l => .cons (VLevel.equiv_def'.2 rfl) (forall₂_equiv_refl l)

theorem EnvRule.head_not_rigid (H : env.WF) (hrig : env.Rigid c) (hr : EnvRule env r) :
    r.head ≠ .const c := by
  have HT := envTables_inv H
  intro hh
  rcases hr with ⟨v, hv, _, rfl⟩ | ⟨hq, _, rfl⟩ | ⟨df, hdf, data, hd, index, ho, hg, rfl⟩ |
    ⟨_, _, _, _, _, _, _, _, rfl⟩
  · simp only [defRule_head, Head.const.injEq] at hh
    exact hrig _ hv _ (by rw [← hh]; rfl)
  · simp only [majorRule_head, Head.const.injEq] at hh
    exact hrig _ hq _ (by rw [← hh]; exact quot_head)
  · simp only [majorRule_head, Head.const.injEq] at hh
    exact hrig _ hdf _ (by rw [← hh]; exact native_head HT hd ho hg)
  · simp at hh

/-- The semantic signature of a well-formed environment is coherent. -/
theorem envSig_coherent (H : env.WF) (hC : SchemaStructCompat env) :
    @SemSig.Coherent (envSig env) := by
  letI := envSig env
  constructor
  · intro r₁ r₂ h₁ h₂ hh
    rcases rule_pair H h₁ h₂ hh with rfl | ⟨pre₁, pre₂, c₁, c₂, lv, f₁, f₂, hv₁, hv₂, hl, hm₁, hm₂, _⟩
    · exact ⟨rfl, rfl⟩
    · exact ⟨by simp [hv₁, hv₂, hl], by simp [hm₁, hm₂]⟩
  · intro r₁ r₂ mj₁ mj₂ ci₁ ci₂ h₁ h₂ hh hmj₁ hmj₂ hci₁ hci₂
    rcases rule_pair H h₁ h₂ hh with rfl | ⟨pre₁, pre₂, c₁, c₂, lv, f₁, f₂, _, _, _, hm₁, hm₂, _, hfam, _⟩
    · rw [hmj₁] at hmj₂; cases hmj₂
      change sigCtor env _ = _ at hci₁ hci₂
      rw [hci₁] at hci₂; cases hci₂
      exact ⟨rfl, forall₂_equiv_refl _⟩
    · rw [hm₁] at hmj₁; cases hmj₁
      rw [hm₂] at hmj₂; cases hmj₂
      have e₁ := sigCtor_family hci₁
      have e₂ := sigCtor_family hci₂
      rw [e₁, e₂] at hfam
      exact ⟨Option.some.inj hfam, forall₂_equiv_refl _⟩
  · intro r₁ r₂ mj₁ mj₂ h₁ h₂ hh hmj₁ hmj₂ hc
    rcases rule_pair H h₁ h₂ hh with rfl | ⟨pre₁, pre₂, c₁, c₂, lv, f₁, f₂, _, _, _, hm₁, hm₂, hne, _⟩
    · rfl
    · rw [hm₁] at hmj₁; cases hmj₁
      rw [hm₂] at hmj₂; cases hmj₂
      exact absurd hc hne
  · intro r₁ r₂ h₁ h₂ hh hn₁ _
    rcases rule_pair H h₁ h₂ hh with rfl | ⟨pre₁, pre₂, c₁, c₂, lv, f₁, f₂, _, _, _, hm₁, _⟩
    · rfl
    · rw [hm₁] at hn₁; cases hn₁
  · intro c ci r hci hr
    exact EnvRule.head_not_rigid H ((sigCtor_spec hci).1.rigid H) hr
  · intro c ci c' ci' hs hci hci' hfam
    change sigIsStruct env c = true at hs
    obtain ⟨s, info, hproj, rfl, _⟩ := @of_decide_eq_true _ (Classical.propDecidable _) hs
    have hcs : ctorFamily env info.ctorName = some s :=
      (ctorOf_shape' H (ctorOf_projection H hproj)).family
    have e₁ := sigCtor_family hci
    rw [hcs] at e₁
    have e₂ := sigCtor_family hci'
    rw [hfam, ← Option.some.inj e₁] at e₂
    exact ctor_of_struct_family H hC hproj (sigCtor_spec hci').1 e₂

end Lean4Lean.ShapeModel
