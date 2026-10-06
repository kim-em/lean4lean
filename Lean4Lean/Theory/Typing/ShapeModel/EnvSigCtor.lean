import Lean4Lean.Theory.Typing.ShapeModel.EnvSig

/-!
# Constructors of the semantic signature of a well-formed environment
-/

namespace Lean4Lean.ShapeModel
open InductiveSignature

variable {env : VEnv}

/-- A registered structure is determined by its constructor (through the constructor table). -/
theorem projection_of_ctorName (H : env.WF) (h₁ : env.projections s₁ info₁)
    (h₂ : env.projections s₂ info₂) (hn : info₁.ctorName = info₂.ctorName) :
    s₁ = s₂ ∧ info₁ = info₂ := by
  have e₁ := ctorOf_projection H h₁
  have e₂ := ctorOf_projection H h₂
  rw [hn, e₂] at e₁
  have hs : s₂ = s₁ := (CtorData.mk.inj (Option.some.inj e₁)).1
  subst hs
  exact ⟨rfl, H.ordered.projections_unique h₁ h₂⟩

theorem structNp_of_proj (H : env.WF) (h : env.projections s info) :
    structNp env info.ctorName = info.nparams := by
  have hex : ∃ info' : VProjectionInfo, (∃ s, env.projections s info') ∧
      info'.ctorName = info.ctorName := ⟨info, ⟨s, h⟩, rfl⟩
  unfold structNp
  rw [dif_pos hex]
  obtain ⟨⟨s', h'⟩, hn⟩ := Classical.choose_spec hex
  rw [(projection_of_ctorName H h' h hn).2]

theorem structNp_eq (H : env.WF) (c : Name) :
    structNp env c = 0 ∨ ∃ s info, env.projections s info ∧ info.ctorName = c ∧
      structNp env c = info.nparams := by
  by_cases hex : ∃ info : VProjectionInfo, (∃ s, env.projections s info) ∧ info.ctorName = c
  · obtain ⟨info, ⟨s, h⟩, rfl⟩ := hex
    exact .inr ⟨s, info, h, rfl, structNp_of_proj H h⟩
  · left; unfold structNp; rw [dif_neg hex]

/-- The applied rule extracted from a generic equation reads the major constructor of the
equation. -/
theorem generates_ctorName {schema : CaseSchema} {owner : Fin schema.signature.families.size}
    {rule : CaseSchema.AppliedRule} (hgen : schema.Generates key owner rule)
    (hm : rule.equation.lhs.stripLams = .app fn (VExpr.mkApps (.const c ls) args)) :
    rule.application.ctorName = c := by
  obtain ⟨_, _, _, hextract⟩ := hgen
  have hb := (CaseSchema.Generates.body_exact ⟨_, ‹_›, ‹_›, hextract⟩).1
  have ha := CaseSchema.Application.extract_sound (CaseSchema.AppliedRule.extract_spec hextract).2.2.1
  rw [← hb, stripLams_wrapLams', ← ha] at hm
  simp only [CaseSchema.Application.expr, VExpr.stripLams] at hm
  exact (mkApps_const_inj (VExpr.app.inj hm).2).1

theorem ctorOf_shape' (H : env.WF) (h : ctorOf env c = some k) : CtorShape env c k :=
  ctorOf_shape H h

theorem SchemaMajor.shape (H : env.WF) (h : SchemaMajor env c) : ∃ k, CtorShape env c k := by
  obtain ⟨key, schema, hreg, owner, rules, df, fn, ls, args, hgen, hdf, hm⟩ := h
  obtain ⟨kS, _, _, _, _, hs, _⟩ := schema_major H hreg hgen hdf hm
  exact ⟨kS, hs⟩

theorem SchemaMajor.rigid (H : env.WF) (h : SchemaMajor env c) : env.Rigid c := by
  obtain ⟨key, schema, hreg, owner, rules, df, fn, ls, args, hgen, hdf, hm⟩ := h
  obtain ⟨rule, hrule, rfl⟩ := CaseSchema.generates_of_genericEquation hgen hdf
  have := VEnv.WF.case_constructor_rigid H hreg hrule
  rw [generates_ctorName hrule hm] at this
  exact VEnv.nativeHeadRigid_iff.mp this

theorem IsCtor.shape (H : env.WF) (h : IsCtor env c) : ∃ k, CtorShape env c k := by
  rcases h with h | h
  · obtain ⟨k, hk⟩ := Option.ne_none_iff_exists'.mp h
    exact ⟨k, ctorOf_shape H hk⟩
  · exact h.shape H

theorem IsCtor.rigid (H : env.WF) (h : IsCtor env c) : env.Rigid c := by
  rcases h with h | h
  · obtain ⟨k, hk⟩ := Option.ne_none_iff_exists'.mp h
    exact (ctorOf_rigid H hk).1
  · exact h.rigid H

theorem sigCtor_spec (h : sigCtor env c = some ci) :
    IsCtor env c ∧ ∃ cv, env.constants c = some cv ∧ familyOfType cv.type = some ci.family ∧
      ci.nparams = structNp env c ∧ ci.nfields = cv.type.forallArity - structNp env c := by
  unfold sigCtor at h
  split at h
  · rename_i hc
    cases hcv : env.constants c with
    | none => simp [hcv] at h
    | some cv =>
      simp only [hcv, Option.bind_some, Option.map_eq_some_iff] at h
      obtain ⟨F, hF, rfl⟩ := h
      exact ⟨hc, cv, rfl, hF, rfl, rfl⟩
  · cases h

theorem sigCtor_family (h : sigCtor env c = some ci) : ctorFamily env c = some ci.family := by
  obtain ⟨_, cv, hcv, hF, _⟩ := sigCtor_spec h
  simp [ctorFamily, hcv, hF]

theorem sigCtor_of_shape (hc : IsCtor env c) (hk : CtorShape env c k) :
    sigCtor env c = some ⟨k.family, structNp env c, k.nparams + k.nfields - structNp env c⟩ := by
  obtain ⟨ci, doms, idx, hci, _, ht, hl⟩ := hk
  unfold sigCtor
  rw [if_pos hc, hci]
  simp only [ht, Option.bind_some, familyOfType_shape, forallArity_shape, hl, Option.map_some]

theorem sigCtor_isCtor (H : env.WF) (hc : IsCtor env c) :
    ∃ k, CtorShape env c k ∧
      sigCtor env c = some ⟨k.family, structNp env c, k.nparams + k.nfields - structNp env c⟩ := by
  obtain ⟨k, hk⟩ := hc.shape H
  exact ⟨k, hk, sigCtor_of_shape hc hk⟩

theorem sigCtor_ne_none (H : env.WF) (hc : IsCtor env c) : sigCtor env c ≠ none := by
  obtain ⟨k, _, h⟩ := sigCtor_isCtor H hc
  simp [h]

theorem sigCtor_isCtor_iff : sigCtor env c ≠ none → IsCtor env c := by
  intro h
  obtain ⟨ci, hci⟩ := Option.ne_none_iff_exists'.mp h
  exact (sigCtor_spec hci).1

/-! ## The constructor lists of families -/

theorem mem_dedupNames {l : List Name} : x ∈ dedupNames l ↔ x ∈ l := by
  induction l with
  | nil => simp [dedupNames]
  | cons y l ih =>
    unfold dedupNames
    split
    · rename_i hy
      rw [ih, List.mem_cons]
      constructor
      · exact .inr
      · rintro (rfl | h)
        · exact ih.1 hy
        · exact h
    · rw [List.mem_cons, ih, List.mem_cons]

theorem nodup_dedupNames (l : List Name) : (dedupNames l).Nodup := by
  induction l with
  | nil => simp [dedupNames]
  | cons y l ih =>
    unfold dedupNames
    split
    · exact ih
    · rename_i hy
      exact List.nodup_cons.mpr ⟨hy, ih⟩

theorem constNames_spec (H : env.WF) (h : env.constants c = some ci) : c ∈ constNames env := by
  have hex := WF.constList H
  unfold constNames
  rw [dif_pos hex]
  exact Classical.choose_spec hex _ _ h

theorem mem_sigFamCtors (H : env.WF) :
    c ∈ sigFamCtors env I ↔ ∃ ci, sigCtor env c = some ci ∧ ci.family = I := by
  unfold sigFamCtors
  rw [mem_dedupNames, List.mem_filter]
  constructor
  · rintro ⟨_, h⟩
    exact of_decide_eq_true h
  · intro h
    refine ⟨?_, decide_eq_true h⟩
    obtain ⟨ci, hci, _⟩ := h
    obtain ⟨_, cv, hcv, _⟩ := sigCtor_spec hci
    exact constNames_spec H hcv

theorem nodup_sigFamCtors : (sigFamCtors env I).Nodup := nodup_dedupNames _

end Lean4Lean.ShapeModel
