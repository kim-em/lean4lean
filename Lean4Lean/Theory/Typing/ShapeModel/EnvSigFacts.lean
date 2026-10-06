import Lean4Lean.Theory.Typing.ShapeModel.EnvSigCoherent

/-!
# Environment facts of the semantic signature of a well-formed environment

`SemSig.EnvFactsIn E env` for `envSig env` and every `E ≤ env`, except the field
`StructFacts.famTypeSem` (the approximations of a structure's declared type are those of the
telescope ending in its sort), which follows by soundness from the open derivation form proved
here (`structFamType`) and is taken as a hypothesis by `envSig_envFactsIn`.
-/

namespace Lean4Lean.ShapeModel
open InductiveSignature

variable {env : VEnv}

theorem vars_eq_range (np nf : Nat) :
    vars np nf = (List.range np).map (fun j => VExpr.bvar (np + nf - 1 - j)) := by
  apply List.ext_getElem
  · simp [vars]
  · intro i h1 h2
    simp only [vars, List.length_map, List.length_reverse, List.length_range] at h1
    simp only [vars, List.getElem_map, List.getElem_reverse, List.getElem_range,
      List.length_range, VExpr.bvar.injEq]
    omega

theorem wrapForalls_body_eq {doms doms' : List VExpr} {b b' : VExpr}
    (hl : doms.length = doms'.length) (h : VExpr.wrapForalls doms b = VExpr.wrapForalls doms' b') :
    b = b' := by
  induction doms generalizing doms' with
  | nil => cases doms' with
    | nil => exact h
    | cons => simp at hl
  | cons d ds ih => cases doms' with
    | nil => simp at hl
    | cons d' ds' => exact ih (by simpa using hl) (VExpr.forallE.inj h).2

theorem nodup_eq_singleton {l : List Name} (hn : l.Nodup) (hm : ∀ y, y ∈ l ↔ y = x) : l = [x] := by
  match l, hn with
  | [], _ => exact absurd ((hm x).2 rfl) (by simp)
  | [a], _ => rw [(hm a).1 (by simp)]
  | a :: b :: l, hn =>
    have ha := (hm a).1 (by simp)
    have hb := (hm b).1 (by simp)
    have := (List.nodup_cons.mp hn).1
    exact absurd (by simp [ha, hb]) this

/-! ## Structure facts -/

section
variable (H : env.WF) (hproj : env.projections s info)
include H hproj

theorem sig_structCtor : sigStructCtor env s = some info.ctorName := by
  have hex : ∃ info, env.projections s info := ⟨info, hproj⟩
  unfold sigStructCtor
  rw [dif_pos hex, H.ordered.projections_unique (Classical.choose_spec hex) hproj]

theorem sig_ctor_proj : sigCtor env info.ctorName = some ⟨s, info.nparams, info.numFields⟩ := by
  have hk := ctorOf_projection H hproj
  have hc : IsCtor env info.ctorName := .inl (by simp [hk])
  rw [sigCtor_of_shape hc (ctorOf_shape' H hk), structNp_of_proj H hproj]
  simp

theorem sig_famCtors_proj (hC : SchemaStructCompat env) :
    sigFamCtors env s = [info.ctorName] := by
  apply nodup_eq_singleton nodup_sigFamCtors
  intro c
  rw [mem_sigFamCtors H]
  constructor
  · rintro ⟨ci, hci, rfl⟩
    exact ctor_of_struct_family H hC hproj (sigCtor_spec hci).1 (sigCtor_family hci)
  · rintro rfl
    exact ⟨_, sig_ctor_proj H hproj, rfl⟩

omit H in
theorem sig_isStruct_proj (h0 : info.nindices = 0) : sigIsStruct env info.ctorName = true :=
  @decide_eq_true _ (Classical.propDecidable _) ⟨s, info, hproj, rfl, h0⟩

theorem sig_ctorConst : env.constants info.ctorName = some ⟨info.uvars, info.ctorType⟩ :=
  H.ordered.projectionConstructor hproj

theorem sig_ctorType : ∃ (Ds idx : List VExpr), Ds.length = info.nparams + info.numFields ∧
    idx.length = info.nindices ∧
    info.ctorType = Ds.foldr .forallE (VExpr.mkApps (.const s (VLevel.params info.uvars))
      ((List.range info.nparams).map (fun j => .bvar (info.nparams + info.numFields - 1 - j)) ++
        idx)) := by
  obtain ⟨ci, doms, indices, hci, huv, ht, hl⟩ := ctorOf_shape' H (ctorOf_projection H hproj)
  rw [sig_ctorConst H hproj] at hci
  cases hci
  simp only at huv ht hl
  obtain ⟨decl, type, ctor, htype, _, hname, _, _, hnp, hind, _, _, hctype, _, _, _, hraw,
    hnodup⟩ := H.ordered.projectionShape hproj
  obtain ⟨doms', result, heq, _, happ, _, harity⟩ := hraw.forallArity
  have hlen : doms'.length = doms.length := by
    rw [← harity, hctype, ht, forallArity_shape]
  have hres := wrapForalls_body_eq hlen (heq.symm.trans (hctype.trans ht))
  obtain ⟨type', htype', htarget, levels, hfn, _, hargs, _⟩ := happ
  rcases htarget with h | h
  · cases h
  · have := VInductDecl.type_eq_of_mem_name hnodup htype' htype (Option.some.inj h).symm
    subst this
    change (VExpr.getAppFnArgs result).2.length = _ at hargs
    rw [hres, VExpr.getAppFnArgs_mkApps_const] at hargs
    simp only [List.length_append, vars_succ_length] at hargs
    refine ⟨doms, indices, hl, by omega, ?_⟩
    rw [ht, ← vars_eq_range]
    rfl

theorem sig_famNotCtor : sigCtor env s = none := by
  have hfam := famOf_projection H hproj
  unfold sigCtor
  rw [if_neg]
  rintro (h | ⟨_, h⟩)
  · exact h ((envTables_inv H).views.fam_ctor (by simp [famOf] at hfam; simp [hfam]))
  · simp [hfam] at h

theorem sig_famNoRule : ∀ r, EnvRule env r → r.head ≠ .const s := by
  have hfam := famOf_projection H hproj
  intro r hr
  exact EnvRule.head_not_rigid H
    ((envTables_inv H).views.rigid (.inl (by simp [famOf] at hfam; simp [hfam]))) hr

theorem sig_famLevel : sigFamLevel env s = some info.resultLevel := by
  simp [sigFamLevel, famOf_projection H hproj]

/-- The declared type of a registered structure is definitionally a telescope over its
parameters and indices whose body is definitionally its sort (open form: two derivations). -/
theorem structFamType : ∃ ci, env.constants s = some ci ∧ ci.uvars = info.uvars ∧
    ∃ (Ds : List VExpr) (body A : VExpr), Ds.length = info.nparams + info.nindices ∧
      env.IsDefEq info.uvars [] ci.type (Ds.foldr .forallE body) A ∧
      env.IsDefEq info.uvars Ds.reverse body (.sort info.resultLevel)
        (.sort info.resultLevel.succ) := by
  obtain ⟨ci, hci, huv, doms, result, type, h1, h2, h3⟩ := famOf_shape H (famOf_projection H hproj)
  exact ⟨ci, hci, huv, doms, result, type, h2, h1, h3⟩

end

/-! ## Eliminator types -/

theorem sig_elimType (H : env.WF) (hreg : env.eliminators b schema)
    (hT : schema.genericType owner = some T) : sigElimType env b owner.val = some T := by
  have hex : ∃ (schema : CaseSchema) (T : VExpr), env.eliminators b schema ∧
      ∃ ho : owner.val < schema.signature.families.size, schema.genericType ⟨owner.val, ho⟩ = some T :=
    ⟨schema, T, hreg, owner.isLt, hT⟩
  have key : ∀ (schema' : CaseSchema) (T' : VExpr), env.eliminators b schema' →
      ∀ ho : owner.val < schema'.signature.families.size,
        schema'.genericType ⟨owner.val, ho⟩ = some T' → T' = T := by
    intro schema' T' hreg' ho hT'
    have := H.eliminators_unique hreg hreg'
    subst this
    rw [hT] at hT'
    exact (Option.some.inj hT').symm
  unfold sigElimType
  rw [dif_pos hex]
  obtain ⟨hreg', ho, hT'⟩ := Classical.choose_spec (Classical.choose_spec hex)
  exact congrArg some (key _ _ hreg' ho hT')

/-! ## Assembly -/

/-- The semantic field `famTypeSem` of `StructFacts` for the signature of `env`. -/
def FamTypeSem (env : VEnv) (s : Name) (info : VProjectionInfo) : Prop :=
  letI := envSig env
  ∃ ci, ∃ Ds : List VExpr, env.constants s = some ci ∧ ci.uvars = info.uvars ∧
    Ds.length = info.nparams + info.nindices ∧
    ∀ ls, ls.length = info.uvars → ∀ m, Interp env .nil m (ci.type.instL ls) ↔
      Interp env .nil m (VExpr.instL ls (Ds.foldr VExpr.forallE (VExpr.sort info.resultLevel)))

theorem envSig_structFacts (H : env.WF) (hC : SchemaStructCompat env)
    (hproj : env.projections s info) (hsem : FamTypeSem env s info) :
    letI := envSig env; SemSig.StructFacts env s info := by
  letI := envSig env
  exact ⟨sig_structCtor H hproj, sig_ctor_proj H hproj, sig_famCtors_proj H hproj hC,
    sig_isStruct_proj hproj, sig_ctorConst H hproj, sig_ctorType H hproj, sig_famNotCtor H hproj,
    sig_famNoRule H hproj, sig_famLevel H hproj, hsem⟩

/-- The environment facts of the signature of `env`, for derivations in any `E ≤ env`; the
semantic structure-type field is the hypothesis `hsem` (derived by M4c from `structFamType`). -/
theorem envSig_envFactsIn (H : env.WF) (hC : SchemaStructCompat env) {E : VEnv} (hle : E ≤ env)
    (hsem : ∀ {s info}, E.projections s info → FamTypeSem env s info) :
    letI := envSig env; SemSig.EnvFactsIn E env := by
  letI := envSig env
  exact ⟨fun h => H.ordered.closedC h, fun hreg hT _ => sig_elimType H (hle.eliminators hreg) hT,
    fun hp => envSig_structFacts H hC (hle.projections hp) (hsem hp)⟩

end Lean4Lean.ShapeModel
