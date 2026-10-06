import Lean4Lean.Theory.Typing.ShapeModel.EnvTablesSteps

/-!
# Preservation of the table invariant by eliminator and projection registration
-/

namespace Lean4Lean.ShapeModel
open VEnv InductiveSignature

variable {env env' : VEnv} {T : Tables}

/-! ## Constant occurrences with their universe arity -/

/-- Every constant occurrence is declared, at its universe arity. -/
def ConstsWF (env : VEnv) : VExpr → Prop
  | .const name levels => ∃ ci, env.constants name = some ci ∧ levels.length = ci.uvars
  | .app f a | .lam f a | .forallE f a => ConstsWF env f ∧ ConstsWF env a
  | .proj _ _ e => ConstsWF env e
  | _ => True

theorem IsDefEqStrong.constsWF {U Γ left right type}
    (h : IsDefEqStrong env U Γ left right type) : ConstsWF env left ∧ ConstsWF env right := by
  induction h with
  | bvar | sortDF | elimDF => exact ⟨trivial, trivial⟩
  | constDF lookup _ _ hlen hrel => exact ⟨⟨_, lookup, hlen⟩, ⟨_, lookup, (Lean4Lean.List.Forall₂.length_eq hrel) ▸ hlen⟩⟩
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ⟨ih₁.1, ih₂.2⟩
  | appDF _ _ _ _ _ _ _ _ _ fn arg _ =>
    exact ⟨⟨fn.1, arg.1⟩, ⟨fn.2, arg.2⟩⟩
  | projDF _ _ _ _ _ _ _ _ _ _ _ _ _ first second => exact ⟨first.2, second.2⟩
  | lamDF _ _ _ _ _ _ _ domain _ _ body _ =>
    exact ⟨⟨domain.1, body.1⟩, ⟨domain.2, body.2⟩⟩
  | forallEDF _ _ _ _ _ domain body _ =>
    exact ⟨⟨domain.1, body.1⟩, ⟨domain.2, body.2⟩⟩
  | defeqDF _ _ _ _ ih => exact ih
  | beta _ _ _ _ _ _ _ _ domain _ body arg _ result =>
    exact ⟨⟨⟨domain.1, body.1⟩, arg.1⟩, result.1⟩
  | eta _ _ _ _ _ _ _ _ domain _ _ fn lifted _ =>
    exact ⟨⟨domain.1, lifted.1, trivial⟩, fn.1⟩
  | proofIrrel _ _ _ _ left right => exact ⟨left.1, right.1⟩
  | extra _ _ _ _ _ _ _ _ _ _ _ _ left right => exact ⟨left.1, right.1⟩
  | elimIota _ _ _ _ _ _ _ _ _ _ left right => exact ⟨left.1, right.1⟩
  | projIota _ _ _ _ left right => exact ⟨left.1, right.1⟩
  | structEta _ _ _ _ _ right left => exact ⟨left.1, right.1⟩
  | unitLike _ _ _ _ _ _ left right => exact ⟨left.1, right.1⟩

theorem ConstsWF.mkApps_head {f : VExpr} (h : ConstsWF env (VExpr.mkApps f args)) :
    ConstsWF env f := by
  induction args generalizing f with
  | nil => exact h
  | cons a args ih => exact (ih (f := .app f a) h).1

theorem ConstsWF.wrapForalls_body (h : ConstsWF env (VExpr.wrapForalls doms body)) :
    ConstsWF env body := by
  induction doms with
  | nil => exact h
  | cons _ _ ih => exact ih h.2

/-- A constructor of an ordered environment uses its family at the family's universe arity. -/
theorem family_uvars_of_ctor (henv : env.Ordered) (hc : env.constants c = some ci)
    (hshape : ci.type = VExpr.wrapForalls doms (VExpr.mkApps (.const F ls) args))
    (hF : env.constants F = some ciF) : ls.length = ciF.uvars := by
  obtain ⟨u, ht⟩ := henv.constWF hc
  have h := (IsDefEqStrong.constsWF (ht.strong henv (Γ := []) ⟨⟩)).1
  rw [hshape] at h
  obtain ⟨ci', hci', hlen⟩ := h.wrapForalls_body.mkApps_head
  rw [hF] at hci'
  cases hci'
  exact hlen

/-! ## Constructor names of a certified schema -/

theorem forall₂_prefix {R : α → β → Prop} {as : List α} {bs cs : List β}
    (h : List.Forall₂ R as (bs ++ cs)) : List.Forall₂ R (as.take bs.length) bs := by
  induction bs generalizing as with
  | nil => simp
  | cons b bs ih =>
    cases h with
    | cons hab hrest => exact .cons hab (ih hrest)

theorem Certified.mem_schemaCtorNames {schema : CaseSchema}
    (H : schema.Certified base source block) :
    n ∈ schemaCtorNames schema ↔ ∃ c ∈ source.constructorConstants, c.name = n := by
  obtain ⟨expanded, g, aux, hdata, _, _, hnames⟩ := H
  obtain ⟨envTypes, direct, _, _, _, hfamilies⟩ := hdata.correspondence
  have hpre := forall₂_prefix hfamilies
  have hlen : schema.originalFamilies.length = source.types.length := by rw [hnames]; simp
  simp only [schemaCtorNames, hlen, List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨nt, hnt, nc, hnc, rfl⟩
    obtain ⟨t, ht, hrel⟩ := Lean4Lean.List.Forall₂.forall_exists_l hpre nt hnt
    obtain ⟨c, hc, hcrel⟩ := Lean4Lean.List.Forall₂.forall_exists_l hrel.constructors nc hnc
    exact ⟨c, List.mem_flatMap.mpr ⟨t, ht, hc⟩, hcrel.1.symm⟩
  · rintro ⟨c, hc, rfl⟩
    obtain ⟨t, ht, hc⟩ := List.mem_flatMap.mp hc
    obtain ⟨nt, hnt, hrel⟩ := Lean4Lean.List.Forall₂.forall_exists_r hpre t ht
    obtain ⟨nc, hnc, hcrel⟩ := Lean4Lean.List.Forall₂.forall_exists_r hrel.constructors c hc
    exact ⟨nt, hnt, nc, hnc, hcrel.1⟩

/-! ## Witnesses are present below -/

theorem Witness.present {base : VEnv} (hbase : base.WF) (hle : base ≤ env)
    (hdf : env.defeqs = base.defeqs) (hproj : env.projections = base.projections)
    (helim : env.eliminators = base.eliminators) (hw : Witness env X) :
    ∃ ci, base.constants X = some ci := by
  have hord := hbase.ordered
  rcases hw with ⟨df, h1, h2⟩ | ⟨df, Y, ci, h1, h2, h3, h4⟩ | ⟨s, info, h1, h2⟩ |
    ⟨key, schema, h1, h2⟩
  · rw [hdf] at h1
    exact defeq_lhs_present hord h1 h2
  · rw [hdf] at h1
    obtain ⟨ciY, hY⟩ := defeq_lhs_present hord h1 h2
    have := hle.constants hY
    rw [h3] at this
    cases this
    exact const_type_present hord hY h4
  · rw [hproj] at h1
    rcases h2 with rfl | rfl
    · exact hord.projectionConstant h1
    · exact ⟨_, hord.projectionConstructor h1⟩
  · rw [helim] at h1
    rcases h2 with h2 | h2
    · exact hbase.eliminator_family_present h1 h2
    · obtain ⟨b, src, blk, _, _, hcert, _, hconsts⟩ := hbase.eliminator_origin h1
      obtain ⟨c, hc, rfl⟩ := (Certified.mem_schemaCtorNames hcert).mp h2
      refine ⟨_, hconsts c (List.mem_append_right _ ?_)⟩
      obtain ⟨expanded, g, aux, hdata, _⟩ := hcert
      rw [hdata.ctors]; exact hc

/-! ## Eliminator registration -/

def selAll (_ : VInductiveType) : Bool := true

/-- Record a schema's views if none of its names is recorded yet. -/
noncomputable def Tables.addSchema (T : Tables) (source : VInductDecl) : Tables := by
  classical
  exact if ∀ t ∈ source.types, T.fam t.name = none ∧ T.ctor t.name = none ∧
      ∀ c ∈ t.ctors, T.fam c.name = none ∧ T.ctor c.name = none then
    T.addViews (viewFams source selAll) (viewCtors source selAll)
  else T

theorem Tables.Inv.eliminator {base : VEnv} {source : VInductDecl} {block : VInductBlock}
    {schema : CaseSchema} (H : T.Inv env) (hbase : base.WF) (hle : base ≤ env)
    (hcert : schema.Certified base source block)
    (hconsts : ∀ value ∈ block.types ++ block.ctors,
      env.constants value.name = some value.toVConstant)
    (hdf : env.defeqs = base.defeqs) :
    T.Extends (T.addSchema source) ∧ (T.addSchema source).Inv (env.addEliminator key schema) := by
  classical
  have H' := H.transport (env' := env.addEliminator key schema) VEnv.addEliminator_le rfl rfl
  unfold Tables.addSchema
  split
  · rename_i hfree
    refine ⟨T.extends_addViews _ _, H'.addViews ?_⟩
    obtain ⟨expanded, g, aux, hdata, _, _, hnames⟩ := hcert
    obtain ⟨_, hnd, hTypeUv, hCtorUv, envTypes, envCtors, htypes, hctors, _⟩ := hdata.sourceWF
    obtain ⟨params, _, _, hTypeShape, _, hraw⟩ := hdata.sourceParameters
    have hle' : base ≤ env.addEliminator key schema := hle.trans VEnv.addEliminator_le
    have htypeConst : ∀ t ∈ source.types,
        (env.addEliminator key schema).constants t.name = some t.toVConstant := by
      intro t ht
      exact hconsts t.toVConstVal (List.mem_append_left _ (by
        rw [hdata.types]; exact List.mem_map.mpr ⟨t, ht, rfl⟩))
    have hctorConst : ∀ t ∈ source.types, ∀ c ∈ t.ctors,
        (env.addEliminator key schema).constants c.name = some c.toVConstant := by
      intro t ht c hc
      exact hconsts c (List.mem_append_right _ (by
        rw [hdata.ctors]; exact List.mem_flatMap.mpr ⟨t, ht, hc⟩))
    have hfreshType : ∀ t ∈ source.types, base.constants t.name = none := fun t ht =>
      VEnv.addConstVals_names_fresh htypes t.toVConstVal (List.mem_map.mpr ⟨t, ht, rfl⟩)
    have hfreshCtor : ∀ t ∈ source.types, ∀ c ∈ t.ctors, base.constants c.name = none :=
      fun t ht c hc => fresh_of_le (VEnv.addConstVals_le htypes)
        (VEnv.addConstVals_names_fresh hctors c (List.mem_flatMap.mpr ⟨t, ht, hc⟩))
    have hrigid : ∀ n, base.constants n = none → (env.addEliminator key schema).Rigid n := by
      intro n hn
      have := hbase.ordered.rigid_of_absent hn
      simpa only [VEnv.Rigid, VEnv.addEliminator_defeqs, hdf] using this
    have hreg : (env.addEliminator key schema).eliminators key schema := VEnv.addEliminator_self
    apply viewsOK_decl hnd
    · intro t ht _; exact hfree t ht
    · intro t ht _
      exact famShape_of_typeShape ((hTypeShape t ht).mono hle') (hTypeUv t ht) (htypeConst t ht)
    · intro t ht _ c hc
      exact ⟨hctorConst t ht c hc, hraw t ht c hc, hCtorUv c (List.mem_flatMap.mpr ⟨t, ht, hc⟩)⟩
    · intro t ht _
      exact ⟨hrigid _ (hfreshType t ht), fun c hc => hrigid _ (hfreshCtor t ht c hc)⟩
    · intro t ht _
      refine ⟨.inr <| .inr <| .inr ⟨key, schema, hreg, .inl ?_⟩,
        fun c hc => .inr <| .inr <| .inr ⟨key, schema, hreg, .inr ?_⟩⟩
      · rw [hnames]; exact List.mem_map.mpr ⟨t, ht, rfl⟩
      · exact (Certified.mem_schemaCtorNames ⟨expanded, g, aux, hdata, ‹_›, ‹_›, hnames⟩).mpr
          ⟨c, List.mem_flatMap.mpr ⟨t, ht, hc⟩, rfl⟩
  · exact ⟨.rfl, H'⟩

/-! ## Structure registration -/

def selStruct (t : VInductiveType) : Bool := t.ctors.length == 1

theorem Tables.Inv.registerProjections {base envTypes envCtors : VEnv} {decl : VInductDecl}
    {block : VInductBlock} (H : T.Inv envCtors) (hbase : base.WF)
    (henv' : (envCtors.addProjections block.projections).WF)
    (hsource : decl.sourceNames.Nodup)
    (hconstructorUvars : ∀ ctor ∈ decl.constructorConstants, ctor.uvars = decl.uvars)
    (hparams : decl.SourceParameterWF base)
    (hshape : ∀ type ∈ decl.types, ∀ ctor ∈ type.ctors, decl.RawCtorShape type ctor)
    (htypesSource : block.types = decl.typeConstants)
    (hctorsSource : block.ctors = decl.constructorConstants)
    (hprojections : block.projections = decl.projectionEntries)
    (htypes : base.addConstVals block.types = some envTypes)
    (hctors : envTypes.addConstVals block.ctors = some envCtors) :
    let T' := T.addViews (viewFams decl selStruct) (viewCtors decl selStruct)
    T.Extends T' ∧ T'.Inv (envCtors.addProjections block.projections) := by
  intro T'
  let env' := envCtors.addProjections block.projections
  have hle1 : base ≤ envCtors := (VEnv.addConstVals_le htypes).trans (VEnv.addConstVals_le hctors)
  have hle2 : envCtors ≤ env' := VEnv.addProjections_le
  have hdfC : envCtors.defeqs = base.defeqs :=
    (VEnv.addConstVals_defeqs hctors).trans (VEnv.addConstVals_defeqs htypes)
  have hprojC : envCtors.projections = base.projections :=
    (VEnv.addConstVals_projections hctors).trans (VEnv.addConstVals_projections htypes)
  have helimC : envCtors.eliminators = base.eliminators :=
    (VEnv.addConstVals_eliminators hctors).trans (VEnv.addConstVals_eliminators htypes)
  have hdf' : env'.defeqs = base.defeqs := (VEnv.addProjections_defeqs _ _).trans hdfC
  have htypeMem : ∀ t ∈ decl.types, t.toVConstVal ∈ block.types := fun t ht => by
    rw [htypesSource]; exact List.mem_map.mpr ⟨t, ht, rfl⟩
  have hctorMem : ∀ t ∈ decl.types, ∀ c ∈ t.ctors, c ∈ block.ctors := fun t ht c hc => by
    rw [hctorsSource]; exact List.mem_flatMap.mpr ⟨t, ht, hc⟩
  have hfreshType : ∀ t ∈ decl.types, base.constants t.name = none := fun t ht =>
    VEnv.addConstVals_names_fresh htypes _ (htypeMem t ht)
  have hfreshCtor : ∀ t ∈ decl.types, ∀ c ∈ t.ctors, base.constants c.name = none :=
    fun t ht c hc => fresh_of_le (VEnv.addConstVals_le htypes)
      (VEnv.addConstVals_names_fresh hctors c (hctorMem t ht c hc))
  have htypeConst : ∀ t ∈ decl.types, env'.constants t.name = some t.toVConstant := by
    intro t ht
    rw [VEnv.addProjections_constants]
    exact (VEnv.addConstVals_le hctors).constants (VEnv.addConstVals_get htypes (htypeMem t ht))
  have hctorConst : ∀ t ∈ decl.types, ∀ c ∈ t.ctors, env'.constants c.name = some c.toVConstant := by
    intro t ht c hc
    rw [VEnv.addProjections_constants]
    exact VEnv.addConstVals_get hctors (hctorMem t ht c hc)
  have hctorUv : ∀ t ∈ decl.types, ∀ c ∈ t.ctors, c.uvars = decl.uvars := fun t ht c hc =>
    hconstructorUvars c (List.mem_flatMap.mpr ⟨t, ht, hc⟩)
  have hfreeT : ∀ n, base.constants n = none → T.fam n = none ∧ T.ctor n = none := by
    intro n hn
    have hw : T.fam n ≠ none ∨ T.ctor n ≠ none → False := fun hne' => by
      obtain ⟨ci, hci⟩ := (H.views.witness hne').present hbase hle1 hdfC hprojC helimC
      rw [hn] at hci
      cases hci
    refine ⟨?_, ?_⟩
    · cases h : T.fam n with
      | none => rfl
      | some _ => exact (hw (.inl (by simp [h]))).elim
    · cases h : T.ctor n with
      | none => rfl
      | some _ => exact (hw (.inr (by simp [h]))).elim
  have hrigid : ∀ n, base.constants n = none → env'.Rigid n := by
    intro n hn
    have := hbase.ordered.rigid_of_absent hn
    simpa only [VEnv.Rigid, hdf'] using this
  have hext : T.Extends T' := T.extends_addViews _ _
  obtain ⟨params, _, _, hTypeShape, _, _⟩ := hparams
  have hstructEntry : ∀ t ∈ decl.types, ∀ c, t.ctors = [c] →
      ∃ entry ∈ block.projections, entry.typeName = t.name ∧ entry.info.ctorName = c.name := by
    intro t ht c hc
    rw [hprojections]
    refine ⟨_, List.mem_filterMap.mpr ⟨t, ht, by rw [hc]⟩, rfl, rfl⟩
  have hselStruct : ∀ {t : VInductiveType}, selStruct t = true → ∃ c, t.ctors = [c] := by
    intro t ht
    simp only [selStruct, beq_iff_eq] at ht
    match h : t.ctors, ht with
    | [c], _ => exact ⟨c, rfl⟩
  have hok : ViewsOK env' T.fam T.ctor (viewFams decl selStruct) (viewCtors decl selStruct) := by
    apply viewsOK_decl hsource
    · intro t ht _
      exact ⟨(hfreeT _ (hfreshType t ht)).1, (hfreeT _ (hfreshType t ht)).2, fun c hc =>
        hfreeT _ (hfreshCtor t ht c hc)⟩
    · intro t ht hs
      obtain ⟨c, hc⟩ := hselStruct hs
      have hcmem : c ∈ t.ctors := by simp [hc]
      have hcs := ctorShape_of_raw (env := env') (hshape t ht c hcmem) (hctorUv t ht c hcmem)
        (hctorConst t ht c hcmem)
      obtain ⟨ci, doms, indices, hci, _, htype, _⟩ := hcs
      have huv := family_uvars_of_ctor henv'.ordered hci htype (htypeConst t ht)
      simp only [ctorView, VLevel.params_length] at huv
      exact famShape_of_typeShape ((hTypeShape t ht).mono (hle1.trans hle2)) huv.symm
        (htypeConst t ht)
    · intro t ht _ c hc
      exact ⟨hctorConst t ht c hc, hshape t ht c hc, hctorUv t ht c hc⟩
    · intro t ht _
      exact ⟨hrigid _ (hfreshType t ht), fun c hc => hrigid _ (hfreshCtor t ht c hc)⟩
    · intro t ht hs
      obtain ⟨c, hc⟩ := hselStruct hs
      obtain ⟨entry, hentry, hn, hcn⟩ := hstructEntry t ht c hc
      have hproj : env'.projections entry.typeName entry.info :=
        VEnv.addProjections_iff.mpr (.inl ⟨entry, hentry, rfl, rfl⟩)
      refine ⟨.inr <| .inr <| .inl ⟨_, _, hproj, .inl hn.symm⟩, fun c' hc' => ?_⟩
      rw [hc, List.mem_singleton] at hc'
      subst hc'
      exact .inr <| .inr <| .inl ⟨_, _, hproj, .inr hcn.symm⟩
  refine ⟨hext, ⟨fun {n v} hv => ?_, fun {n data} hd => ?_, fun hq => ?_, H.defs_natives,
    (H.views.transport hle2 (VEnv.addProjections_defeqs _ _)).addViews hok,
    fun {df} hdf => ?_, fun {s info} hp => ?_⟩⟩
  · obtain ⟨h1, h2, h3⟩ := H.defs hv
    exact ⟨h1, hle2.constants h2, hle2.defeqs h3⟩
  · obtain ⟨h1, h2⟩ := H.natives hd
    exact ⟨h1, h2.mono hle2 hext⟩
  · obtain ⟨hQI, h2, h3, h4⟩ := H.quot hq
    exact ⟨hQI.mono hle2, addView_of_old h2, addView_of_old h3, h4⟩
  · rw [VEnv.addProjections_defeqs] at hdf
    rcases H.equations hdf with h | h | h
    · exact .inl h
    · exact .inr (.inl h)
    · exact .inr (.inr h)
  · rcases VEnv.addProjections_iff.mp hp with ⟨entry, hentry, rfl, rfl⟩ | hold
    · rw [hprojections] at hentry
      obtain ⟨t, ht, c, hctors1, rfl⟩ := VInductDecl.projectionEntries_origin hentry
      have hs : selStruct t = true := by simp [selStruct, hctors1]
      have hc : c ∈ t.ctors := by simp [hctors1]
      refine ⟨addView_some.mpr (.inr ⟨(hfreeT _ (hfreshType t ht)).1, ?_⟩),
        addView_some.mpr (.inr ⟨(hfreeT _ (hfreshCtor t ht c hc)).2, ?_⟩)⟩
      · rw [viewFams_mem hsource ht hs]
        simp [famView, projFam, hctors1]
      · rw [viewCtors_mem ht hs hc
          (ctorView_unique (fun t ht _ c hc => ⟨hctorConst t ht c hc, hshape t ht c hc,
            hctorUv t ht c hc⟩) t ht hs c hc)]
        rfl
    · obtain ⟨h1, h2⟩ := H.projections hold
      exact ⟨addView_of_old h1, addView_of_old h2⟩

end Lean4Lean.ShapeModel

namespace Lean4Lean.ShapeModel
open VEnv InductiveSignature

/-! ## Every history has tables -/

def Tables.empty : Tables := ⟨fun _ => none, fun _ => none, false, fun _ => none, fun _ => none⟩

theorem Tables.empty_inv : Tables.empty.Inv VEnv.empty where
  defs h := by cases h
  natives h := by cases h
  quot h := by cases h
  defs_natives h := rfl
  views := {
    fam := fun h => by cases h
    ctor := fun h => by cases h
    fam_ctor := fun _ => rfl
    rigid := fun h => (h.elim (· rfl) (· rfl)).elim
    witness := fun h => (h.elim (· rfl) (· rfl)).elim }
  equations h := by cases h
  projections h := by cases h

theorem VEnv.WF'.tables {ds : List VDecl} {env : VEnv} (H : env.WF' ds) :
    ∃ T : Tables, T.Inv env ∧ (VDecl.quot ∈ ds → T.quot = true) := by
  induction H with
  | empty => exact ⟨_, Tables.empty_inv, fun h => by cases h⟩
  | @decl d env' ds env hdecl hprev ih =>
    obtain ⟨T, hT, hq⟩ := ih
    have henv : env.WF := ⟨ds, hprev⟩
    have henv' : env'.WF := ⟨d :: ds, .decl hdecl hprev⟩
    have hq' : ∀ {T' : Tables}, (T.quot = true → T'.quot = true) → d ≠ VDecl.quot →
        VDecl.quot ∈ d :: ds → T'.quot = true := by
      intro T' hext hne hmem
      rcases List.mem_cons.mp hmem with h | h
      · exact absurd h.symm hne
      · exact hext (hq h)
    cases hdecl with
    | «axiom» _ hadd =>
      exact ⟨T, hT.transport (VEnv.addConst_le hadd) (VEnv.addConst_defeqs hadd)
        (VEnv.addConst_projections hadd), hq' id (by simp)⟩
    | «opaque» _ hadd =>
      exact ⟨T, hT.transport (VEnv.addConst_le hadd) (VEnv.addConst_defeqs hadd)
        (VEnv.addConst_projections hadd), hq' id (by simp)⟩
    | «example» => exact ⟨T, hT, hq' id (by simp)⟩
    | @«def» _ _ ci _ hadd =>
      exact ⟨_, hT.addDefinitions (cis := [ci]) (by simpa [VEnv.addConsts] using hadd),
        hq' id (by simp)⟩
    | mutualDef _ hadd _ =>
      exact ⟨_, hT.addDefinitions hadd, hq' id (by simp)⟩
    | quot _ hadd => exact ⟨_, hT.addQuot henv henv' hadd, fun _ => rfl⟩
    | induct _ hadd =>
      cases hadd with
      | intro _ hcompile hblock hinstall =>
        obtain ⟨T', hext, hT'⟩ := hT.install henv hcompile hblock hinstall
        exact ⟨T', hT', hq' hext.quot (by simp)⟩
  | inductEliminators hbase _ hle hcert _ hconsts _ _ ih =>
    obtain ⟨T, hT, hq⟩ := ih
    obtain ⟨hext, hT'⟩ := hT.eliminator ⟨_, hbase⟩ hle hcert hconsts.1 hconsts.2.1
    exact ⟨_, hT', fun h => hext.quot (hq h)⟩
  | inductProjections hbase hctorsWF hsource _ hconstructorUvars _ hparams hshape htypesSource
      hctorsSource hprojections htypes hctors _ ih =>
    obtain ⟨T, hT, hq⟩ := ih
    have henv' := VEnv.WF.inductProjections ⟨_, hbase⟩ ⟨_, hctorsWF⟩ hsource
      ‹_› hconstructorUvars ‹_› hparams hshape htypesSource hctorsSource hprojections htypes hctors
    obtain ⟨hext, hT'⟩ := hT.registerProjections ⟨_, hbase⟩ henv' hsource hconstructorUvars
      hparams hshape htypesSource hctorsSource hprojections htypes hctors
    exact ⟨_, hT', fun h => hext.quot (hq h)⟩

theorem VEnv.WF.tables {env : VEnv} (H : env.WF) : ∃ T : Tables, T.Inv env :=
  (VEnv.WF'.tables H.choose_spec).imp fun _ h => h.1

end Lean4Lean.ShapeModel
