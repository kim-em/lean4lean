import Lean4Lean.Theory.Typing.EnvLemmas

/-! # The origin of a projection entry in the declaration history

Every projection entry of an environment in the history `VEnv.WF'` is the entry of a
single-constructor family of an inductive declaration `decl`. The entry is installed, either
by the `induct` declaration or by an `inductProjections` stage, on top of an earlier
environment `base` of the history. The constructor's type is well formed in
`envTypes = base.addConstVals decl.typeConstants`. That environment has the rules,
projections and eliminators of `base`, so soundness of `base`'s derivations applies to it.
-/

namespace Lean4Lean

theorem VEnv.addConsts_projections {env env' : VEnv} :
    ∀ {cis}, env.addConsts cis = some env' → env'.projections = env.projections
  | [], h => by cases h; rfl
  | _ :: _, h => by
    simp only [VEnv.addConsts, List.foldlM_cons, Option.bind_eq_bind,
      Option.bind_eq_some_iff] at h
    obtain ⟨middle, hfirst, hrest⟩ := h
    exact (VEnv.addConsts_projections hrest).trans (VEnv.addConst_projections hfirst)

@[simp] theorem VEnv.addDefEqs_projections (env : VEnv) (cis : List VDefVal) :
    (env.addDefEqs cis).projections = env.projections := by
  induction cis generalizing env with
  | nil => rfl
  | cons ci cis ih => exact ih (env := env.addDefEq ci.toDefEq)

theorem VEnv.addQuot_projections {env env' : VEnv}
    (H : env.addQuot = some env') : env'.projections = env.projections := by
  simp only [VEnv.addQuot, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.pure_def, Option.some.injEq] at H
  obtain ⟨a, ha, b, hb, c, hc, d, hd, rfl⟩ := H
  exact (VEnv.addConst_projections hd).trans <|
    (VEnv.addConst_projections hc).trans <|
      (VEnv.addConst_projections hb).trans (VEnv.addConst_projections ha)

private theorem defs_le (env : VEnv) (cis : List VDefVal) :
    env ≤ env.addDefEqs cis := by
  induction cis generalizing env with
  | nil => exact .rfl
  | cons ci cis ih => exact VEnv.addDefEq_le.trans (ih _)

private theorem decl_le (H : VDecl.WF env decl env') : env ≤ env' := by
  cases H with
  | «axiom» _ h | «opaque» _ h => exact VEnv.addConst_le h
  | «def» _ h => exact (VEnv.addConst_le h).trans VEnv.addDefEq_le
  | «example» => exact .rfl
  | mutualDef _ h _ => exact (VEnv.addConsts_le h).trans (defs_le ..)
  | quot _ h =>
    simp only [VEnv.addQuot, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.some.injEq] at h
    obtain ⟨a, ha, b, hb, c, hc, d, hd, rfl⟩ := h
    exact (VEnv.addConst_le ha).trans <| (VEnv.addConst_le hb).trans <|
      (VEnv.addConst_le hc).trans <| (VEnv.addConst_le hd).trans VEnv.addDefEq_le
  | induct _ h =>
    cases h with
    | intro _ _ _ h =>
      simp only [VInductBlock.install, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at h
      obtain ⟨types, ht, ctors, hc, recs, hr, rfl⟩ := h
      exact (VEnv.addConstVals_le ht).trans <| (VEnv.addConstVals_le hc).trans <|
        VEnv.addProjections_le.trans <| (VEnv.addConstVals_le hr).trans VEnv.addDefEqRules_le

private theorem typeConstants_wf {decl : VInductDecl} {base : VEnv}
    (h : ∀ type ∈ decl.types, type.toVConstant.WF base) :
    ∀ ci ∈ decl.typeConstants, ci.toVConstant.WF base := by
  intro ci hci
  obtain ⟨type, htype, rfl⟩ := List.mem_map.1 hci
  exact h type htype

/-- The facts recorded at the installation of a projection entry. -/
def VEnv.ProjOrigin (env : VEnv) (S : Name) (info : VProjectionInfo) : Prop :=
  ∃ (base envTypes : VEnv) (dsb : List VDecl) (decl : VInductDecl) (type : VInductiveType)
    (ctor : VConstVal),
    base.WF' dsb ∧ base.addConstVals decl.typeConstants = some envTypes ∧ envTypes ≤ env ∧
    envTypes.Ordered ∧ type ∈ decl.types ∧ type.ctors = [ctor] ∧ type.name = S ∧
    info.uvars = decl.uvars ∧ info.nparams = decl.nparams ∧ info.nindices = type.numIndices ∧
    info.resultLevel = type.resultLevel ∧ info.ctorName = ctor.name ∧ info.ctorType = ctor.type ∧
    ctor.uvars = decl.uvars ∧ envTypes.IsType decl.uvars [] ctor.type ∧
    decl.RawCtorShape type ctor ∧ decl.sourceNames.Nodup

theorem VEnv.ProjOrigin.mono {env env' : VEnv} (hle : env ≤ env') :
    env.ProjOrigin S info → env'.ProjOrigin S info
  | ⟨base, envTypes, dsb, decl, type, ctor, h1, h2, h3, h4⟩ =>
    ⟨base, envTypes, dsb, decl, type, ctor, h1, h2, h3.trans hle, h4⟩

/-- The origin of a projection entry of a new block. -/
theorem VEnv.ProjOrigin.ofEntry {base envTypes env : VEnv} {dsb : List VDecl}
    {decl : VInductDecl} (hbase : base.WF' dsb)
    (htypes : base.addConstVals decl.typeConstants = some envTypes) (hle : envTypes ≤ env)
    (htypesWF : ∀ ci ∈ decl.typeConstants, ci.toVConstant.WF base)
    (hctorsWF : ∀ ctor ∈ decl.constructorConstants, ctor.toVConstant.WF envTypes)
    (huvars : ∀ ctor ∈ decl.constructorConstants, ctor.uvars = decl.uvars)
    (hshape : ∀ type ∈ decl.types, ∀ ctor ∈ type.ctors, decl.RawCtorShape type ctor)
    (hnodup : decl.sourceNames.Nodup)
    {entry : VProjectionEntry} (hentry : entry ∈ decl.projectionEntries) :
    env.ProjOrigin entry.typeName entry.info := by
  obtain ⟨type, htype, ctor, hctors, rfl⟩ := VInductDecl.projectionEntries_origin hentry
  have hmem : ctor ∈ type.ctors := by rw [hctors]; simp
  have hcc : ctor ∈ decl.constructorConstants := by
    simp only [VInductDecl.constructorConstants, List.mem_flatMap]
    exact ⟨type, htype, hmem⟩
  have hwf := hctorsWF ctor hcc
  have hu := huvars ctor hcc
  change envTypes.IsType ctor.uvars [] ctor.type at hwf
  rw [hu] at hwf
  have hord : envTypes.Ordered :=
    (show base.WF from ⟨dsb, hbase⟩).ordered.addConstVals htypesWF htypes
  exact ⟨base, envTypes, dsb, decl, type, ctor, hbase, htypes, hle, hord, htype, hctors, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, hu, hwf, hshape type htype ctor hmem, hnodup⟩

/-- **The origin of every projection entry** in the declaration history. -/
theorem VEnv.WF'.projOrigin {ds : List VDecl} {env : VEnv} (H : env.WF' ds) :
    ∀ {S info}, env.projections S info → env.ProjOrigin S info := by
  induction H with
  | empty => intro S info h; cases h
  | @decl d env' ds env0 hdecl hbase ih =>
    intro S info hp
    have hle := decl_le hdecl
    cases hdecl with
    | «axiom» _ hadd | «opaque» _ hadd =>
      rw [VEnv.addConst_projections hadd] at hp
      exact (ih hp).mono hle
    | «def» _ hadd =>
      have hp' : env0.projections S info := by
        have : _ = env0.projections := VEnv.addConst_projections hadd
        rw [← this]; exact hp
      exact (ih hp').mono hle
    | «example» => exact ih hp
    | mutualDef _ hadd _ =>
      rw [VEnv.addDefEqs_projections, VEnv.addConsts_projections hadd] at hp
      exact (ih hp).mono hle
    | quot _ hadd =>
      rw [VEnv.addQuot_projections hadd] at hp
      exact (ih hp).mono hle
    | induct hdeclWF hadd =>
      cases hadd with
      | intro _ hcompile hblock hinstall =>
        obtain ⟨envTypes, envCtors, envRecursors, htypes, hctors, hrecs, -, -, -, -⟩ := hblock
        have hinst := hinstall
        simp only [VInductBlock.install, htypes, hctors, hrecs, Option.bind_eq_bind,
          Option.bind_some, Option.pure_def, Option.some.injEq] at hinst
        subst hinst
        rw [VEnv.addDefEqRules_projections, VEnv.addConstVals_projections hrecs,
          VEnv.addProjections_iff] at hp
        rcases hp with ⟨entry, hentry, rfl, rfl⟩ | hold
        · rw [hcompile.projections] at hentry
          have htypes' := htypes
          rw [hcompile.types] at htypes'
          have hparams := hdeclWF.sourceParameterWF htypes'
          exact VEnv.ProjOrigin.ofEntry hbase htypes'
            ((VEnv.addConstVals_le hctors).trans <| VEnv.addProjections_le.trans <|
              (VEnv.addConstVals_le hrecs).trans VEnv.addDefEqRules_le)
            (typeConstants_wf hdeclWF.1.originalTypes) (hdeclWF.1.constructorsWF_at htypes') hdeclWF.1.2.2.2.1 hparams.rawCtorShape
            hcompile.sourceNames hentry
        · rw [VEnv.addConstVals_projections hctors, VEnv.addConstVals_projections htypes] at hold
          exact (ih hold).mono hle
  | inductEliminators _ _ _ _ _ _ _ _ _ ih =>
    intro S info hp
    rw [VEnv.addEliminator_projections] at hp
    exact (ih hp).mono VEnv.addEliminator_le
  | inductProjections hbase _ hsource htypesWF hconstructorUvars hctorsWF _ hshape htypesSource
      _ hprojections htypes hctors _ ihCtors =>
    intro S info hp
    rw [VEnv.addProjections_iff] at hp
    rcases hp with ⟨entry, hentry, rfl, rfl⟩ | hold
    · rw [hprojections] at hentry
      have htypes' := htypes
      rw [htypesSource] at htypes'
      exact VEnv.ProjOrigin.ofEntry hbase htypes'
        ((VEnv.addConstVals_le hctors).trans VEnv.addProjections_le)
        (typeConstants_wf htypesWF) hctorsWF hconstructorUvars hshape hsource hentry
    · exact (ihCtors hold).mono VEnv.addProjections_le

end Lean4Lean

namespace Lean4Lean

theorem VExpr.mkApps_getAppFnArgs_go : ∀ (e : VExpr) (args : List VExpr),
    VExpr.mkApps (VExpr.getAppFnArgs.go e args).1 (VExpr.getAppFnArgs.go e args).2 =
      VExpr.mkApps e args
  | .app f a, args => by
    rw [show VExpr.getAppFnArgs.go (.app f a) args = VExpr.getAppFnArgs.go f (a :: args) from rfl,
      VExpr.mkApps_getAppFnArgs_go f (a :: args)]
    rfl
  | .bvar .., _ | .sort .., _ | .const .., _ | .elim .., _ | .proj .., _ | .lam .., _
  | .forallE .., _ => rfl

theorem VExpr.mkApps_getAppFnArgs' (e : VExpr) :
    VExpr.mkApps e.getAppFnArgs.1 e.getAppFnArgs.2 = e :=
  VExpr.mkApps_getAppFnArgs_go e []

/-- **The syntactic shape of a projection-registered constructor type**: a telescope ending
in the family at its own universe parameters, applied to the parameter variables and to index
arguments. -/
theorem VEnv.ProjOrigin.ctorType_shape {env : VEnv} (h : env.ProjOrigin S info) :
    ∃ doms idx, info.ctorType = VExpr.wrapForalls doms
        (VExpr.mkApps (.const S (VLevel.params info.uvars))
          ((List.range info.nparams).reverse.map
              (fun i => .bvar (doms.length - info.nparams + i)) ++ idx)) ∧
      info.nparams ≤ doms.length ∧ idx.length = info.nindices := by
  obtain ⟨-, -, -, decl, type, ctor, -, -, -, -, htype, -, rfl, hu, hnp, hni, -, -, hct, -, -, hraw,
    hnodup⟩ := h
  obtain ⟨doms, result, heq, hle, ⟨type', hmem', htarget, levels, hfn, -, hargs, htake⟩, hhead⟩ :=
    hraw
  have hname : type.name = type'.name := by
    rcases htarget with h | h
    · cases h
    · exact Option.some.inj h
  have htt : type' = type := VInductDecl.type_eq_of_mem_name hnodup hmem' htype hname.symm
  subst htt
  have htake' : result.getAppFnArgs.2.take decl.nparams =
      decl.paramVars (doms.length - decl.nparams) := htake
  have hargs' : result.getAppFnArgs.2.length = decl.nparams + type'.numIndices := hargs
  have hres := VExpr.mkApps_getAppFnArgs' result
  rw [hhead, ← List.take_append_drop decl.nparams result.getAppFnArgs.2, htake'] at hres
  refine ⟨doms, result.getAppFnArgs.2.drop decl.nparams, ?_, by omega, ?_⟩
  · rw [hct, heq, hu, hnp]
    conv => lhs; rw [← hres]
    rfl
  · simp [hargs', hni]

/-- Every single-constructor family of a declaration has a projection entry. -/
theorem VInductDecl.mem_projectionEntries {decl : VInductDecl} {ty : VInductiveType}
    {ctor : VConstVal} (htype : ty ∈ decl.types) (hctors : ty.ctors = [ctor]) :
    VProjectionEntry.mk ty.name (VProjectionInfo.mk decl.uvars decl.nparams ty.numIndices
        ty.resultLevel ctor.name ctor.type) ∈
      decl.projectionEntries := by
  simp only [VInductDecl.projectionEntries, List.mem_filterMap]
  exact ⟨ty, htype, by rw [hctors]⟩

end Lean4Lean
