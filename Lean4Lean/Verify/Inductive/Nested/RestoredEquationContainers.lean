import Lean4Lean.Verify.Inductive.Nested.RestoredEquationWF

/-! The container fields of `NestedRestoredEquationGaps`
(`Nested/RestoredEquationWF.lean`): the typing of the restoration lambdas of
the auxiliary constructors (`auxiliaryConstructors`) and the transport of the
projection rules of the lowered declaration (`projections`).

**Auxiliary constructors.** The restoration lambda of an auxiliary
constructor head is `λ params, J.c levels args`, where `J.c` is a constructor
of the certified container `J` of the specialization. The container's
installation certificate records its source parameter formation: the
parameter prefix of the constructor type of `J.c` is definitionally the
parameter prefix of the family type of `J`
(`InstalledInductCertificate.ctorParameterContext`). The specialization
evidence types the family application `J levels args` in the source parameter
context, so the constructor application `J.c levels args` has the
instantiated constructor type (`HasType.const_mkApps_of_family`). Closing over
the signature parameters gives the type of the direct constructor, which is
definitionally the generated constructor type, the syntactic restoration of
the lowered constructor type.

**Projections.** A projection entry of a lowered original structure agrees
with the projection entry of the source structure, which the final
environment registers, except for its constructor type, which restores
syntactically to the source constructor type (and has the same forall arity,
`Restoration.expr_forallArity`). If the lowered constructor type mentions no
restorable name the two entries coincide and `ProjectionTransport.of_fixed`
applies. Otherwise `ProjectionTransport.of_ctorType` reduces the transport to
the correspondence of field types (`VEnv.ProjectionFieldTransport`): the
transported field type computed from the lowered constructor type is
definitionally the field type computed from the source constructor type. The
two differ by beta reduction of the restoration lambdas, below substitutions
of the parameters and of the projections of an arbitrary major premise; the
projection rule carries no well-formedness of its context, so beta subject
reduction (`BetaSubjectReduction`, stated for well-formed contexts) does not
apply. This correspondence, and the whole transport for the projections of
auxiliary structure-like families (renamed to their containers, whose
registered projection data is the container's, specialized at the
specialization arguments only up to beta reduction), form the hypothesis
`NestedProjectionTransportGap`.
-/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open InductiveSignature

namespace VerifyInductive

/-! ### Generic telescope lemmas -/

/-- Definitionally equal forall telescopes of the same length have
definitionally equal domain contexts. -/
theorem VEnv.IsDefEqU.wrapForalls_defeqCtx_inv {env : VEnv} {U : Nat} (henv : env.WF)
    {Γ₀ : List VExpr} :
    ∀ {A A' : List VExpr} {X X' : VExpr} {Γ₁ Γ₂ : List VExpr},
      A.length = A'.length →
      VEnv.IsDefEqCtx env U Γ₀ Γ₁ Γ₂ → OnCtx Γ₁ (env.IsType U) →
      env.IsDefEqU U Γ₁ (VExpr.wrapForalls A X) (VExpr.wrapForalls A' X') →
      VEnv.IsDefEqCtx env U Γ₀ (A.reverse ++ Γ₁) (A'.reverse ++ Γ₂)
  | [], [], _, _, _, _, _, hctx, _, _ => by simpa using hctx
  | [], _ :: _, _, _, _, _, h, _, _, _ => by simp at h
  | _ :: _, [], _, _, _, _, h, _, _, _ => by simp at h
  | d :: A, d' :: A', X, X', Γ₁, Γ₂, hlen, hctx, hΓ, H => by
    obtain ⟨⟨u, hd⟩, _, hb⟩ := Lean4Lean.VEnv.IsDefEqU.forallE_inv henv hΓ H
    have hctx' : VEnv.IsDefEqCtx env U Γ₀ (d :: Γ₁) (d' :: Γ₂) := .succ hctx hd
    have hΓ' : OnCtx (d :: Γ₁) (env.IsType U) := ⟨hΓ, u, hd.hasType.1⟩
    have := VEnv.IsDefEqU.wrapForalls_defeqCtx_inv henv (A := A) (A' := A')
      (X := X) (X' := X') (by simpa using hlen) hctx' hΓ' ⟨_, hb⟩
    simpa [List.reverse_cons, List.append_assoc] using this

/-- A constant whose type is a forall telescope whose parameter prefix is
definitionally that of another constant can be applied to every argument
spine consumed by that other constant's prefix. -/
theorem VEnv.HasType.const_mkApps_of_family {env : VEnv} {U N : Nat} (henv : env.WF)
    {Γ : List VExpr} (hΓ : OnCtx Γ (env.IsType U))
    {fam ctor : Name} {cf cc : VConstant}
    (hf : env.constants fam = some cf) (hc : env.constants ctor = some cc)
    {famDoms ctorDoms : List VExpr} {famRest ctorRest : VExpr}
    (hfty : cf.type = VExpr.wrapForalls famDoms famRest)
    (hcty : cc.type = VExpr.wrapForalls ctorDoms ctorRest)
    (hfu : cf.uvars = N) (hcu : cc.uvars = N)
    (hctx : VEnv.IsDefEqCtx env N [] famDoms.reverse ctorDoms.reverse)
    {levels : List VLevel} (hlev : ∀ l ∈ levels, l.WF U) (hlen : levels.length = N)
    {args : List VExpr} (hargs : args.length = famDoms.length) {T : VExpr}
    (happ : env.HasType U Γ (VExpr.mkApps (.const fam levels) args) T) :
    env.HasType U Γ (VExpr.mkApps (.const ctor levels) args)
      (VExpr.instantiateForallPrefix (cc.type.instL levels) args) := by
  have hordered := henv.ordered
  have hctxL := VEnv.IsDefEqCtx.instL hlev hctx
  simp only [List.map_nil, List.map_reverse] at hctxL
  have hf0 : env.HasType U [] (.const fam levels)
      (VExpr.wrapForalls (famDoms.map (VExpr.instL levels)) (famRest.instL levels)) := by
    have := VEnv.HasType.const (Γ := []) hf hlev (by rw [hfu]; exact hlen)
    rwa [hfty, VExpr.instL_wrapForalls] at this
  have hc0 : env.HasType U [] (.const ctor levels)
      (VExpr.wrapForalls (ctorDoms.map (VExpr.instL levels)) (ctorRest.instL levels)) := by
    have := VEnv.HasType.const (Γ := []) hc hlev (by rw [hcu]; exact hlen)
    rwa [hcty, VExpr.instL_wrapForalls] at this
  have hcT := VEnv.IsType.wrapForalls_inv hordered (ctx := []) trivial
    (VEnv.IsDefEq.isType hordered trivial hc0)
  have hY : env.IsType U (famDoms.map (VExpr.instL levels)).reverse (ctorRest.instL levels) := by
    have h2 : env.IsType U (ctorDoms.map (VExpr.instL levels)).reverse
        (ctorRest.instL levels) := by simpa using hcT.2
    exact h2.defeqDFC hordered (hctxL.symm hordered)
  obtain ⟨u, hu⟩ := hY
  have hW := VExpr.wrapForalls_defeqCtx henv (P := ctorDoms.map (VExpr.instL levels))
    (Q := famDoms.map (VExpr.instL levels)) (hctxL.symm hordered) ⟨u, hu⟩ ⟨_, hu⟩
  have hc1 := hc0.defeqU_r henv trivial hW
  have hcΓ : env.HasType U Γ (.const ctor levels)
      (VExpr.wrapForalls (famDoms.map (VExpr.instL levels)) (ctorRest.instL levels)) :=
    hc1.weak0 hordered
  have hfΓ : env.HasType U Γ (.const fam levels)
      (VExpr.wrapForalls (famDoms.map (VExpr.instL levels)) (famRest.instL levels)) :=
    hf0.weak0 hordered
  have Hdom : SameTelescopeDomains args.length
      (VExpr.wrapForalls (famDoms.map (VExpr.instL levels)) (ctorRest.instL levels))
      (VExpr.wrapForalls (famDoms.map (VExpr.instL levels)) (famRest.instL levels)) := by
    have := SameTelescopeDomains.wrapForalls (famDoms.map (VExpr.instL levels))
      (ctorRest.instL levels) (famRest.instL levels)
    rwa [List.length_map, ← hargs] at this
  have H := VEnv.HasType.mkApps_sameTelescopeDomains_exact henv hΓ Hdom hcΓ hfΓ ⟨_, happ⟩
  have hlenC : ctorDoms.length = famDoms.length := by
    have := hctx.length_eq
    simp only [List.length_reverse] at this
    omega
  rw [VExpr.applyForallType_eq_instantiateForallPrefix,
    VExpr.instantiateForallPrefix_wrapForalls _ _ _ (by simpa using hargs.symm)] at H
  rw [hcty, VExpr.instL_wrapForalls,
    VExpr.instantiateForallPrefix_wrapForalls _ _ _ (by simp [hlenC, hargs])]
  exact H

/-! ### Installed containers -/

private theorem install_base_le_REC {base installed : VEnv} {block : VInductBlock}
    (H : VInductBlock.install base block = some installed) : base ≤ installed := by
  simp only [VInductBlock.install, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.pure_def, Option.some.injEq] at H
  obtain ⟨types, ht, ctors, hc, recursors, hr, rfl⟩ := H
  exact (VEnv.addConstVals_le ht).trans <| (VEnv.addConstVals_le hc).trans <|
    VEnv.addProjections_le.trans <| (VEnv.addConstVals_le hr).trans VEnv.addDefEqRules_le

/-- The parameter prefix of every constructor type of an installed container
is definitionally the parameter prefix of its family type, given that the
family type has a syntactic parameter prefix. -/
theorem _root_.Lean4Lean.VEnv.InstalledInductCertificate.ctorParameterContext {env : VEnv}
    {decl : VInductDecl} (henv : env.WF) (H : VEnv.InstalledInductCertificate env decl)
    {type : VInductiveType} (htype : type ∈ decl.types)
    {ctor : VConstVal} (hctor : ctor ∈ type.ctors)
    (hpre : HasForallPrefix type.type decl.nparams) :
    ∃ famDoms famRest ctorDoms ctorRest,
      type.type = VExpr.wrapForalls famDoms famRest ∧
      ctor.type = VExpr.wrapForalls ctorDoms ctorRest ∧
      famDoms.length = decl.nparams ∧
      VEnv.IsDefEqCtx env decl.uvars [] famDoms.reverse ctorDoms.reverse := by
  obtain ⟨_, hfacts⟩ := H.familyFacts
  have hparams : ∃ base', base' ≤ env ∧ VInductDecl.SourceParameterWF base' decl := by
    cases H with
    | @intro _ _ base block installed hsource hformation hcompile _ hinstall hle =>
      have hbase : base ≤ env := (install_base_le_REC hinstall).trans hle
      cases hformation with
      | ordinary hwf => exact ⟨base, hbase, hwf.sourceParameterWF⟩
      | nested hnested hle' =>
        cases hnested with
        | intro _ _ hparams _ _ _ _ => exact ⟨_, hle'.trans hbase, hparams⟩
  obtain ⟨base', hbase', params, envT', htypes', hshapes, hctorShapes, -⟩ := hparams
  have hT'le : envT' ≤ env := VEnv.addConstVals_le_target hbase' htypes' (by
    intro value hvalue
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hvalue
    exact (hfacts t ht).1)
  obtain ⟨normalized, ownF, afterF, -, -, exprType, hdef, htakeF, -, hPF, -⟩ :=
    hshapes type htype
  obtain ⟨ctorDoms, ctorRest, htakeC, hPC⟩ := hctorShapes type htype ctor hctor
  obtain ⟨hctorEq, hctorLen⟩ := VExpr.takeForalls_rebuild htakeC
  obtain ⟨hnormEq, hnormLen⟩ := VExpr.takeForalls_rebuild htakeF
  obtain ⟨domains, body, htypeEq, hn⟩ := hpre
  have hsplit : type.type = VExpr.wrapForalls (domains.take decl.nparams)
      (VExpr.wrapForalls (domains.drop decl.nparams) body) := by
    rw [htypeEq, ← VExpr.wrapForalls_append, List.take_append_drop]
  have hfamLen : (domains.take decl.nparams).length = decl.nparams := by
    simp [List.length_take, Nat.min_eq_left hn]
  have hdefE : env.IsDefEqU decl.uvars [] (VExpr.wrapForalls (domains.take decl.nparams)
      (VExpr.wrapForalls (domains.drop decl.nparams) body))
      (VExpr.wrapForalls ownF afterF) := by
    rw [← hsplit, ← hnormEq]
    exact ⟨_, hdef.mono hbase'⟩
  have h1 := VEnv.IsDefEqU.wrapForalls_defeqCtx_inv henv (Γ₀ := []) (Γ₁ := []) (Γ₂ := [])
    (by rw [hfamLen, hnormLen]) .zero trivial hdefE
  simp only [List.append_nil] at h1
  have hPF' : VEnv.IsDefEqCtx env decl.uvars [] params.reverse ownF.reverse :=
    VEnv.IsDefEqCtx.mono hbase' hPF
  have hPC' : VEnv.IsDefEqCtx env decl.uvars [] params.reverse ctorDoms.reverse :=
    VEnv.IsDefEqCtx.mono hT'le hPC
  exact ⟨_, _, ctorDoms, ctorRest, hsplit, hctorEq, hfamLen,
    VEnv.IsDefEqCtx.transEmpty henv h1
      (VEnv.IsDefEqCtx.transEmpty henv (hPF'.symm henv.ordered) hPC')⟩

/-- An installed declaration exposes each of its constructor constants at the
exact abstract value recorded by the source declaration (membership form). -/
theorem _root_.Lean4Lean.VEnv.InstalledInductCertificate.constructorConstant_mem {env : VEnv}
    {decl : VInductDecl} (H : VEnv.InstalledInductCertificate env decl)
    {type : VInductiveType} (htype : type ∈ decl.types)
    {ctor : VConstVal} (hctor : ctor ∈ type.ctors) :
    env.constants ctor.name = some ctor.toVConstant := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp htype
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hctor
  exact H.constructorConstant i j hi hj

/-! ### Auxiliary constructors -/

private theorem nodup_map_inj_REC {f : α → β} :
    ∀ {l : List α}, (l.map f).Nodup → ∀ {x y}, x ∈ l → y ∈ l → f x = f y → x = y
  | [], _, _, _, hx, _, _ => by simp at hx
  | a :: l, hnd, x, y, hx, hy, hxy => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    rcases List.mem_cons.mp hx with hx' | hx' <;> rcases List.mem_cons.mp hy with hy' | hy'
    · exact hx'.trans hy'.symm
    · subst hx'; exact absurd ⟨y, hy', hxy.symm⟩ hnd.1
    · subst hy'; exact absurd ⟨x, hx', hxy⟩ hnd.1
    · exact nodup_map_inj_REC hnd.2 hx' hy' hxy

/-- **Typing of the restoration lambdas of the auxiliary constructors**, for
a specialization list with its evidence and a restoring expansion of the
lowered auxiliary families: the restoration lambda `λ params, J.c levels args`
of the head of a lowered auxiliary constructor has, in the source header
environment, the restoration of the lowered constructor type (which is the
generated constructor type). -/
theorem auxiliaryConstructorLambdas_hasType
    {base envTypes : VEnv} {paramCtx params : List VExpr} {decl : VInductDecl}
    {auxiliaries : List ContainerSpecialization}
    {generated targets : List VInductiveType}
    (henv : envTypes.WF) (hle : base ≤ envTypes)
    (Haux : List.Forall₂ (AuxiliarySpecializationEvidence base envTypes paramCtx decl)
      auxiliaries generated)
    (Hexp : List.Forall₂ (VInductDecl.NestedTypeExpansion base decl
        ((compilationRestoration decl auxiliaries).RestoringLeaf (VLevel.params decl.uvars)))
      generated targets)
    (hparams : VEnv.IsDefEqCtx envTypes decl.uvars [] params.reverse paramCtx)
    (hnodup : ((compilationRestoration decl auxiliaries).heads.map (·.auxiliary)).Nodup)
    (hfresh : ∀ name ∈ (compilationRestoration decl auxiliaries).restorableNames,
      envTypes.constants name = none)
    (hlevels : ∀ t ∈ targets, ∀ lc ∈ t.ctors,
      lc.type.ConstLevelsAt ((compilationRestoration decl auxiliaries).heads.map (·.auxiliary))
        (VLevel.params decl.uvars)) :
    ∀ t ∈ targets, ∀ lc ∈ t.ctors, ∀ h ∈ (compilationRestoration decl auxiliaries).heads,
      h.auxiliary = lc.name →
      ∃ restored, (compilationRestoration decl auxiliaries).expr lc.type = some restored ∧
        envTypes.HasType decl.uvars []
          (VExpr.wrapLams params (VExpr.mkApps (.const h.target h.levels) h.arguments))
          restored := by
  intro t ht lc hlc h hh hname
  have hordered := henv.ordered
  obtain ⟨g, hg, hexp⟩ := Lean4Lean.List.Forall₂.forall_exists_r Hexp t ht
  obtain ⟨a, ha, hev⟩ := Lean4Lean.List.Forall₂.forall_exists_r Haux g hg
  obtain ⟨gc, hgc, hc⟩ := Lean4Lean.List.Forall₂.forall_exists_r hexp.constructors lc hlc
  obtain ⟨sp, -, hspCtx, hspOn, htyping, -, hctors⟩ := hev.application
  obtain ⟨ctor, hctor, hdc⟩ := Lean4Lean.List.Forall₂.forall_exists_r hctors gc hgc
  -- the head of `lc` is the constructor head of `a` at `ctor`
  let hA : HeadSpecialization :=
    { auxiliary := a.constructorName ctor, uvars := decl.uvars, nparams := decl.nparams,
      target := ctor.name, levels := a.levels, arguments := a.arguments }
  have hAmem : hA ∈ (compilationRestoration decl auxiliaries).heads :=
    List.mem_flatMap.mpr ⟨a, ha, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨ctor, hctor, rfl⟩)⟩
  have hAname : hA.auxiliary = lc.name := by
    change a.constructorName ctor = lc.name
    rw [hc.name, hdc.name, ← hev.auxiliary]
    rfl
  have heq := nodup_map_inj_REC hnodup hh hAmem (hname.trans hAname.symm)
  subst heq
  -- restoration of the lowered constructor type
  obtain ⟨_, hgd⟩ := hdc.type
  have hfree : gc.type.containsAnyConst
      (compilationRestoration decl auxiliaries).restorableNames = false :=
    (hgd.hasType.1.noFreshConsts hordered hfresh (by intro _ h; simp at h)).1
  refine ⟨gc.type, hc.type.restore hfree (hlevels t ht lc hlc), ?_⟩
  -- typing of the container constructor application
  have hinst := hev.installed.mono hle
  have hsrc : a.source ∈ a.container.types := List.getElem_mem a.family.isLt
  obtain ⟨famDoms, famRest, ctorDoms, ctorRest, hfty, hcty, hfamLen, hctx⟩ :=
    hinst.ctorParameterContext henv hsrc hctor
      (by rw [← hev.argumentsLength]; exact hev.familyForallPrefix)
  have hfconst : envTypes.constants a.source.name = some a.source.toVConstant := by
    have := hinst.familyConstant a.family.val a.family.isLt
    exact this
  have hcconst := hinst.constructorConstant_mem hsrc hctor
  have hcapp := VEnv.HasType.const_mkApps_of_family henv hspOn hfconst hcconst hfty hcty
    (hinst.typeUvars _ hsrc)
    (hinst.constructorUvars _ (List.mem_flatMap.mpr ⟨_, hsrc, hctor⟩))
    hctx hev.levelsWF hev.levelsLength (by rw [hfamLen, hev.argumentsLength]) htyping
  have hPS : VEnv.IsDefEqCtx envTypes decl.uvars [] params.reverse sp.reverse :=
    VEnv.IsDefEqCtx.transEmpty henv hparams (hspCtx.symm hordered)
  have hcappP := hcapp.defeqDFC hordered (hPS.symm hordered)
  have hlam : envTypes.HasType decl.uvars []
      (VExpr.wrapLams params (VExpr.mkApps (.const ctor.name a.levels) a.arguments))
      (VExpr.wrapForalls params
        (VExpr.instantiateForallPrefix (ctor.type.instL a.levels) a.arguments)) :=
    VEnv.HasType.wrapLams (ctx := []) (by simpa using hPS.isType) (by simpa using hcappP)
  obtain ⟨u, hu⟩ := VEnv.IsDefEq.isType hordered hspOn hcapp
  have hforalls := VExpr.wrapForalls_defeqCtx henv hPS ⟨u, hu⟩ ⟨_, hu⟩
  exact hlam.defeqU_r henv trivial
    (VEnv.IsDefEqU.trans henv trivial hforalls ⟨_, hgd.symm⟩)

/-- **The `auxiliaryConstructors` field of `NestedRestoredEquationGaps`**,
for every restoration table of the run. The specialization list of
`restorationTablesRestoringAll` carries the evidence of
`auxiliaryConstructorLambdas_hasType`; its heads and restoration agree with
those of every other table (`RestorationTableData.find_transfer`,
`RestorationTableData.expr_eq`). -/
theorem NestedValidatedRunResult.restoredEquationAuxiliaryConstructors_of
    {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}
    (E : NestedValidatedRunResult result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (wf : ves.WF sourceProdEnv) (Hsources : SourceSyntaxChecks sourceTypes) :
    ∀ auxiliaries : List ContainerSpecialization,
      RestorationTableData sourceDecl auxiliaries result E.loweredEnv
        (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 lparams →
      ∀ envTypes : VEnv,
        (ves.venv (if isUnsafe then .unsafe else .safe)).addConstVals
          sourceDecl.typeConstants = some envTypes →
        ∀ t ∈ E.production.loweredDecl.types.drop sourceDecl.types.length,
          ∀ lc ∈ t.ctors, ∀ h ∈ (compilationRestoration sourceDecl auxiliaries).heads,
            h.auxiliary = lc.name →
            ∃ restored, (compilationRestoration sourceDecl auxiliaries).expr lc.type =
                some restored ∧
              envTypes.HasType sourceDecl.uvars []
                (VExpr.wrapLams E.production.compilationSignature.params
                  (VExpr.mkApps (.const h.target h.levels) h.arguments)) restored := by
  intro auxiliaries D envTypes' hadded' t ht lc hlc h hh hname
  have hnodup :
      (familyNames E.production.loweredDecl.types ++
        E.production.loweredDecl.types.map (fun t => t.name.str "rec")).Nodup := by
    rcases E.containerSpecializations wf Hsources with
      ⟨_, _, _, _, _, _, _, h, _⟩
    exact h
  rcases E.restorationTablesRestoringAll wf Hsources with
    ⟨envTypes, generated, aux', hadded, henvTypes, Haux, Hexpansion, -, D', -,
      HauxRestoring⟩
  have heq : envTypes' = envTypes := Option.some.inj (hadded'.symm.trans hadded)
  rw [heq]
  have hfreshAll := E.restorableNames_fresh hadded Haux Hexpansion hnodup
  have hlevels : ∀ t ∈ E.production.loweredDecl.types.drop sourceDecl.types.length,
      ∀ lc ∈ t.ctors, lc.type.ConstLevelsAt
        ((compilationRestoration sourceDecl aux').heads.map (·.auxiliary))
        (VLevel.params sourceDecl.uvars) := by
    have h := E.loweredAuxiliaryConstructorLevels wf Hsources
    rwa [← auxiliarySpecializations_headNames Haux Hexpansion,
      ← compilationRestoration_heads_auxiliary] at h
  have hlink : VEnv.IsDefEqCtx envTypes sourceDecl.uvars []
      (E.production.constructors.completed.parameterScope.toCtx.reverse).reverse
      E.production.headers.commonParameterContext := by
    rw [List.reverse_reverse,
      ConstructorPhasesResult.completed_parameterScope_toCtx]
    exact VEnv.IsDefEqCtx.mono (VEnv.addConstVals_le hadded)
      (E.commonParameterContext_refl wf)
  have hparams : E.production.compilationSignature.params =
      E.production.constructors.completed.parameterScope.toCtx.reverse :=
    E.production.loweredConstruction.consumedGeneration.params
  have hP : VEnv.IsDefEqCtx envTypes sourceDecl.uvars []
      E.production.compilationSignature.params.reverse
      E.production.headers.commonParameterContext := by
    rw [hparams]; exact hlink
  have hheadsNodup : ∀ {aux : List ContainerSpecialization},
      RestorationTableData sourceDecl aux result E.loweredEnv
        (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 lparams →
      ((compilationRestoration sourceDecl aux).heads.map (·.auxiliary)).Nodup := by
    intro aux Daux
    rw [compilationRestoration_heads_auxiliary]
    exact Daux.headNodup
  -- transfer the head to the table of `restorationTablesRestoringAll`
  have hfind := Restoration.find?_of_nodup (hheadsNodup D) hh
  have hfind' := D'.find_transfer D hfind
  have hmem' := List.mem_of_find?_eq_some hfind'
  obtain ⟨restored, hr, hty⟩ := auxiliaryConstructorLambdas_hasType henvTypes
    (VEnv.addConstVals_le hadded) Haux HauxRestoring hP (hheadsNodup D') hfreshAll hlevels
    t ht lc hlc h hmem' hname
  exact ⟨restored, by rw [D.expr_eq D']; exact hr, hty⟩


/-! ### Projections with a registered constructor type -/

/-- The field types of the projection `(typeName, info)`, transported along
`replaceRen ρ σ`, are definitionally the field types computed from the
registered constructor type `ctorType'` (at every sort typing of the
transported field type). -/
def _root_.Lean4Lean.VEnv.ProjectionFieldTransport (envS : VEnv)
    (ρ : Name → Option VExpr) (σ : Name → Name) (typeName : Name)
    (info : VProjectionInfo) (ctorType' : VExpr) : Prop :=
  ∀ {levels : List VLevel} {params : List VExpr} {index : Nat} {major fieldType : VExpr},
    info.fieldType typeName levels params index major = some fieldType →
    ∃ fieldType', { info with ctorType := ctorType' }.fieldType typeName levels
        (params.map (VExpr.replaceRen ρ σ)) index (major.replaceRen ρ σ) = some fieldType' ∧
      ∀ {U : Nat} {Γ : List VExpr} {fieldLevel : VLevel},
        envS.HasType U Γ (fieldType.replaceRen ρ σ) (.sort fieldLevel) →
        envS.IsDefEq U Γ fieldType' (fieldType.replaceRen ρ σ) (.sort fieldLevel)

/-- A projection whose type and constructor names are fixed by the
replacement transports to a projection registered with another constructor
type, of the same syntactic arity, whose field types are the transported
ones up to definitional equality. -/
theorem _root_.Lean4Lean.VEnv.ProjectionTransport.of_ctorType {envS : VEnv}
    {ρ : Name → Option VExpr} {σ : Name → Name} {typeName : Name}
    {info : VProjectionInfo} {ctorType' : VExpr}
    (hS : envS.projections typeName { info with ctorType := ctorType' })
    (htn : ρ typeName = none) (hσtn : σ typeName = typeName)
    (hctorName : ρ info.ctorName = none) (hσctor : σ info.ctorName = info.ctorName)
    (hclosed : ctorType'.Closed) (harity : ctorType'.forallArity = info.ctorType.forallArity)
    (HF : VEnv.ProjectionFieldTransport envS ρ σ typeName info ctorType') :
    VEnv.ProjectionTransport envS ρ σ typeName info where
  projDF := by
    intro U Γ levels params index sourceMajor fieldType fieldLevel major indexArgs major'
      hlevels huvars hparams hindices hfield _ hguard ihField ihLeft ihRight
    obtain ⟨fieldType', hfield', hdef⟩ := HF hfield
    have hdefF := hdef ihField
    simp only [VExpr.replaceRen_mkApps, List.map_append,
      VExpr.replaceRen_const_none htn, hσtn] at ihLeft ihRight
    simp only [VExpr.replaceRen, hσtn]
    exact .defeqDF hdefF (.projDF hS hlevels huvars (by simpa using hparams)
      (by simpa using hindices) hfield' hdefF.hasType.1 ihLeft ihRight hclosed hguard)
  projIota := by
    intro U Γ index levels args field fieldType ih1 h3 ih2
    simp only [VExpr.replaceRen, VExpr.replaceRen_mkApps, hctorName,
      hσctor, hσtn] at ih1 ⊢
    exact .projIota (info := { info with ctorType := ctorType' }) hS ih1 (by simp [h3]) ih2
  structEta := by
    intro U Γ levels params e h2 h3 ih1 ih2
    have hnf : ({ info with ctorType := ctorType' } : VProjectionInfo).numFields =
        info.numFields := by
      simp only [VProjectionInfo.numFields, harity]
    simp only [VExpr.replaceRen, VExpr.replaceRen_mkApps, List.map_append,
      List.map_map, Function.comp_def, hctorName, htn, hσctor, hσtn] at ih1 ih2 ⊢
    rw [← hnf] at ih2 ⊢
    exact .structEta hS (by simpa using h2) h3 ih1 ih2
  unitLike := by
    intro U Γ levels params e e' h2 h3 h4 ih1 ih2
    have hnf : ({ info with ctorType := ctorType' } : VProjectionInfo).numFields =
        info.numFields := by
      simp only [VProjectionInfo.numFields, harity]
    simp only [VExpr.replaceRen_mkApps, VExpr.replaceRen_const_none htn, hσtn] at ih1 ih2 ⊢
    exact .unitLike hS (by simpa using h2) h3 (hnf.trans h4) ih1 ih2

private theorem forallArity_mkApps_of_zero :
    ∀ {f : VExpr} (xs : List VExpr), f.forallArity = 0 →
      (VExpr.mkApps f xs).forallArity = 0
  | _, [], h => h
  | _, _ :: xs, _ => forallArity_mkApps_of_zero (f := .app _ _) xs rfl

private theorem forallArity_mkApps_cons (f x : VExpr) (xs : List VExpr) :
    (VExpr.mkApps f (x :: xs)).forallArity = 0 :=
  forallArity_mkApps_of_zero (f := .app f x) xs rfl

private theorem Restoration.go_forallArity (r : Restoration) :
    ∀ (e : VExpr) (args : List VExpr) (out : VExpr), Restoration.expr.go r e args = some out →
      out.forallArity = if args = [] then e.forallArity else 0 := by
  intro e
  induction e with
  | bvar i | sort u | elim b o ls =>
    intro args out h
    simp only [Restoration.expr.go, Option.some.injEq] at h
    subst h
    cases args with
    | nil => rfl
    | cons x xs => simp [forallArity_mkApps_cons]
  | const c ls =>
    intro args out h
    simp only [Restoration.expr.go] at h
    have h0 : out.forallArity = 0 := by
      split at h
      · next hd _ =>
        unfold HeadSpecialization.apply at h
        split at h
        · cases h
        · simp only [Option.pure_def, Option.some.injEq] at h
          subst h
          exact forallArity_mkApps_of_zero _ rfl
      · simp only [Option.some.injEq] at h
        subst h
        exact forallArity_mkApps_of_zero _ rfl
    rw [h0]; split <;> rfl
  | app fn arg ihf _ =>
    intro args out h
    simp only [Restoration.expr.go, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨arg', _, hfn⟩ := h
    rw [ihf _ _ hfn]
    simp [VExpr.forallArity]
  | lam d b _ _ =>
    intro args out h
    simp only [Restoration.expr.go, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq] at h
    obtain ⟨d', _, b', _, rfl⟩ := h
    rw [forallArity_mkApps_of_zero _ rfl]
    split <;> rfl
  | forallE d b _ ihb =>
    intro args out h
    simp only [Restoration.expr.go, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq] at h
    obtain ⟨d', _, b', hb, rfl⟩ := h
    cases args with
    | nil =>
      have := ihb [] b' hb
      simp only [if_true] at this
      simp [VExpr.mkApps, VExpr.forallArity, this]
    | cons x xs => simp [forallArity_mkApps_cons]
  | proj n i m _ =>
    intro args out h
    simp only [Restoration.expr.go, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq] at h
    obtain ⟨m', _, rfl⟩ := h
    rw [forallArity_mkApps_of_zero _ rfl]
    split <;> rfl

/-- Restoration preserves the syntactic forall arity. -/
theorem Restoration.expr_forallArity (r : Restoration) {e e' : VExpr}
    (h : r.expr e = some e') : e'.forallArity = e.forallArity := by
  simpa using Restoration.go_forallArity r e [] e' h

/-! ### Projections -/

theorem RestorationTableData.lambdaReplacement_eq {decl : VInductDecl}
    {result : Lean4Lean.ElimNestedInductive.Result} {env : Environment}
    {auxRec : NameMap Name} {Us₀ : List Name} {aux₀ aux₁ : List ContainerSpecialization}
    (D₀ : RestorationTableData decl aux₀ result env auxRec Us₀)
    (D₁ : RestorationTableData decl aux₁ result env auxRec Us₀)
    (domains : HeadSpecialization → List VExpr) :
    (compilationRestoration decl aux₀).lambdaReplacement domains =
      (compilationRestoration decl aux₁).lambdaReplacement domains := by
  funext c
  simp only [Restoration.lambdaReplacement, D₀.find_eq D₁ c]

theorem RestorationTableData.renaming_eq {decl : VInductDecl}
    {result : Lean4Lean.ElimNestedInductive.Result} {env : Environment}
    {auxRec : NameMap Name} {Us₀ : List Name} {aux₀ aux₁ : List ContainerSpecialization}
    (D₀ : RestorationTableData decl aux₀ result env auxRec Us₀)
    (D₁ : RestorationTableData decl aux₁ result env auxRec Us₀) :
    (compilationRestoration decl aux₀).renaming =
      (compilationRestoration decl aux₁).renaming := by
  funext n
  simp only [Restoration.renaming, D₀.find_eq D₁ n, D₀.recursorName n, D₁.recursorName n]

theorem RestorationTableData.restorable_iff {decl : VInductDecl}
    {result : Lean4Lean.ElimNestedInductive.Result} {env : Environment}
    {auxRec : NameMap Name} {Us₀ : List Name} {aux₀ aux₁ : List ContainerSpecialization}
    (D₀ : RestorationTableData decl aux₀ result env auxRec Us₀)
    (D₁ : RestorationTableData decl aux₁ result env auxRec Us₀) (n : Name) :
    n ∈ (compilationRestoration decl aux₀).restorableNames ↔
      n ∈ (compilationRestoration decl aux₁).restorableNames :=
  ⟨D₁.restorable_transfer D₀, D₀.restorable_transfer D₁⟩

theorem RestorationTableData.restorableNames_containsAnyConst {decl : VInductDecl}
    {result : Lean4Lean.ElimNestedInductive.Result} {env : Environment}
    {auxRec : NameMap Name} {Us₀ : List Name} {aux₀ aux₁ : List ContainerSpecialization}
    (D₀ : RestorationTableData decl aux₀ result env auxRec Us₀)
    (D₁ : RestorationTableData decl aux₁ result env auxRec Us₀) (e : VExpr) :
    e.containsAnyConst (compilationRestoration decl aux₀).restorableNames =
      e.containsAnyConst (compilationRestoration decl aux₁).restorableNames := by
  induction e with
  | bvar | sort | elim => rfl
  | const c ls =>
    simp only [VExpr.containsAnyConst]
    exact Bool.eq_iff_iff.mpr (by simpa using D₀.restorable_iff D₁ c)
  | app f a ihf iha | lam f a ihf iha | forallE f a ihf iha =>
    simp only [VExpr.containsAnyConst, ihf, iha]
  | proj n i e ih =>
    simp only [VExpr.containsAnyConst, ih]
    congr 1
    exact Bool.eq_iff_iff.mpr (by simpa using D₀.restorable_iff D₁ n)

/-- **The part of the `projections` field of `NestedRestoredEquationGaps`
that is not derived from the run.**

* `auxiliary`: the projection rules of the lowered projections of auxiliary
  structure-like families (whose type names are restorable, renamed to their
  containers) transport to the final abstract environment;
* `primaryFields`: for a lowered projection of an original structure whose
  lowered constructor type mentions a restorable name, the transported field
  types are definitionally the field types computed from the source
  constructor type registered by the final environment. -/
structure NestedProjectionTransportGap
    {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}
    (E : NestedValidatedRunResult result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (C : NestedFinalAssemblyShape E.restoration
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe))
    (auxiliaries : List ContainerSpecialization) : Prop where
  auxiliary : ∀ entry ∈ E.production.loweredDecl.projectionEntries,
    entry.typeName ∈ (compilationRestoration sourceDecl auxiliaries).restorableNames →
    VEnv.ProjectionTransport C.finalBaseVEnv
      ((compilationRestoration sourceDecl auxiliaries).lambdaReplacement
        fun _ => E.production.compilationSignature.params)
      (compilationRestoration sourceDecl auxiliaries).renaming
      entry.typeName entry.info
  primaryFields : ∀ entry ∈ E.production.loweredDecl.projectionEntries,
    ∀ src ∈ sourceDecl.projectionEntries, src.typeName = entry.typeName →
    entry.info.ctorType.containsAnyConst
      (compilationRestoration sourceDecl auxiliaries).restorableNames = true →
    VEnv.ProjectionFieldTransport C.finalBaseVEnv
      ((compilationRestoration sourceDecl auxiliaries).lambdaReplacement
        fun _ => E.production.compilationSignature.params)
      (compilationRestoration sourceDecl auxiliaries).renaming
      entry.typeName entry.info src.info.ctorType

/-- **The `projections` field of `NestedRestoredEquationGaps`** for the
projection entries of the original families. The entry of a lowered original
structure agrees with the projection entry of the source structure, which the
final environment registers, except for the constructor type, which restores
syntactically to the source constructor type. If the lowered constructor type
mentions no restorable name the two entries coincide
(`ProjectionTransport.of_fixed`); otherwise the transport follows from the
field-type hypothesis `primaryFields` (`ProjectionTransport.of_ctorType`). -/
theorem NestedValidatedRunResult.restoredEquationPrimaryProjections_of
    {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}
    (E : NestedValidatedRunResult result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (wf : ves.WF sourceProdEnv) (Hsources : SourceSyntaxChecks sourceTypes) :
    ∀ auxiliaries : List ContainerSpecialization,
      RestorationTableData sourceDecl auxiliaries result E.loweredEnv
        (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 lparams →
      ∀ C : NestedFinalAssemblyShape E.restoration
          (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
          nparams isUnsafe (if isUnsafe then .unsafe else .safe),
        C.production = E.production →
        (∀ entry ∈ E.production.loweredDecl.projectionEntries,
          ∀ src ∈ sourceDecl.projectionEntries, src.typeName = entry.typeName →
          entry.info.ctorType.containsAnyConst
            (compilationRestoration sourceDecl auxiliaries).restorableNames = true →
          VEnv.ProjectionFieldTransport C.finalBaseVEnv
            ((compilationRestoration sourceDecl auxiliaries).lambdaReplacement
              fun _ => E.production.compilationSignature.params)
            (compilationRestoration sourceDecl auxiliaries).renaming
            entry.typeName entry.info src.info.ctorType) →
        ∀ entry ∈ E.production.loweredDecl.projectionEntries,
          entry.typeName ∉ (compilationRestoration sourceDecl auxiliaries).restorableNames →
          VEnv.ProjectionTransport C.finalBaseVEnv
            ((compilationRestoration sourceDecl auxiliaries).lambdaReplacement
              fun _ => E.production.compilationSignature.params)
            (compilationRestoration sourceDecl auxiliaries).renaming
            entry.typeName entry.info := by
  intro auxiliaries D C hC HF entry hentry hTN₀
  have hnodup :
      (familyNames E.production.loweredDecl.types ++
        E.production.loweredDecl.types.map (fun t => t.name.str "rec")).Nodup := by
    rcases E.containerSpecializations wf Hsources with
      ⟨_, _, _, _, _, _, _, h, _⟩
    exact h
  rcases E.restorationTablesRestoringAll wf Hsources with
    ⟨envTypes, generated, aux', hadded, henvTypes, Haux, Hexpansion, -, D', Hrestoring, -⟩
  -- work with the table of `restorationTablesRestoringAll`
  rw [D.lambdaReplacement_eq D', D.renaming_eq D']
  rw [D.lambdaReplacement_eq D', D.renaming_eq D'] at HF
  have hTN : entry.typeName ∉ (compilationRestoration sourceDecl aux').restorableNames :=
    fun h => hTN₀ ((D.restorable_iff D' _).mpr h)
  have HF' : ∀ src ∈ sourceDecl.projectionEntries, src.typeName = entry.typeName →
      entry.info.ctorType.containsAnyConst
        (compilationRestoration sourceDecl aux').restorableNames = true →
      VEnv.ProjectionFieldTransport C.finalBaseVEnv
        ((compilationRestoration sourceDecl aux').lambdaReplacement
          fun _ => E.production.compilationSignature.params)
        (compilationRestoration sourceDecl aux').renaming
        entry.typeName entry.info src.info.ctorType := by
    intro src hsrc hname hCT
    exact HF entry hentry src hsrc hname (by rw [D.restorableNames_containsAnyConst D']; exact hCT)
  clear HF
  let r := compilationRestoration sourceDecl aux'
  obtain ⟨-, -, hauxNames, hheadNames', -, -, -, -, -⟩ :=
    E.restorationPrefix_of wf hadded henvTypes Haux Hexpansion hnodup D' True.intro
  obtain ⟨-, hheadNames, hnp, hargs, hPclosed, -, -⟩ :=
    E.headerSetup wf hadded henvTypes Haux Hexpansion hnodup
  have hclosed := Restoration.lambdaReplacement_closed hnp hargs hPclosed
  have hfreshAll := E.restorableNames_fresh hadded Haux Hexpansion hnodup
  have hlevels := E.loweredConstructorLevels_heads wf Hsources hheadNames'
  have hordered := henvTypes.ordered
  -- source constructor types are closed types mentioning no restorable name
  have hsourceTyped : ∀ family ∈ sourceDecl.types, ∀ sc ∈ family.ctors,
      ∃ u, envTypes.HasType sourceDecl.uvars [] sc.type (.sort u) := by
    have Hsource := E.nativeSource.core
    rw [E.nativeSourceDecl_eq] at Hsource
    have htypesEq : E.nativeSource.envTypes = envTypes :=
      Option.some.inj (Hsource.typesAdded.symm.trans hadded)
    intro family hfamily sc hsc
    obtain ⟨T, -, hT⟩ := Lean4Lean.List.Forall₂.forall_exists_r Hsource.types family hfamily
    obtain ⟨C, -, hC⟩ := Lean4Lean.List.Forall₂.forall_exists_r hT.ctors sc hsc
    obtain ⟨u, hu⟩ := hC.wf
    rw [htypesEq, hC.uvars, ← Hsource.uvars] at hu
    exact ⟨u, hu⟩
  have hsourceFree : ∀ family ∈ sourceDecl.types, ∀ sc ∈ family.ctors,
      sc.type.containsAnyConst r.restorableNames = false := by
    intro family hfamily sc hsc
    obtain ⟨u, hu⟩ := hsourceTyped family hfamily sc hsc
    exact (hu.noFreshConsts hordered hfreshAll (by intro _ h; simp at h)).1
  -- the expansion of the source families into the lowered prefix
  have hassembly := C.formationAssembly.types
  rw [C.formationExpanded, hC] at hassembly
  have hlen : sourceDecl.types.length =
      (E.production.loweredDecl.types.take sourceDecl.types.length).length := by
    have := Lean4Lean.List.Forall₂.length_eq hassembly
    simp only [List.length_append] at this
    simp only [List.length_take]
    omega
  rw [← List.take_append_drop sourceDecl.types.length E.production.loweredDecl.types]
    at hassembly
  have hprefixExp := ((Lean4Lean.List.Forall₂.append_of_left hlen).mp hassembly).1
  have Hboth := Lean4Lean.List.Forall₂.and hprefixExp Hrestoring
  -- the lowered entry
  obtain ⟨t, ht, lc, hlct, rfl⟩ := E.production.loweredDecl.projectionEntries_origin hentry
  simp only at hTN HF' ⊢
  have htTake : t ∈ E.production.loweredDecl.types.take sourceDecl.types.length := by
    rw [← List.take_append_drop sourceDecl.types.length E.production.loweredDecl.types] at ht
    rcases List.mem_append.mp ht with h | h
    · exact h
    · exfalso
      apply hTN
      apply List.mem_append_left
      rw [hheadNames]
      exact mem_familyNames.mpr ⟨t, h, .inl rfl⟩
  obtain ⟨st, hst, hexpT, hrestT⟩ := Lean4Lean.List.Forall₂.forall_exists_r Hboth t htTake
  have hlcmem : lc ∈ t.ctors := by rw [hlct]; exact List.mem_singleton_self lc
  obtain ⟨sc, hsc, hcexp⟩ :=
    Lean4Lean.List.Forall₂.forall_exists_r hexpT.constructors lc hlcmem
  obtain ⟨sc', hsc', hcrest⟩ := Lean4Lean.List.Forall₂.forall_exists_r hrestT lc hlcmem
  have hstCtors : st.ctors = [sc] := by
    have hl := Lean4Lean.List.Forall₂.length_eq hexpT.constructors
    rw [hlct] at hl
    obtain ⟨x, hx⟩ := List.length_eq_one_iff.mp hl
    rw [hx] at hsc ⊢
    rw [List.mem_singleton.mp hsc]
  have hsc'eq : sc' = sc := by
    rw [hstCtors] at hsc'
    simpa using hsc'
  rw [hsc'eq] at hcrest
  have hrestore : r.expr lc.type = some sc.type :=
    hcrest.restore (hsourceFree st hst sc hsc) (hlevels t htTake lc hlcmem)
  have hloweredUvars : E.production.loweredDecl.uvars = sourceDecl.uvars := by
    have h := C.formationAssembly.uvars
    rwa [C.formationExpanded, hC] at h
  have hloweredNparams : E.production.loweredDecl.nparams = sourceDecl.nparams := by
    have h := C.formationAssembly.nparams
    rwa [C.formationExpanded, hC] at h
  -- the registered source entry
  have hsrcEntry : (⟨st.name, ⟨sourceDecl.uvars, sourceDecl.nparams, st.numIndices,
      st.resultLevel, sc.name, sc.type⟩⟩ : VProjectionEntry) ∈
        sourceDecl.projectionEntries := by
    rw [VInductDecl.projectionEntries, List.mem_filterMap]
    exact ⟨st, hst, by simp [hstCtors]⟩
  have hS := C.canonical.recursorsAdded.le.projections
    (VEnv.addProjections_iff.mpr (Or.inl ⟨_, hsrcEntry, rfl, rfl⟩))
  have hctorName : lc.name ∉ r.restorableNames :=
    not_restorable_of_take hnodup hheadNames hauxNames
      (mem_familyNames.mpr ⟨t, htTake, .inr ⟨lc, hlcmem, rfl⟩⟩)
  have hρtn := Restoration.lambdaReplacement_eq_none_of_not_restorable
    (domains := fun _ => E.production.compilationSignature.params) hTN
  have hσtn := Restoration.renaming_eq_self hTN
  have hρctor := Restoration.lambdaReplacement_eq_none_of_not_restorable
    (domains := fun _ => E.production.compilationSignature.params) hctorName
  have hσctor := Restoration.renaming_eq_self hctorName
  have hS' : C.finalBaseVEnv.projections t.name ⟨E.production.loweredDecl.uvars,
      E.production.loweredDecl.nparams, t.numIndices, t.resultLevel, lc.name, sc.type⟩ := by
    rw [hloweredUvars, hloweredNparams, hexpT.name, hexpT.numIndices, hexpT.resultLevel,
      hcexp.name]
    exact hS
  cases hCT : lc.type.containsAnyConst r.restorableNames with
  | false =>
    -- the lowered and source entries coincide
    have htype : lc.type = sc.type :=
      Option.some.inj ((Restoration.expr_of_not_contains r hCT).symm.trans hrestore)
    rw [← htype] at hS'
    exact VEnv.ProjectionTransport.of_fixed hclosed hS' hρtn hσtn hρctor hσctor
      (Restoration.replaceRen_eq_self hCT)
  | true =>
    have harity := Restoration.expr_forallArity r hrestore
    obtain ⟨u, hu⟩ := hsourceTyped st hst sc hsc
    have hscClosed : sc.type.Closed := by
      simpa using hu.closedN hordered trivial
    exact VEnv.ProjectionTransport.of_ctorType hS' hρtn hσtn hρctor hσctor hscClosed harity
      (HF' _ hsrcEntry hexpT.name.symm hCT)

/-- **The `projections` field of `NestedRestoredEquationGaps`**, modulo
`NestedProjectionTransportGap`. -/
theorem NestedValidatedRunResult.restoredEquationProjections_of
    {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}
    (E : NestedValidatedRunResult result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (wf : ves.WF sourceProdEnv) (Hsources : SourceSyntaxChecks sourceTypes) :
    ∀ auxiliaries : List ContainerSpecialization,
      RestorationTableData sourceDecl auxiliaries result E.loweredEnv
        (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 lparams →
      ∀ C : NestedFinalAssemblyShape E.restoration
          (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
          nparams isUnsafe (if isUnsafe then .unsafe else .safe),
        C.production = E.production →
        NestedProjectionTransportGap E C auxiliaries →
        ∀ entry ∈ E.production.loweredDecl.projectionEntries,
          VEnv.ProjectionTransport C.finalBaseVEnv
            ((compilationRestoration sourceDecl auxiliaries).lambdaReplacement
              fun _ => E.production.compilationSignature.params)
            (compilationRestoration sourceDecl auxiliaries).renaming
            entry.typeName entry.info := by
  intro auxiliaries D C hC G entry hentry
  by_cases hTN : entry.typeName ∈ (compilationRestoration sourceDecl auxiliaries).restorableNames
  · exact G.auxiliary entry hentry hTN
  · exact E.restoredEquationPrimaryProjections_of wf Hsources auxiliaries D C hC
      G.primaryFields entry hentry hTN

/-- **The container fields (`auxiliaryConstructors` and `projections`) of
`NestedRestoredEquationGaps`** for every restoration table and final assembly
shape of the run, modulo `NestedProjectionTransportGap`. -/
theorem NestedValidatedRunResult.restoredEquationContainers_of
    {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}
    (E : NestedValidatedRunResult result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (wf : ves.WF sourceProdEnv) (Hsources : SourceSyntaxChecks sourceTypes) :
    ∀ auxiliaries : List ContainerSpecialization,
      RestorationTableData sourceDecl auxiliaries result E.loweredEnv
        (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 lparams →
      ∀ C : NestedFinalAssemblyShape E.restoration
          (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
          nparams isUnsafe (if isUnsafe then .unsafe else .safe),
        C.production = E.production →
        CheckingEnv.Valid (if isUnsafe then .unsafe else .safe)
          (Lean4Lean.stripRecursorRules outEnv
            (Lean4Lean.restoredRecursorNames
              (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 sourceTypes
              (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).1)) C.finalBaseVEnv →
        NestedProjectionTransportGap E C auxiliaries →
        (∀ envTypes : VEnv,
          (ves.venv (if isUnsafe then .unsafe else .safe)).addConstVals
            sourceDecl.typeConstants = some envTypes →
          ∀ t ∈ E.production.loweredDecl.types.drop sourceDecl.types.length,
            ∀ lc ∈ t.ctors, ∀ h ∈ (compilationRestoration sourceDecl auxiliaries).heads,
              h.auxiliary = lc.name →
              ∃ restored, (compilationRestoration sourceDecl auxiliaries).expr lc.type =
                  some restored ∧
                envTypes.HasType sourceDecl.uvars []
                  (VExpr.wrapLams E.production.compilationSignature.params
                    (VExpr.mkApps (.const h.target h.levels) h.arguments)) restored) ∧
        (∀ entry ∈ E.production.loweredDecl.projectionEntries,
          VEnv.ProjectionTransport C.finalBaseVEnv
            ((compilationRestoration sourceDecl auxiliaries).lambdaReplacement
              fun _ => E.production.compilationSignature.params)
            (compilationRestoration sourceDecl auxiliaries).renaming
            entry.typeName entry.info) := by
  intro auxiliaries D C hC _hV G
  exact ⟨E.restoredEquationAuxiliaryConstructors_of wf Hsources auxiliaries D,
    E.restoredEquationProjections_of wf Hsources auxiliaries D C hC G⟩

/-- Assemble `NestedRestoredEquationGaps` from its four projection-name
fields and the container fields of `restoredEquationContainers_of`. -/
theorem NestedValidatedRunResult.restoredEquationGaps_of_containers
    {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}
    (E : NestedValidatedRunResult result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (wf : ves.WF sourceProdEnv) (Hsources : SourceSyntaxChecks sourceTypes)
    {auxiliaries : List ContainerSpecialization}
    (D : RestorationTableData sourceDecl auxiliaries result E.loweredEnv
      (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 lparams)
    {C : NestedFinalAssemblyShape E.restoration
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe)}
    (hC : C.production = E.production)
    (hV : CheckingEnv.Valid (if isUnsafe then .unsafe else .safe)
      (Lean4Lean.stripRecursorRules outEnv
        (Lean4Lean.restoredRecursorNames
          (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 sourceTypes
          (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).1)) C.finalBaseVEnv)
    (G : NestedProjectionTransportGap E C auxiliaries)
    (eliminatorProjNames : EliminatorProjNamesAvoid
      (ves.venv (if isUnsafe then .unsafe else .safe))
      (compilationRestoration sourceDecl auxiliaries).restorableNames)
    (constructorProjNames : ∀ lc ∈ E.production.loweredDecl.constructorConstants,
      lc.type.projNamesAvoid (compilationRestoration sourceDecl auxiliaries).restorableNames =
        true)
    (recursorProjNames :
      ∀ owner : Fin E.production.production.completed.generationSignature.families.size,
        (E.production.production.completed.canonicalGeneration.recursorType owner).projNamesAvoid
          (compilationRestoration sourceDecl auxiliaries).restorableNames = true)
    (equationProjNames :
      ∀ k : Fin E.production.production.completed.generationSignature.constructors.size,
        (E.production.production.completed.canonicalGeneration.equation k).lhs.projNamesAvoid
            (compilationRestoration sourceDecl auxiliaries).restorableNames = true ∧
        (E.production.production.completed.canonicalGeneration.equation k).rhs.projNamesAvoid
            (compilationRestoration sourceDecl auxiliaries).restorableNames = true ∧
        (E.production.production.completed.canonicalGeneration.equation k).type.projNamesAvoid
            (compilationRestoration sourceDecl auxiliaries).restorableNames = true) :
    NestedRestoredEquationGaps E C auxiliaries :=
  let H := E.restoredEquationContainers_of wf Hsources auxiliaries D C hC hV G
  { eliminatorProjNames, constructorProjNames, recursorProjNames, equationProjNames,
    auxiliaryConstructors := H.1
    projections := H.2 }

end VerifyInductive
end Lean4Lean
