import Lean4Lean.Verify.Inductive.Nested.ConstructorRestoration
import Lean4Lean.Verify.Inductive.Nested.AuxiliaryFamilyCorrespondence
import Lean4Lean.Verify.Inductive.Nested.LoweringLevels

/-! Restoration of the auxiliary constructor types of a validated nested run
(the constructor-type conjunct of the `auxiliaryFamilies` field of
`NestedCompilationPending`).

Every lowered auxiliary family expands the generated family of its container
specialization by restoring leaves
(`NestedValidatedRunResult.restorationTablesRestoringAll`), so restoration
maps each lowered auxiliary constructor type syntactically to the generated
constructor type. The generated constructor type is definitionally the
container's constructor type instantiated at the specialization arguments,
under a parameter telescope definitionally equal to the common one; the
constructor of the direct family is the same instantiation under the
signature's parameters. The restoration substitution of
`Nested.ConstructorRestoration` transports the defeq of `Models.constructors`
between normalized and lowered constructor types to the source header
environment (`sourceConstructors_of_substitution`).
-/

namespace Lean4Lean

open InductiveSignature

namespace VerifyInductive

open Lean hiding Environment Exception
open Kernel

/-! ### Direct constructors -/

/-- The constructors of a direct family are the container constructors,
specialized at the arguments and closed over the given parameters. -/
theorem ContainerSpecialization.directFamily_ctors
    {a : ContainerSpecialization} {U : Nat} {params : List VExpr}
    {direct : VInductiveType} (H : a.directFamily U params = some direct) :
    List.Forall₂ (fun ctor dc : VConstVal => dc.type = VExpr.wrapForalls params
        (VExpr.instantiateForallPrefix (ctor.type.instL a.levels) a.arguments))
      a.source.ctors direct.ctors := by
  unfold ContainerSpecialization.directFamily at H
  simp only [bind, Option.bind_eq_some_iff] at H
  obtain ⟨type, _, ctors, hctors, he⟩ := H
  cases Option.some.inj he
  refine Lean4Lean.List.Forall₂.imp (fun ctor dc h => ?_) (List.mapM_eq_some.1 hctors)
  simp only [Option.bind_eq_some_iff, pure, Option.some.injEq] at h
  obtain ⟨spec, hspec, rfl⟩ := h
  rw [specializeType_eq_instantiateForallPrefix hspec]

/-- Replace a parameter telescope by a definitionally equal one, for a term
definitionally equal to the telescope. -/
theorem VEnv.IsDefEqU.wrapForalls_params {env : VEnv} {U : Nat} (henv : env.WF)
    {sp params : List VExpr} {X R : VExpr}
    (hctx : VEnv.IsDefEqCtx env U [] params.reverse sp.reverse)
    (h : env.IsDefEqU U [] X (VExpr.wrapForalls sp R)) :
    env.IsDefEqU U [] X (VExpr.wrapForalls params R) := by
  cases sp with
  | nil =>
    have hlen := hctx.length_eq
    simp only [List.length_reverse, List.length_nil, List.length_eq_zero_iff] at hlen
    subst hlen
    exact h
  | cons d rest =>
    obtain ⟨T, hT⟩ := h
    have hW : env.HasType U [] (.forallE d (VExpr.wrapForalls rest R)) T := hT.hasType.2
    obtain ⟨hd, hB⟩ := hW.forallE_inv henv.ordered
    have hR := (VEnv.IsType.wrapForalls_inv henv.ordered
      (ctx := [d]) ⟨trivial, hd⟩ hB).2
    have hY : env.IsType U (d :: rest).reverse R := by
      simpa [List.reverse_cons] using hR
    obtain ⟨u, hu⟩ := hY
    have hclose := VExpr.wrapForalls_defeqCtx henv hctx ⟨u, hu⟩ ⟨_, hu⟩
    exact VEnv.IsDefEqU.trans henv trivial ⟨T, hT⟩ hclose.symm

/-! ### Lowered auxiliary constructors restore to the direct constructors -/

/-- For auxiliary families expanding their generated families by restoring
leaves, restoration maps every lowered auxiliary constructor type to a term
equal (at every type) to the corresponding constructor type of the direct
family. -/
theorem auxiliaryLoweredConstructors_restore
    {base envTypes : VEnv} {paramCtx params : List VExpr} {decl : VInductDecl}
    {r : Restoration} {auxiliaries : List ContainerSpecialization}
    {generated targets direct : List VInductiveType}
    (henv : envTypes.WF)
    (Haux : List.Forall₂ (AuxiliarySpecializationEvidence base envTypes paramCtx decl)
      auxiliaries generated)
    (Hexp : List.Forall₂ (VInductDecl.NestedTypeExpansion base decl
        (r.RestoringLeaf (VLevel.params decl.uvars)))
      generated targets)
    (hparams : VEnv.IsDefEqCtx envTypes decl.uvars [] params.reverse paramCtx)
    (hfresh : ∀ name ∈ r.restorableNames, envTypes.constants name = none)
    (hlevels : ∀ t ∈ targets, ∀ lc ∈ t.ctors,
      lc.type.ConstLevelsAt (r.heads.map (·.auxiliary)) (VLevel.params decl.uvars))
    (hmapM : auxiliaries.mapM (fun a => a.directFamily decl.uvars params) = some direct) :
    List.Forall₂ (fun t d : VInductiveType => List.Forall₂
        (fun lc dc : VConstVal => ∃ restored, r.expr lc.type = some restored ∧
          envTypes.SimAt decl.uvars [] restored dc.type)
        t.ctors d.ctors)
      targets direct := by
  have hordered := henv.ordered
  induction Haux generalizing targets direct with
  | nil =>
    cases Hexp
    simp only [List.mapM_nil, pure, Option.some.injEq] at hmapM
    subst hmapM
    exact .nil
  | @cons a g auxs gens hev _ ih =>
    cases Hexp with
    | @cons _ t _ ts hexp hexps =>
    simp only [List.mapM_cons, bind, Option.bind_eq_some_iff, pure,
      Option.some.injEq] at hmapM
    obtain ⟨d, hd, ds, hds, rfl⟩ := hmapM
    refine .cons ?_ (ih hexps
      (fun t ht => hlevels t (List.mem_cons_of_mem _ ht)) hds)
    obtain ⟨sp, -, hspCtx, -, -, -, hctors⟩ := hev.application
    have hPS : VEnv.IsDefEqCtx envTypes decl.uvars [] params.reverse sp.reverse :=
      VEnv.IsDefEqCtx.transEmpty henv hparams (hspCtx.symm hordered)
    -- generated and direct constructors are definitionally equal
    have HGD : List.Forall₂ (fun gc dc : VConstVal =>
        envTypes.IsDefEqU decl.uvars [] gc.type dc.type) g.ctors d.ctors :=
      Lean4Lean.List.Forall₂.trans (fun gc c dc h1 h2 => by
          rw [h2]
          exact VEnv.IsDefEqU.wrapForalls_params henv hPS h1.type)
        (Lean4Lean.List.Forall₂.flip hctors)
        (ContainerSpecialization.directFamily_ctors hd)
    refine Lean4Lean.List.Forall₂.trans (fun lc gc dc h1 h2 => ?_)
      (Lean4Lean.List.Forall₂.flip
        (Lean4Lean.List.Forall₂.and_mem hexp.constructors)) HGD
    obtain ⟨hc, -, hlc⟩ := h1
    obtain ⟨_, hgd⟩ := h2
    have hfree : gc.type.containsAnyConst r.restorableNames = false :=
      (hgd.hasType.1.noFreshConsts hordered hfresh (by intro _ h; simp at h)).1
    exact ⟨gc.type, hc.type.restore hfree (hlevels t List.mem_cons_self lc hlc),
      fun _ hT => VEnv.IsDefEqU.of_l henv trivial ⟨_, hgd⟩ hT⟩

/-! ### The restoration substitution of a validated nested run -/

private theorem nodup_map_inj₄ {f : α → β} :
    ∀ {l : List α}, (l.map f).Nodup → ∀ {x y}, x ∈ l → y ∈ l → f x = f y → x = y
  | [], _, _, _, hx, _, _ => by simp at hx
  | a :: l, hnd, x, y, hx, hy, hxy => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    rcases List.mem_cons.mp hx with hx' | hx' <;> rcases List.mem_cons.mp hy with hy' | hy'
    · exact hx'.trans hy'.symm
    · subst hx'; exact absurd ⟨y, hy', hxy.symm⟩ hnd.1
    · subst hy'; exact absurd ⟨x, hx', hxy⟩ hnd.1
    · exact nodup_map_inj₄ hnd.2 hx' hy' hxy

private theorem forall₂_drop₄ {R : α → β → Prop} :
    ∀ {l : List α} {r : List β} (_ : List.Forall₂ R l r) (k : Nat),
      List.Forall₂ R (l.drop k) (r.drop k)
  | _, _, .nil, _ => by simp
  | _, _, .cons h t, 0 => by simpa using List.Forall₂.cons h t
  | _, _, .cons _ t, k + 1 => by
    simp only [List.drop_succ_cons]
    exact forall₂_drop₄ t k

/-- The restoration substitution of a validated nested run from the lowered
header environment to the source header environment
(`Restoration.lambdaReplacement_substitution` over the signature's
parameters), together with the definitional equality, in the lowered header
environment, of the normalized and lowered constructor types of every family
(`Models.constructors`). This is the setup of
`NestedValidatedRunResult.sourceConstructors_of_evidence`. -/
theorem NestedValidatedRunResult.constructorRestorationSubstitution
    {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}
    (E : NestedValidatedRunResult result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (wf : ves.WF sourceProdEnv)
    {envTypes : VEnv} {generated : List VInductiveType}
    {auxiliaries : List ContainerSpecialization}
    (hadded : (ves.venv (if isUnsafe then .unsafe else .safe)).addConstVals
      sourceDecl.typeConstants = some envTypes)
    (henvTypes : envTypes.WF)
    (Haux : List.Forall₂ (AuxiliarySpecializationEvidence
      (ves.venv (if isUnsafe then .unsafe else .safe)) envTypes
      E.production.headers.commonParameterContext sourceDecl)
      auxiliaries generated)
    (Hexpansion : List.Forall₂ (VInductDecl.NestedTypeExpansion
        (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl
        (VInductDecl.NestedAuxiliarySourceAbsolute
          (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl generated))
      generated (E.production.loweredDecl.types.drop sourceDecl.types.length))
    (hnodup : (familyNames E.production.loweredDecl.types ++
      E.production.loweredDecl.types.map (fun t => t.name.str "rec")).Nodup)
    (hfresh : ∀ name ∈ (compilationRestoration sourceDecl auxiliaries).heads.map
      (·.auxiliary), envTypes.constants name = none)
    (hrecFresh : ∀ p ∈ (compilationRestoration sourceDecl auxiliaries).recursors,
      envTypes.constants p.1 = none) :
    ∃ ρ, RestorationSubstitution envTypes E.production.constructors.completed.headerVEnv
        (compilationRestoration sourceDecl auxiliaries) ρ ∧
      List.Forall₂ (fun n l : VInductiveType => List.Forall₂
          (fun nc lc : VConstVal =>
            E.production.constructors.completed.headerVEnv.IsDefEqU sourceDecl.uvars []
              nc.type lc.type) n.ctors l.ctors)
        E.production.compilationSignature.declaration.types
        E.production.loweredDecl.types := by
  have hsuffixNodup :
      (familyNames (E.production.loweredDecl.types.drop sourceDecl.types.length) ++
        (E.production.loweredDecl.types.drop sourceDecl.types.length).map
          (fun t => t.name.str "rec")).Nodup := by
    refine hnodup.sublist (List.Sublist.append ?_ ((List.drop_sublist _ _).map _))
    conv => rhs; rw [← List.take_append_drop sourceDecl.types.length
      E.production.loweredDecl.types]
    simp only [familyNames, List.flatMap_append]
    exact List.sublist_append_right _ _
  have hlink : VEnv.IsDefEqCtx envTypes sourceDecl.uvars []
      (E.production.constructors.completed.parameterScope.toCtx.reverse).reverse
      E.production.headers.commonParameterContext := by
    rw [List.reverse_reverse,
      ConstructorPhasesResult.completed_parameterScope_toCtx]
    exact VEnv.IsDefEqCtx.mono (VEnv.addConstVals_le hadded)
      (E.commonParameterContext_refl wf)
  have hscoped := auxiliarySpecializations_scoped Haux Hexpansion hsuffixNodup
  have hinit : E.production.initialEnv =
      ves.venv (if isUnsafe then .unsafe else .safe) := E.production_initialEnv
  have hloweredTypes : (ves.venv (if isUnsafe then .unsafe else .safe)).addConstVals
      E.production.loweredDecl.typeConstants =
        some E.production.constructors.completed.headerVEnv :=
    Eq.mp (congrArg (fun env : VEnv => env.addConstVals
        E.production.loweredDecl.typeConstants =
          some E.production.constructors.completed.headerVEnv) hinit)
      E.production.constructors.completed.core.typesAdded
  have Hsource := E.nativeSource.core
  rw [E.nativeSourceDecl_eq] at Hsource
  have hsourceLength : sourceDecl.types.length = sourceTypes.length :=
    (TrInductDeclCore.types_length Hsource).symm
  have hprefix : sourceDecl.typeConstants =
      E.production.loweredDecl.typeConstants.take sourceDecl.types.length := by
    have h := E.nativeSource.sourceTypeValues
    rw [E.nativeSourceDecl_eq] at h
    rw [h, VInductDecl.typeConstants, List.map_take, hsourceLength]
  have hloweredSplit : (ves.venv (if isUnsafe then .unsafe else .safe)).addConstVals
      (sourceDecl.typeConstants ++
        (E.production.loweredDecl.types.drop sourceDecl.types.length).map
          VInductiveType.toVConstVal) =
        some E.production.constructors.completed.headerVEnv := by
    rw [hprefix, VInductDecl.typeConstants, List.map_drop, List.take_append_drop]
    exact hloweredTypes
  have Hmodels : E.production.compilationSignature.Models
      (ves.venv (if isUnsafe then .unsafe else .safe)) E.production.loweredDecl := by
    have h := E.production.loweredConstruction.consumedGeneration.models
    change E.production.compilationSignature.Models E.production.initialEnv
      E.production.loweredDecl at h
    rwa [hinit] at h
  have hheadNames : (compilationRestoration sourceDecl auxiliaries).heads.map (·.auxiliary) =
      familyNames (E.production.loweredDecl.types.drop sourceDecl.types.length) := by
    rw [compilationRestoration_heads_auxiliary]
    exact auxiliarySpecializations_headNames Haux Hexpansion
  have hparams : E.production.compilationSignature.params =
      E.production.constructors.completed.parameterScope.toCtx.reverse :=
    E.production.loweredConstruction.consumedGeneration.params
  have hP : VEnv.IsDefEqCtx envTypes sourceDecl.uvars []
      E.production.compilationSignature.params.reverse
      E.production.headers.commonParameterContext := by
    rw [hparams]; exact hlink
  have hPclosed : ∀ i (hi : i < E.production.compilationSignature.params.length),
      E.production.compilationSignature.params[i].ClosedN i := by
    intro i hi
    simpa using OnCtx.reverse_getElem_closedN henvTypes (Γ := [])
      (by simpa using hP.isType) i hi
  have hordered := henvTypes.ordered
  have hscopedNodup := hscoped.1
  have hfamilyHead : ∀ t ∈ E.production.loweredDecl.types.drop sourceDecl.types.length,
      ∃ a ∈ auxiliaries, ∃ g,
        AuxiliarySpecializationEvidence (ves.venv (if isUnsafe then .unsafe else .safe))
          envTypes E.production.headers.commonParameterContext sourceDecl a g ∧
        VInductDecl.NestedTypeExpansion (ves.venv (if isUnsafe then .unsafe else .safe))
          sourceDecl (VInductDecl.NestedAuxiliarySourceAbsolute
            (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl generated) g t := by
    intro t ht
    obtain ⟨g, hg, hexp⟩ := Lean4Lean.List.Forall₂.forall_exists_r Hexpansion t ht
    obtain ⟨a, ha, hev⟩ := Lean4Lean.List.Forall₂.forall_exists_r Haux g hg
    exact ⟨a, ha, g, hev, hexp⟩
  have hheadsParams : ∀ h ∈ (compilationRestoration sourceDecl auxiliaries).heads,
      h.nparams = E.production.compilationSignature.params.length := by
    intro h hh
    obtain ⟨a, ha, hh⟩ := List.mem_flatMap.mp hh
    have hn : h.nparams = sourceDecl.nparams := by
      simp only [ContainerSpecialization.heads, List.mem_cons, List.mem_map] at hh
      rcases hh with rfl | ⟨_, _, rfl⟩ <;> rfl
    obtain ⟨g, -, hev⟩ := Lean4Lean.List.Forall₂.forall_exists_l Haux a ha
    obtain ⟨sourceParams, hlen, hctx, -⟩ := hev.application
    rw [hn, ← hlen]
    have h1 := hctx.length_eq
    have h2 := hP.length_eq
    simp only [List.length_reverse] at h1 h2
    omega
  have hreplaced : ∀ h ∈ (compilationRestoration sourceDecl auxiliaries).heads, ∀ ci,
      E.production.constructors.completed.headerVEnv.constants h.auxiliary = some ci →
      ci.type.containsAnyConst
          ((compilationRestoration sourceDecl auxiliaries).heads.map (·.auxiliary)) = false ∧
      envTypes.HasType ci.uvars []
        (VExpr.wrapLams E.production.compilationSignature.params
          (VExpr.mkApps (.const h.target h.levels) h.arguments)) ci.type := by
    intro h hh ci hci
    rcases lookup_of_addConstVals_append hadded hloweredSplit hci with
      henvT | ⟨entry, hentry, hn, hval⟩
    · rw [hfresh _ (List.mem_map_of_mem hh)] at henvT; cases henvT
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hentry
    obtain ⟨a, ha, g, hev, hexp⟩ := hfamilyHead t ht
    have hfh : InductiveSignature.HeadSpecialization.mk a.auxiliary sourceDecl.uvars
        sourceDecl.nparams a.source.name a.levels a.arguments ∈
        (compilationRestoration sourceDecl auxiliaries).heads :=
      List.mem_flatMap.mpr ⟨a, ha, List.mem_cons_self⟩
    have heqh := nodup_map_inj₄ hscopedNodup hh hfh
      (hn.symm.trans (hexp.name.trans hev.auxiliary.symm))
    subst heqh
    subst hval
    obtain ⟨sourceParams, hlen, hctx, honctx, htyping, hgtype, -⟩ := hev.application
    have htype : envTypes.IsDefEqU sourceDecl.uvars [] g.type t.type :=
      hexp.type.mono (VEnv.addConstVals_le hadded)
    obtain ⟨_, htypeD⟩ := htype
    have huvars : t.uvars = sourceDecl.uvars := hexp.uvars.trans hev.generatedUvars
    change t.type.containsAnyConst _ = false ∧
      envTypes.HasType t.uvars [] _ t.type
    rw [huvars]
    refine ⟨(htypeD.noFreshConsts hordered hfresh (by intro _ h; simp at h)).2.1, ?_⟩
    have hPS : VEnv.IsDefEqCtx envTypes sourceDecl.uvars []
        E.production.compilationSignature.params.reverse sourceParams.reverse :=
      VEnv.IsDefEqCtx.transEmpty henvTypes hP (hctx.symm hordered)
    have htypingP := htyping.defeqDFC hordered (hPS.symm hordered)
    have hlam : envTypes.HasType sourceDecl.uvars []
        (VExpr.wrapLams E.production.compilationSignature.params
          (VExpr.mkApps (.const a.source.name a.levels) a.arguments))
        (VExpr.wrapForalls E.production.compilationSignature.params
          (VExpr.instantiateForallPrefix (a.source.type.instL a.levels) a.arguments)) :=
      VEnv.HasType.wrapLams (ctx := []) (by simpa using hP.isType) (by simpa using htypingP)
    obtain ⟨u, hu⟩ := htyping.isType hordered honctx
    have hforalls := VExpr.wrapForalls_defeqCtx henvTypes hPS ⟨u, hu⟩ ⟨_, hu⟩
    have hchain : envTypes.IsDefEqU sourceDecl.uvars []
        (VExpr.wrapForalls E.production.compilationSignature.params
          (VExpr.instantiateForallPrefix (a.source.type.instL a.levels) a.arguments))
        t.type :=
      VEnv.IsDefEqU.trans henvTypes trivial hforalls
        (VEnv.IsDefEqU.trans henvTypes trivial hgtype.symm ⟨_, htypeD⟩)
    exact hlam.defeqU_r henvTypes trivial hchain
  have S := Restoration.lambdaReplacement_substitution
    (r := compilationRestoration sourceDecl auxiliaries)
    (P := E.production.compilationSignature.params)
    henvTypes hadded hloweredSplit hheadsParams
    (fun h hh arg harg => (hscoped.2.2.1 h hh).2 arg harg) hPclosed hfresh
    (by
      intro entry hentry
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hentry
      rw [hheadNames]
      exact mem_familyNames.mpr ⟨t, ht, .inl rfl⟩)
    hrecFresh hreplaced (henvTypes.eliminatorsAvoidConsts hfresh)
  have hloweredUvars : E.production.loweredDecl.uvars = sourceDecl.uvars := by
    have h1 := E.production.constructors.completed.core.uvars
    have h2 := E.nativeSource.core.uvars
    rw [E.nativeSourceDecl_eq] at h2
    rw [h1, h2, E.production_c, E.productionContext_lparams]
  obtain ⟨envT, henvT, Hctors⟩ := Hmodels.constructors
  rw [hloweredTypes] at henvT
  cases henvT
  have Hlengths : List.Forall₂ (fun a b : VInductiveType => a.ctors.length = b.ctors.length)
      E.production.compilationSignature.declaration.types E.production.loweredDecl.types :=
    Lean4Lean.List.Forall₂.imp (fun _ _ h => by
      simpa using congrArg List.length h.2.2.2.2) Hmodels.families
  exact ⟨_, S, forall₂_ctors_split (R := fun nc lc : VConstVal =>
      E.production.constructors.completed.headerVEnv.IsDefEqU sourceDecl.uvars []
        nc.type lc.type) Hlengths
    (Lean4Lean.List.Forall₂.imp (fun _ _ h => by
      rw [hloweredUvars] at h
      exact h.2.2) Hctors)⟩

/-- **Restoration of the auxiliary constructor types of a validated nested
run** (the constructor-type conjunct of the `auxiliaryFamilies` field of
`NestedCompilationPending`), for any specialization list whose auxiliary
families expand their generated families by restoring leaves, given that
restoration is defined on the normalized auxiliary constructor types. -/
theorem NestedValidatedRunResult.auxiliaryConstructors_of_evidence
    {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}
    (E : NestedValidatedRunResult result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (wf : ves.WF sourceProdEnv) (Hsources : SourceSyntaxChecks sourceTypes)
    {envTypes : VEnv} {generated : List VInductiveType}
    {auxiliaries : List ContainerSpecialization}
    (hadded : (ves.venv (if isUnsafe then .unsafe else .safe)).addConstVals
      sourceDecl.typeConstants = some envTypes)
    (henvTypes : envTypes.WF)
    (Haux : List.Forall₂ (AuxiliarySpecializationEvidence
      (ves.venv (if isUnsafe then .unsafe else .safe)) envTypes
      E.production.headers.commonParameterContext sourceDecl)
      auxiliaries generated)
    (Hexpansion : List.Forall₂ (VInductDecl.NestedTypeExpansion
        (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl
        (VInductDecl.NestedAuxiliarySourceAbsolute
          (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl generated))
      generated (E.production.loweredDecl.types.drop sourceDecl.types.length))
    (HauxRestoring : List.Forall₂ (VInductDecl.NestedTypeExpansion
        (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl
        ((compilationRestoration sourceDecl auxiliaries).RestoringLeaf
          (VLevel.params sourceDecl.uvars)))
      generated (E.production.loweredDecl.types.drop sourceDecl.types.length))
    (hnodup : (familyNames E.production.loweredDecl.types ++
      E.production.loweredDecl.types.map (fun t => t.name.str "rec")).Nodup)
    (htotal : ∀ normalized ∈ E.production.compilationSignature.declaration.types.drop
        sourceDecl.types.length,
      ∀ ctor ∈ normalized.ctors, ∃ restored,
        (compilationRestoration sourceDecl auxiliaries).expr ctor.type = some restored) :
    ∀ envTypes direct,
      (ves.venv (if isUnsafe then .unsafe else .safe)).addConstVals
        sourceDecl.typeConstants = some envTypes →
      auxiliaries.mapM (fun a => a.directFamily sourceDecl.uvars
        E.production.compilationSignature.params) = some direct →
      List.Forall₂ (fun normalized family : VInductiveType =>
          List.Forall₂ (fun normalized ctor : VConstVal =>
            RestoresType (compilationRestoration sourceDecl auxiliaries) envTypes
              sourceDecl.uvars normalized.type ctor.type)
            normalized.ctors family.ctors)
        (E.production.compilationSignature.declaration.types.drop
          sourceDecl.types.length) direct := by
  intro envTypes' direct hadded' hmapM
  rw [hadded] at hadded'
  cases hadded'
  let r := compilationRestoration sourceDecl auxiliaries
  have hfreshAll := E.restorableNames_fresh hadded Haux Hexpansion hnodup
  have hfresh : ∀ name ∈ r.heads.map (·.auxiliary), envTypes.constants name = none :=
    fun name hname => hfreshAll name (List.mem_append_left _ hname)
  have hrecFresh : ∀ p ∈ r.recursors, envTypes.constants p.1 = none :=
    fun p hp => hfreshAll p.1 (List.mem_append_right _ (List.mem_map_of_mem hp))
  obtain ⟨ρ, S, Hdefeq⟩ := E.constructorRestorationSubstitution wf hadded henvTypes
    Haux Hexpansion hnodup hfresh hrecFresh
  -- the common parameter telescope
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
  -- the universe arguments of the lowered auxiliary constructor types
  have hlevels : ∀ t ∈ E.production.loweredDecl.types.drop sourceDecl.types.length,
      ∀ lc ∈ t.ctors, lc.type.ConstLevelsAt (r.heads.map (·.auxiliary))
        (VLevel.params sourceDecl.uvars) := by
    have h := E.loweredAuxiliaryConstructorLevels wf Hsources
    rwa [← auxiliarySpecializations_headNames Haux Hexpansion,
      ← compilationRestoration_heads_auxiliary] at h
  have Hlowered := auxiliaryLoweredConstructors_restore henvTypes Haux HauxRestoring hP
    hfreshAll hlevels hmapM
  exact sourceConstructors_of_substitution S henvTypes.betaSubjectReduction
    (forall₂_drop₄ Hdefeq sourceDecl.types.length) Hlowered htotal

/-- The lowered auxiliary constructor types restore syntactically to the
generated constructor types, so restoration is total on them. -/
theorem auxiliaryLoweredConstructors_total
    {base envTypes : VEnv} {paramCtx : List VExpr} {decl : VInductDecl}
    {r : Restoration} {auxiliaries : List ContainerSpecialization}
    {generated targets : List VInductiveType}
    (henv : envTypes.WF)
    (Haux : List.Forall₂ (AuxiliarySpecializationEvidence base envTypes paramCtx decl)
      auxiliaries generated)
    (Hexp : List.Forall₂ (VInductDecl.NestedTypeExpansion base decl
        (r.RestoringLeaf (VLevel.params decl.uvars)))
      generated targets)
    (hfresh : ∀ name ∈ r.restorableNames, envTypes.constants name = none)
    (hlevels : ∀ t ∈ targets, ∀ lc ∈ t.ctors,
      lc.type.ConstLevelsAt (r.heads.map (·.auxiliary)) (VLevel.params decl.uvars)) :
    ∀ t ∈ targets, ∀ lc ∈ t.ctors, ∃ restored, r.expr lc.type = some restored := by
  intro t ht lc hlc
  obtain ⟨g, hg, hexp⟩ := Lean4Lean.List.Forall₂.forall_exists_r Hexp t ht
  obtain ⟨a, -, hev⟩ := Lean4Lean.List.Forall₂.forall_exists_r Haux g hg
  obtain ⟨gc, hgc, hc⟩ := Lean4Lean.List.Forall₂.forall_exists_r hexp.constructors lc hlc
  obtain ⟨sp, -, -, -, -, -, hctors⟩ := hev.application
  obtain ⟨c, -, hdc⟩ := Lean4Lean.List.Forall₂.forall_exists_r hctors gc hgc
  obtain ⟨_, hgd⟩ := hdc.type
  have hfree : gc.type.containsAnyConst r.restorableNames = false :=
    (hgd.hasType.1.noFreshConsts henv.ordered hfresh (by intro _ h; simp at h)).1
  exact ⟨gc.type, hc.type.restore hfree (hlevels t ht lc hlc)⟩

end VerifyInductive

end Lean4Lean
