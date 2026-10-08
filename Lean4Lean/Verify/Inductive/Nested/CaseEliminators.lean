import Lean4Lean.Verify.Inductive.Nested.FinalAssembly
import Lean4Lean.Verify.Inductive.ConstructorBoundary
import Lean4Lean.Theory.Inductive.CaseCertificateTransport
import Lean4Lean.Verify.Inductive.Nested.CaseEliminatorPieces
import Lean4Lean.Verify.Inductive.Nested.CompilationDataConstructors
import Lean4Lean.Verify.Inductive.Nested.AuxiliaryConstructorRestoration
import Lean4Lean.Verify.Inductive.Nested.RestorationAgreement
import Lean4Lean.Verify.Inductive.Nested.FinalShapes
import Lean4Lean.Verify.Inductive.Nested.WhnfHitShape

/-! # Certified case eliminators of a nested declaration

The source declaration of a validated nested run registers its case eliminator before its
projections and restored recursors (`VInductBlock.install`). The lowered declaration registers,
at its constructor boundary `B`, the restoration-free schema of the boundary signature
`B.sourceSignature` (`CompletedConstructorPhases.eliminatorsBoundary`). The source declaration
registers the same signature under the same key, restored by the nested compilation restoration:
`CaseSchema.ofCompilation sourceDecl B.sourceSignature auxiliaries`. This file certifies it from
the validated run alone, without the final assembly shape (which already carries the
eliminators). -/

open Lean4Lean.InductiveSignature

namespace Lean4Lean.VerifyInductive

open Lean hiding Environment Exception
open Lean.Kernel

private theorem forall₂_drop' {R : α → β → Prop} :
    ∀ {l : List α} {r : List β} (_ : List.Forall₂ R l r) (k : Nat),
      List.Forall₂ R (l.drop k) (r.drop k)
  | _, _, .nil, _ => by simp
  | _, _, .cons h t, 0 => by simpa using List.Forall₂.cons h t
  | _, _, .cons _ t, k + 1 => by
    simp only [List.drop_succ_cons]
    exact forall₂_drop' t k

/-- Constants with distinct names that are fresh in an environment can be installed in it. -/
theorem VEnv.addConstVals_exists_of_fresh :
    ∀ {env : VEnv} {cis : List VConstVal}, (cis.map (·.name)).Nodup →
      (∀ ci ∈ cis, env.constants ci.name = none) → ∃ env', env.addConstVals cis = some env'
  | env, [], _, _ => ⟨env, rfl⟩
  | env, ci :: cis, hnodup, hfresh => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnodup
    have hadd : env.addConst ci.name ci.toVConstant = some { env with
        constants := fun n => if ci.name = n then some ci.toVConstant else env.constants n } := by
      simp [VEnv.addConst, hfresh ci List.mem_cons_self]
    obtain ⟨env', h⟩ := VEnv.addConstVals_exists_of_fresh (env := { env with
        constants := fun n => if ci.name = n then some ci.toVConstant else env.constants n })
      hnodup.2 (by
        intro c hc
        have hne : ci.name ≠ c.name := fun h => hnodup.1 ⟨c, hc, h.symm⟩
        simp [hne, hfresh c (List.mem_cons_of_mem _ hc)])
    exact ⟨env', by simp [VEnv.addConstVals, hadd, h]⟩

/-- The boundary signature models the lowered declaration in the base environment, its
parameters are the common parameter context, and restoration is total on its constructor
types. -/
theorem NestedValidatedRunResult.boundarySignatureFacts
    {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}
    (E : NestedValidatedRunResult result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (wf : ves.WFCore sourceProdEnv) (Hsources : SourceSyntaxChecks sourceTypes)
    (B : ConstructorBoundary E.production.c E.production.stats E.production.loweredDecl
      E.production.nparams E.production.isUnsafe E.production.depth E.production.initialEnv
      E.production.indTypes)
    (hBscope : B.parameterScope = E.production.constructors.completed.parameterScope)
    {envTypes : VEnv} {auxiliaries : List ContainerSpecialization}
    (hadded : (ves.venv (if isUnsafe then .unsafe else .safe)).addConstVals
      sourceDecl.typeConstants = some envTypes)
    (hheadNames : auxiliaries.flatMap (·.headNames) =
      familyNames (E.production.loweredDecl.types.drop sourceDecl.types.length))
    (hloweredNe : E.production.loweredDecl.types ≠ []) :
    B.sourceSignature.Models (ves.venv (if isUnsafe then .unsafe else .safe))
        E.production.loweredDecl ∧
      VEnv.IsDefEqCtx envTypes sourceDecl.uvars [] B.sourceSignature.params.reverse
        E.production.headers.commonParameterContext ∧
      ∀ normalized ∈ B.sourceSignature.declaration.types, ∀ ctor ∈ normalized.ctors,
        ∃ restored, (compilationRestoration sourceDecl auxiliaries).expr ctor.type =
          some restored := by
  have hinit : E.production.initialEnv =
      ves.venv (if isUnsafe then .unsafe else .safe) := E.production_initialEnv
  have hsourceUvars : sourceDecl.uvars = E.production.c.lparams.length := by
    have h := E.nativeSource.core.uvars
    rw [E.nativeSourceDecl_eq] at h
    rw [h, E.production_c, E.productionContext_lparams]
  have hloweredUvars : E.production.loweredDecl.uvars = sourceDecl.uvars :=
    E.production.constructors.core.uvars.trans hsourceUvars.symm
  refine ⟨?_, ?_, ?_⟩
  · have h := B.sourceSignature_models
    generalize B.sourceSignature = sL at h ⊢
    rwa [hinit] at h
  · have Hctx := B.params_scope
    rw [hBscope, ConstructorPhasesResult.completed_parameterScope_toCtx] at Hctx
    have hp : B.sourceSignature.params = B.params := B.sourceSignatureHeader_params
    rw [hp]
    generalize B.params = P at Hctx ⊢
    generalize E.production.headers.commonParameterContext = Q at Hctx ⊢
    rw [hinit, hloweredUvars] at Hctx
    exact VEnv.IsDefEqCtx.mono (VEnv.addConstVals_le hadded) Hctx
  · obtain ⟨-, -, -, -, hfreshSrc, hreserved, -, -⟩ := E.auxHeadsFacts wf Hsources
    have hfresh : ∀ name ∈ E.auxHeads, E.production.initialEnv.constants name = none := by
      rw [hinit]; exact hfreshSrc
    have hN := B.sourceSignature_headsApplied (E.constructorTypesHitShape wf Hsources)
      (fun l => avoidsConsts_lit_of_reserved hreserved l) (B.params_avoid hloweredNe hfresh)
    have Hsource := E.nativeSource.core
    rw [E.nativeSourceDecl_eq] at Hsource
    have hnp : E.production.stats.params.size = sourceDecl.nparams := by
      obtain ⟨_, Hrun, _, _⟩ := E.lowering
      rw [E.statsParamsSize, Hrun.resultNParams, Hsource.nparams]
    have hlv : E.production.stats.levels.length = sourceDecl.uvars := by
      rw [E.statsLevels, List.length_map, Hsource.uvars]
    have hheads : ∀ h ∈ (compilationRestoration sourceDecl auxiliaries).heads,
        h.auxiliary ∈ E.auxHeads ∧ h.uvars = sourceDecl.uvars ∧
          h.nparams = sourceDecl.nparams := by
      intro h hh
      obtain ⟨a, ha, hh⟩ := List.mem_flatMap.1 hh
      obtain ⟨hu, hn, -, -⟩ := ContainerSpecialization.mem_heads hh
      refine ⟨?_, hu, hn⟩
      show h.auxiliary ∈ familyNames _
      rw [← hheadNames]
      refine List.mem_flatMap.2 ⟨a, ha, ?_⟩
      rw [← ContainerSpecialization.heads_map_auxiliary a sourceDecl.uvars sourceDecl.nparams]
      exact List.mem_map_of_mem hh
    intro normalized hn ctor hc
    have hA := hN normalized hn ctor hc
    rw [hnp, hlv] at hA
    exact hA.restorationExpr _ hheads

private theorem forall₂_append_left_split' {R : α → β → Prop}
    {l₁ l₂ : List α} {r : List β} (H : List.Forall₂ R (l₁ ++ l₂) r) :
    List.Forall₂ R l₁ (r.take l₁.length) ∧
      List.Forall₂ R l₂ (r.drop l₁.length) := by
  have h₁ := forall₂_take' H l₁.length
  have h₂ := forall₂_drop' H l₁.length
  simp only [List.take_left', List.drop_left'] at h₁ h₂
  exact ⟨h₁, h₂⟩

private theorem forall₂_of_map_eq' {f : α → γ} {g : β → γ} :
    ∀ {l : List α} {r : List β}, l.map f = r.map g →
      List.Forall₂ (fun a b => f a = g b) l r
  | [], [], _ => .nil
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | _ :: _, _ :: _, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    exact .cons h.1 (forall₂_of_map_eq' h.2)

private theorem forall₂_swap' {R : α → β → Prop} :
    ∀ {l : List α} {r : List β}, List.Forall₂ R l r →
      List.Forall₂ (fun b a => R a b) r l
  | _, _, .nil => .nil
  | _, _, .cons h t => .cons h (forall₂_swap' t)

private theorem forall₂_join' {R : α → β → Prop} {S : γ → β → Prop} :
    ∀ {l : List α} {m : List β} {n : List γ}, List.Forall₂ R l m →
      List.Forall₂ S n m → List.Forall₂ (fun a c => ∃ b, R a b ∧ S c b) l n
  | _, _, _, .nil, .nil => .nil
  | _, _, _, .cons h t, .cons h' t' => .cons ⟨_, h, h'⟩ (forall₂_join' t t')

/-- Basic facts about the source and lowered declarations of a validated nested run. -/
theorem NestedValidatedRunResult.sourceLoweredBasics
    {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}
    (E : NestedValidatedRunResult result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv) :
    sourceDecl.types ≠ [] ∧ E.production.loweredDecl.types ≠ [] ∧
      sourceDecl.typeConstants =
        E.production.loweredDecl.typeConstants.take sourceDecl.types.length ∧
      E.production.loweredDecl.uvars = sourceDecl.uvars ∧
      E.production.loweredDecl.nparams = sourceDecl.nparams ∧
      sourceDecl.SourceWF (ves.venv (if isUnsafe then .unsafe else .safe)) ∧
      (ves.venv (if isUnsafe then .unsafe else .safe)).addConstVals
        E.production.loweredDecl.typeConstants =
          some E.production.constructors.completed.headerVEnv := by
  have hinit : E.production.initialEnv =
      ves.venv (if isUnsafe then .unsafe else .safe) := E.production_initialEnv
  have Hsource := E.nativeSource.core
  rw [E.nativeSourceDecl_eq] at Hsource
  have hsourceLength : sourceDecl.types.length = sourceTypes.length :=
    (TrInductDeclCore.types_length Hsource).symm
  have hsourceNonempty : sourceDecl.types ≠ [] := by
    have hnonempty : sourceTypes ≠ [] := by
      rcases E.lowering with ⟨_finalState, Hrun, _Hcache, _Hparams⟩
      rcases Hrun.source with
        ⟨first, tail, _tail, _paramsState, _lctx, _params, hsource, _⟩
      rw [hsource]
      simp
    intro h
    apply hnonempty
    rw [← List.length_eq_zero_iff, ← hsourceLength, h]
    rfl
  have hprefix : sourceDecl.typeConstants =
      E.production.loweredDecl.typeConstants.take sourceDecl.types.length := by
    have h := E.nativeSource.sourceTypeValues
    rw [E.nativeSourceDecl_eq] at h
    rw [h, VInductDecl.typeConstants, List.map_take, hsourceLength]
  have hsourceUvars : sourceDecl.uvars = E.production.c.lparams.length := by
    have h := E.nativeSource.core.uvars
    rw [E.nativeSourceDecl_eq] at h
    rw [h, E.production_c, E.productionContext_lparams]
  refine ⟨hsourceNonempty, ?_, hprefix,
    E.production.constructors.core.uvars.trans hsourceUvars.symm, ?_,
    TrInductDeclCore.sourceWF_ofNonempty Hsource hsourceNonempty, ?_⟩
  · intro h
    apply hsourceNonempty
    have : sourceDecl.typeConstants = [] := by
      rw [hprefix, VInductDecl.typeConstants, h]; simp
    simpa [VInductDecl.typeConstants] using this
  · have h := E.nativeSource.core.nparams
    rw [E.nativeSourceDecl_eq] at h
    rw [h, E.production.constructors.core.nparams, E.production_nparams]
  · exact Eq.mp (congrArg (fun env : VEnv => env.addConstVals
        E.production.loweredDecl.typeConstants =
          some E.production.constructors.completed.headerVEnv) hinit)
      E.production.constructors.completed.core.typesAdded

/-- **The case part of the nested compilation for the boundary signature of the lowered
declaration**, with the restoration of the nested compilation's specializations. -/
theorem NestedValidatedRunResult.boundaryCaseCompilationData
    {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}
    (E : NestedValidatedRunResult result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (wf : ves.WFCore sourceProdEnv) (Hsources : SourceSyntaxChecks sourceTypes)
    (Hformation : NestedFormationAssembly (ves.venv (if isUnsafe then .unsafe else .safe))
      sourceDecl)
    (hformationExpanded : Hformation.expanded = E.production.loweredDecl)
    (B : ConstructorBoundary E.production.c E.production.stats E.production.loweredDecl
      E.production.nparams E.production.isUnsafe E.production.depth E.production.initialEnv
      E.production.indTypes)
    (hBscope : B.parameterScope = E.production.constructors.completed.parameterScope)
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
    (D : RestorationTableData sourceDecl auxiliaries result E.loweredEnv
      (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 lparams)
    (Hrestoring : List.Forall₂ (fun source lowered : VInductiveType => List.Forall₂
          (fun sc lc : VConstVal => VExpr.NestedExprExpansion
            ((compilationRestoration sourceDecl auxiliaries).RestoringLeaf
              (VLevel.params sourceDecl.uvars)) 0 sc.type lc.type)
          source.ctors lowered.ctors)
        sourceDecl.types (E.production.loweredDecl.types.take sourceDecl.types.length))
    (HauxRestoring : List.Forall₂ (VInductDecl.NestedTypeExpansion
        (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl
        ((compilationRestoration sourceDecl auxiliaries).RestoringLeaf
          (VLevel.params sourceDecl.uvars)))
      generated (E.production.loweredDecl.types.drop sourceDecl.types.length))
    (es : List (Name × CaseSchema)) :
    CaseCompilationData (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl
      E.production.loweredDecl B.sourceSignature auxiliaries (sourceDecl.caseBlock es) := by
  let r := compilationRestoration sourceDecl auxiliaries
  have hinit : E.production.initialEnv =
      ves.venv (if isUnsafe then .unsafe else .safe) := E.production_initialEnv
  have hnodup :
      (familyNames E.production.loweredDecl.types ++
        E.production.loweredDecl.types.map (fun t => t.name.str "rec")).Nodup := by
    rcases E.containerSpecializations wf Hsources with
      ⟨_, _, _, _, _, _, _, h, _⟩
    exact h
  have hfreshAll := E.restorableNames_fresh hadded Haux Hexpansion hnodup
  have hfresh : ∀ name ∈ r.heads.map (·.auxiliary), envTypes.constants name = none :=
    fun name hname => hfreshAll name (List.mem_append_left _ hname)
  have hrecFresh : ∀ p ∈ r.recursors, envTypes.constants p.1 = none :=
    fun p hp => hfreshAll p.1 (List.mem_append_right _ (List.mem_map_of_mem hp))
  have hheadNames := auxiliarySpecializations_headNames Haux Hexpansion
  obtain ⟨hsourceNonempty, hloweredNe, hprefix, hloweredUvars, hloweredNparams, HsourceWF,
    hloweredTypes⟩ := E.sourceLoweredBasics
  obtain ⟨HmodelsL, hPL, htotal⟩ :=
    E.boundarySignatureFacts wf Hsources B hBscope hadded hheadNames hloweredNe
  obtain ⟨-, -, hnames, -, -, hwellFormedAll, -, hscoped, hdirect, -⟩ :=
    E.restorationPrefix_of wf hadded henvTypes Haux Hexpansion hnodup D True.intro
  -- the restoration substitution and the lowered defeqs of the boundary constructors
  obtain ⟨ρ, S, -⟩ := E.constructorRestorationSubstitution wf hadded henvTypes Haux Hexpansion
    hnodup hfresh hrecFresh
  obtain ⟨envT, henvT, Hctors⟩ := HmodelsL.constructors
  rw [hloweredTypes] at henvT
  cases henvT
  have Hlengths : List.Forall₂ (fun a b : VInductiveType => a.ctors.length = b.ctors.length)
      B.sourceSignature.declaration.types E.production.loweredDecl.types :=
    Lean4Lean.List.Forall₂.imp (fun _ _ h => by
      simpa using congrArg List.length h.2.2.2.2) HmodelsL.families
  have Hdefeq := forall₂_ctors_split (R := fun nc lc : VConstVal =>
      E.production.constructors.completed.headerVEnv.IsDefEqU sourceDecl.uvars []
        nc.type lc.type) Hlengths
    (Lean4Lean.List.Forall₂.imp (fun _ _ h => by
      rw [hloweredUvars] at h
      exact h.2.2) Hctors)
  have hlevels := E.loweredConstructorLevels_heads wf Hsources hheadNames
  have HsrcRestore := sourceConstructors_of_substitution S henvTypes.betaSubjectReduction
    (forall₂_take' Hdefeq sourceDecl.types.length)
    (E.loweredConstructors_of_evidence hadded henvTypes hfreshAll Hrestoring hlevels)
    (fun n hn => htotal n (List.mem_of_mem_take hn))
  have hlevelsAux : ∀ t ∈ E.production.loweredDecl.types.drop sourceDecl.types.length,
      ∀ lc ∈ t.ctors, lc.type.ConstLevelsAt (r.heads.map (·.auxiliary))
        (VLevel.params sourceDecl.uvars) := by
    have h := E.loweredAuxiliaryConstructorLevels wf Hsources
    rwa [← auxiliarySpecializations_headNames Haux Hexpansion,
      ← compilationRestoration_heads_auxiliary] at h
  have HauxRestore : ∀ direct,
      auxiliaries.mapM (fun a => a.directFamily sourceDecl.uvars B.sourceSignature.params) =
        some direct →
      List.Forall₂ (fun normalized family : VInductiveType =>
          List.Forall₂ (fun normalized ctor : VConstVal =>
            RestoresType r envTypes sourceDecl.uvars normalized.type ctor.type)
            normalized.ctors family.ctors)
        (B.sourceSignature.declaration.types.drop sourceDecl.types.length) direct :=
    fun direct hmapM => sourceConstructors_of_substitution S henvTypes.betaSubjectReduction
      (forall₂_drop' Hdefeq sourceDecl.types.length)
      (auxiliaryLoweredConstructors_restore henvTypes Haux HauxRestoring hPL hfreshAll
        hlevelsAux hmapM)
      (fun n hn => htotal n (List.mem_of_mem_drop hn))
  have hsourceUvars : sourceDecl.uvars = E.production.c.lparams.length := by
    have h := E.nativeSource.core.uvars
    rw [E.nativeSourceDecl_eq] at h
    rw [h, E.production_c, E.productionContext_lparams]
  have HauxFamilies : ∀ direct,
      auxiliaries.mapM (fun a => a.directFamily sourceDecl.uvars B.sourceSignature.params) =
        some direct →
      List.Forall₂ (fun normalized family : VInductiveType =>
          normalized.numIndices = family.numIndices ∧
          normalized.resultLevel ≈ family.resultLevel ∧
          (∃ domains body level exprType, level ≈ normalized.resultLevel ∧
            envTypes.IsDefEq sourceDecl.uvars [] family.type
              (VExpr.wrapForalls domains body) exprType ∧
            envTypes.IsDefEq sourceDecl.uvars domains.reverse body (.sort level)
              (.sort (.succ level))) ∧
          List.Forall₂ (fun normalized ctor : VConstVal =>
            normalized.name = ctor.name ∧ normalized.uvars = ctor.uvars ∧
            RestoresType r envTypes sourceDecl.uvars normalized.type ctor.type)
            normalized.ctors family.ctors)
        (B.sourceSignature.declaration.types.drop sourceDecl.types.length) direct := by
    intro direct hmapM
    refine auxiliaryFamilies_of_evidence (base := ves.venv (if isUnsafe then .unsafe else .safe))
      (headerParams := E.production.headers.headers.params)
      henvTypes (VEnv.addConstVals_le hadded) Haux Hexpansion ?_ ?_ hloweredUvars
      hloweredNparams hPL ?_ hmapM (HauxRestore direct hmapM)
    · exact Lean4Lean.List.Forall₂.imp (fun _ _ h => ⟨h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩)
        (forall₂_drop' HmodelsL.families sourceDecl.types.length)
    · intro t ht
      have h := E.production.headers.headers.typeShapes t (List.mem_of_mem_drop ht)
      generalize E.production.headers.headers.params = hp at h ⊢
      rwa [hinit] at h
    · intro n hn c hc
      rw [B.sourceSignature.declaration_ctor_uvars n
        (List.mem_of_mem_drop hn) c hc, HmodelsL.uvars, hloweredUvars]
  refine {
    sourceWF := HsourceWF
    sourceParameters := Hformation.sourceParameters
    expandedWF := hformationExpanded ▸ Hformation.expandedSource
    headerPrefix := hprefix
    expandedFormation := hformationExpanded ▸ Hformation.expandedFormation
    model := HmodelsL
    uvars := hformationExpanded ▸ Hformation.uvars
    nparams := hformationExpanded ▸ Hformation.nparams
    safety := hformationExpanded ▸ Hformation.isUnsafe
    restorationScoped := hscoped
    correspondence := ?_
    familyTypesWF := ?_
    types := rfl
    ctors := rfl
    projections := rfl }
  · obtain ⟨direct, hmapM, hshapes⟩ := hdirect sourceDecl.uvars B.sourceSignature.params
    refine ⟨envTypes, direct, hadded, hmapM, hwellFormedAll _ hPL, ?_⟩
    have HT := Hformation.types
    rw [hformationExpanded] at HT
    obtain ⟨HTsource, -⟩ := forall₂_append_left_split' HT
    have HM := HmodelsL.families
    have hle := VEnv.addConstVals_le hadded
    have hsplit := List.take_append_drop sourceDecl.types.length
      B.sourceSignature.declaration.types
    rw [← hsplit]
    have hprefixLength :
        (B.sourceSignature.declaration.types.take sourceDecl.types.length).length =
          sourceDecl.types.length := by
      rw [Lean4Lean.List.Forall₂.length_eq (forall₂_take' HM sourceDecl.types.length)]
      exact (Lean4Lean.List.Forall₂.length_eq HTsource).symm
    refine (Lean4Lean.List.Forall₂.append_of_left hprefixLength).mpr ⟨?_, ?_⟩
    · have HMp := forall₂_take' HM sourceDecl.types.length
      obtain ⟨_, _, _, hheaders, _, _⟩ := Hformation.sourceParameters
      have H1 := forall₂_join' HMp HTsource
      refine Lean4Lean.List.Forall₂.imp ?_ (Lean4Lean.List.Forall₂.and_mem
        (Lean4Lean.List.Forall₂.and H1 HsrcRestore))
      rintro a src ⟨⟨⟨x, hM, hT⟩, hP⟩, ha, hsrc⟩
      have hres : a.resultLevel ≈ src.resultLevel := by
        rw [← hT.resultLevel]; exact hM.2.2.2.1
      obtain ⟨domains, body, exprType, _, htype, hbody⟩ := (hheaders src hsrc).header
      refine ⟨hM.1.trans hT.name, hM.2.1.trans hT.uvars,
        hM.2.2.1.trans hT.numIndices, hres,
        ⟨domains, body, src.resultLevel, exprType, hres.symm, htype.mono hle,
          hbody.mono hle⟩, ?_⟩
      have Hnames := Lean4Lean.List.Forall₂.trans
        (fun _ _ _ h1 h2 => h1.trans h2.name)
        (forall₂_of_map_eq' (f := VConstVal.name) (g := VConstVal.name) hM.2.2.2.2)
        (forall₂_swap' hT.constructors)
      refine Lean4Lean.List.Forall₂.imp ?_ (Lean4Lean.List.Forall₂.and_mem
        (Lean4Lean.List.Forall₂.and Hnames hP))
      rintro n c ⟨⟨hname, hRT⟩, hn, hc⟩
      refine ⟨hname, ?_, hRT⟩
      rw [B.sourceSignature.declaration_ctor_uvars a
        (List.mem_of_mem_take ha) n hn, HmodelsL.uvars, hloweredUvars,
        HsourceWF.2.2.2.1 c (List.mem_flatMap.mpr ⟨src, hsrc, hc⟩)]
    · have HMd := forall₂_drop' HM sourceDecl.types.length
      have HP := HauxFamilies direct hmapM
      have Hnames := forall₂_of_map_eq' (f := ContainerSpecialization.auxiliary)
        (g := fun t : VInductiveType => t.name) hnames
      have Hdirect := forall₂_join' (forall₂_swap' Hnames) (forall₂_swap' hshapes)
      have H1 := forall₂_join' HMd (forall₂_swap' Hdirect)
      refine Lean4Lean.List.Forall₂.imp ?_
        (Lean4Lean.List.Forall₂.and_mem (Lean4Lean.List.Forall₂.and H1 HP))
      rintro a d ⟨⟨⟨x, hM, aux, hname, hshape⟩, hP⟩, ha, _⟩
      refine ⟨hM.1.trans (hname.symm.trans hshape.name.symm), ?_, hP.1, hP.2.1,
        hP.2.2.1, hP.2.2.2⟩
      rw [B.sourceSignature.declaration_type_uvars a
        (List.mem_of_mem_drop ha), HmodelsL.uvars, hloweredUvars, hshape.uvars]
  · have hloweredCtors := E.production.constructors.completed.core.ctorsAdded
    have hBH : B.headerVEnv = E.production.constructors.completed.headerVEnv :=
      Option.some.inj (B.core.typesAdded.symm.trans
        E.production.constructors.completed.core.typesAdded)
    refine ⟨_, _, E.production.constructors.completed.eliminators, hloweredTypes,
      hloweredCtors, ?_, ?_⟩
    · have hown := E.production.constructors.completed.eliminatorsOrdinary.own
      generalize E.production.constructors.completed.eliminators = es at hown ⊢
      rw [hinit] at hown
      exact hown
    · have h := B.sourceSignature_familyTypesWF_header
      rw [hBH] at h
      exact h.mono (((VEnv.addConstVals_le hloweredCtors).trans VEnv.addEliminators_le).trans
        VEnv.addProjections_le)

/-- The recursor names reserved by the nested compilation restoration are the recursor names of
the lowered auxiliary families, fresh in the base environment and distinct from the source and
lowered declarations' names. -/
theorem NestedValidatedRunResult.restorationRecursorNames
    {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}
    (E : NestedValidatedRunResult result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (wf : ves.WFCore sourceProdEnv) (Hsources : SourceSyntaxChecks sourceTypes)
    (Hformation : NestedFormationAssembly (ves.venv (if isUnsafe then .unsafe else .safe))
      sourceDecl)
    (hformationExpanded : Hformation.expanded = E.production.loweredDecl)
    {envTypes : VEnv} {generated : List VInductiveType}
    {auxiliaries : List ContainerSpecialization}
    (hadded : (ves.venv (if isUnsafe then .unsafe else .safe)).addConstVals
      sourceDecl.typeConstants = some envTypes)
    (Haux : List.Forall₂ (AuxiliarySpecializationEvidence
      (ves.venv (if isUnsafe then .unsafe else .safe)) envTypes
      E.production.headers.commonParameterContext sourceDecl)
      auxiliaries generated)
    (Hexpansion : List.Forall₂ (VInductDecl.NestedTypeExpansion
        (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl
        (VInductDecl.NestedAuxiliarySourceAbsolute
          (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl generated))
      generated (E.production.loweredDecl.types.drop sourceDecl.types.length))
    (hnames : auxiliaries.map (·.auxiliary) =
      (E.production.loweredDecl.types.drop sourceDecl.types.length).map (·.name)) :
    RecursorNamesFresh (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl
        E.production.loweredDecl auxiliaries ∧
      ∀ n ∈ (compilationRestoration sourceDecl auxiliaries).recursors.map Prod.fst,
        n ∈ E.production.loweredDecl.types.map (fun t => t.name.str "rec") := by
  have hnodup :
      (familyNames E.production.loweredDecl.types ++
        E.production.loweredDecl.types.map (fun t => t.name.str "rec")).Nodup := by
    rcases E.containerSpecializations wf Hsources with
      ⟨_, _, _, _, _, _, _, h, _⟩
    exact h
  have hfreshAll := E.restorableNames_fresh hadded Haux Hexpansion hnodup
  have hrec : ∀ n ∈ (compilationRestoration sourceDecl auxiliaries).recursors.map Prod.fst,
      n ∈ E.production.loweredDecl.types.map (fun t => t.name.str "rec") := by
    intro n hn
    simp only [compilationRestoration, List.map_map, List.mem_map, Function.comp_def] at hn
    obtain ⟨⟨a, i⟩, hai, rfl⟩ := hn
    have ha : a.auxiliary ∈ auxiliaries.map (·.auxiliary) :=
      List.mem_map_of_mem (List.fst_mem_of_mem_zipIdx hai)
    rw [hnames] at ha
    obtain ⟨t, ht, hteq⟩ := List.mem_map.1 ha
    exact List.mem_map.2 ⟨t, List.mem_of_mem_drop ht, by simp [hteq]⟩
  have hdisj : ∀ n ∈ (compilationRestoration sourceDecl auxiliaries).recursors.map Prod.fst,
      n ∉ familyNames E.production.loweredDecl.types := fun n hn hf =>
    (List.nodup_append.mp hnodup).2.2 n hf n (hrec n hn) rfl
  have hloweredNames : ∀ n, n ∈ E.production.loweredDecl.sourceNames →
      n ∈ familyNames E.production.loweredDecl.types := by
    intro n hn
    apply (familyNames_perm E.production.loweredDecl.types).mem_iff.mpr
    simpa only [VInductDecl.sourceNames, VInductDecl.typeConstants,
      VInductDecl.constructorConstants, List.map_map, List.map_flatMap, Function.comp_def]
      using hn
  refine ⟨fun n hn => ⟨?_, fun hs => ?_, fun hl => hdisj n hn (hloweredNames n hl)⟩, hrec⟩
  · have h := hfreshAll n (List.mem_append_right _ hn)
    exact (VEnv.addConstVals_le hadded).constants_eq_none_left h
  · simp only [VInductDecl.sourceNames, List.mem_append, List.mem_map] at hs
    rcases hs with ⟨ci, hci, rfl⟩ | ⟨ci, hci, rfl⟩
    · have h := hfreshAll ci.name (List.mem_append_right _ hn)
      rw [VEnv.addConstVals_get hadded hci] at h
      cases h
    · have hc := Hformation.sourceConstructorNames hformationExpanded ci hci
      apply hdisj _ hn
      simp only [familyNames, List.mem_flatMap] at hc ⊢
      obtain ⟨t, ht, h⟩ := hc
      exact ⟨t, List.mem_of_mem_take ht, h⟩

private theorem AddConstants.entry_name_eq'
    {safety : DefinitionSafety} {env : Environment} {venv : VEnv}
    {entries : List (ConstantInfo × VConstVal)} {outEnv : Environment} {outVEnv : VEnv}
    (H : AddConstants safety env venv entries outEnv outVEnv) :
    ∀ entry ∈ entries, entry.1.name = entry.2.name := by
  induction H with
  | nil => intro _ h; cases h
  | cons _ _ htr _ _ _ _ ih =>
    intro entry hentry
    rcases List.mem_cons.1 hentry with rfl | h
    · exact htr.2
    · exact ih entry h

/-- **The recursor names of the lowered families are fresh in the source production
environment**: the lowered production installed them over an extension of it. -/
theorem NestedValidatedRunResult.loweredRecursorNames_fresh
    {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}
    (E : NestedValidatedRunResult result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (wf : ves.WFCore sourceProdEnv) :
    ∀ n ∈ E.production.loweredDecl.types.map (fun t => t.name.str "rec"),
      sourceProdEnv.find? n = none := by
  intro n hn
  obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hn
  have hinit : E.production.initialEnv =
      ves.venv (if isUnsafe then .unsafe else .safe) := E.production_initialEnv
  have Hmodels : E.production.compilationSignature.Models
      (ves.venv (if isUnsafe then .unsafe else .safe)) E.production.loweredDecl := by
    have h := E.production.loweredConstruction.consumedGeneration.models
    change E.production.compilationSignature.Models E.production.initialEnv
      E.production.loweredDecl at h
    rwa [hinit] at h
  -- the owner slot of `t`
  have hnames := familyHeaderNames_eq Hmodels.families (fun _ _ h => h.1)
  rw [declaration_familyNames] at hnames
  have htm : t.name ∈ E.production.compilationSignature.families.toList.map (·.name) := by
    rw [hnames]; exact List.mem_map_of_mem ht
  obtain ⟨family, hfamily, hfname⟩ := List.mem_map.1 htm
  obtain ⟨i, hi, hindex⟩ := List.mem_iff_getElem.1 hfamily
  have hi' : i < E.production.compilationSignature.families.size := by simpa using hi
  let owner : Fin E.production.compilationSignature.families.size := ⟨i, hi'⟩
  have hrname : (E.production.compilationInstance.recursor owner).name = t.name.str "rec" := by
    change E.production.compilationInstance.recursorName owner = _
    have hn := E.production.loweredConstruction.consumedGeneration.names owner
    change E.production.compilationInstance.recursorName owner =
      E.production.compilationSignature.families[owner].name.str "rec" at hn
    rw [hn]
    have : E.production.compilationSignature.families[owner].name = family.name := by
      simp only [Fin.getElem_fin, owner]
      rw [← hindex]; simp
    exact congrArg (·.str "rec") (this.trans hfname)
  have hmem : E.production.compilationInstance.recursor owner ∈
      E.production.compilationInstance.recursors :=
    List.mem_map.2 ⟨owner, List.mem_finRange owner, rfl⟩
  have hrecursorValues : E.production.production.entries.map Prod.snd =
      E.production.compilationInstance.recursors :=
    E.production.production.canonicalRecursors
  rw [← hrecursorValues] at hmem
  have Hinst := E.production.production.installed
  obtain ⟨info, hentry⟩ := Hinst.existsEntryOfValue hmem
  have hlocal : E.production.production.localContext.env = E.production.ctorEnv :=
    E.production.production.localExtends.env_eq
  have hwfLocal : E.production.production.localContext.env.constants.WF := by
    rw [hlocal]
    exact E.production.constructors.completed.context.checking.tr.map_wf
  have hfreshLocal := Hinst.entryFresh hwfLocal hentry
  have hname := AddConstants.entry_name_eq' Hinst _ hentry
  simp only at hname
  rw [hname, hrname, hlocal] at hfreshLocal
  cases hfind : sourceProdEnv.find? (t.name.str "rec") with
  | none => rfl
  | some ci =>
    have := E.ctorEnv_preserves wf hfind
    rw [hfreshLocal] at this
    cases this

/-- **The case eliminators of a validated nested run's source declaration are certified**, in
the source environment and in every larger environment in which the names fresh in the
production source environment are fresh. The source declaration registers the boundary
signature `sL` of the lowered declaration's case eliminator, under the same key, restored by the
nested compilation restoration of specializations `auxiliaries` identified with the restoration
tables of the run. -/
theorem NestedValidatedRunResult.caseEliminators
    {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}
    (E : NestedValidatedRunResult result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (wf : ves.WFCore sourceProdEnv) (Hsources : SourceSyntaxChecks sourceTypes)
    (_Howners : ConstructorOwnersPresent sourceProdEnv)
    (Hformation : NestedFormationAssembly (ves.venv (if isUnsafe then .unsafe else .safe))
      sourceDecl)
    (hformationExpanded : Hformation.expanded = E.production.loweredDecl) :
    ∃ es : List (Name × InductiveSignature.CaseSchema),
      VInductBlock.EliminatorsWF (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl
        (sourceDecl.caseBlock es) ∧
      (∀ env', ves.venv (if isUnsafe then .unsafe else .safe) ≤ env' →
        (∀ n, sourceProdEnv.constants.find? n = none → env'.constants n = none) →
        VInductBlock.EliminatorsReplay env' sourceDecl (sourceDecl.caseBlock es)) ∧
      ∃ (key : Name) (sL : InductiveSignature) (auxiliaries : List ContainerSpecialization),
        E.production.constructors.completed.eliminators =
          [(key, CaseSchema.ofCompilation E.production.loweredDecl sL [])] ∧
        es = [(key, CaseSchema.ofCompilation sourceDecl sL auxiliaries)] ∧
        ∃ (envTypes : VEnv) (generated : List VInductiveType),
          (ves.venv (if isUnsafe then .unsafe else .safe)).addConstVals
            sourceDecl.typeConstants = some envTypes ∧
          envTypes.WF ∧
          List.Forall₂ (AuxiliarySpecializationEvidence
            (ves.venv (if isUnsafe then .unsafe else .safe)) envTypes
            E.production.headers.commonParameterContext sourceDecl)
            auxiliaries generated ∧
          List.Forall₂ (VInductDecl.NestedTypeExpansion
              (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl
              (VInductDecl.NestedAuxiliarySourceAbsolute
                (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl generated))
            generated (E.production.loweredDecl.types.drop sourceDecl.types.length) ∧
          result.params.size = result.nparams ∧
          RestorationTableData sourceDecl auxiliaries result E.loweredEnv
            (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 lparams ∧
          List.Forall₂ (fun source lowered : VInductiveType => List.Forall₂
              (fun sc lc : VConstVal => VExpr.NestedExprExpansion
                ((compilationRestoration sourceDecl auxiliaries).RestoringLeaf
                  (VLevel.params sourceDecl.uvars)) 0 sc.type lc.type)
              source.ctors lowered.ctors)
            sourceDecl.types (E.production.loweredDecl.types.take sourceDecl.types.length) ∧
          List.Forall₂ (VInductDecl.NestedTypeExpansion
              (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl
              ((compilationRestoration sourceDecl auxiliaries).RestoringLeaf
                (VLevel.params sourceDecl.uvars)))
            generated (E.production.loweredDecl.types.drop sourceDecl.types.length) := by
  have hinit : E.production.initialEnv =
      ves.venv (if isUnsafe then .unsafe else .safe) := E.production_initialEnv
  obtain ⟨B, hBel, -, hBscope⟩ := E.production.constructors.completed.eliminatorsBoundary
  rcases E.restorationTablesRestoringAll wf Hsources with
    ⟨envTypes, generated, auxiliaries, hadded, henvTypes, Haux, Hexpansion,
      hparamsSize, D, Hrestoring, HauxRestoring⟩
  have hnodup :
      (familyNames E.production.loweredDecl.types ++
        E.production.loweredDecl.types.map (fun t => t.name.str "rec")).Nodup := by
    rcases E.containerSpecializations wf Hsources with
      ⟨_, _, _, _, _, _, _, h, _⟩
    exact h
  have hfreshAll := E.restorableNames_fresh hadded Haux Hexpansion hnodup
  have hheadNames := auxiliarySpecializations_headNames Haux Hexpansion
  obtain ⟨-, -, hnames, -, hcertified, hwellFormedAll, -, -, -, -⟩ :=
    E.restorationPrefix_of wf hadded henvTypes Haux Hexpansion hnodup D True.intro
  obtain ⟨hsourceNonempty, hloweredNe, hprefix, hloweredUvars, -, HsourceWF,
    hloweredTypes⟩ := E.sourceLoweredBasics
  obtain ⟨-, hPL, -⟩ :=
    E.boundarySignatureFacts wf Hsources B hBscope hadded hheadNames hloweredNe
  obtain ⟨hrecFresh, hrecNames⟩ := E.restorationRecursorNames wf Hsources Hformation
    hformationExpanded hadded Haux Hexpansion hnames
  have Hdata := E.boundaryCaseCompilationData wf Hsources Hformation hformationExpanded B
    hBscope hadded henvTypes Haux Hexpansion D Hrestoring HauxRestoring
  let σ := CaseSchema.ofCompilation sourceDecl B.sourceSignature auxiliaries
  -- the key
  have hkey : sourceDecl.types.head?.map (·.name) = some B.caseKey := by
    cases hs : sourceDecl.types with
    | nil => exact absurd hs hsourceNonempty
    | cons s0 srest =>
      cases hl : E.production.loweredDecl.types with
      | nil => exact absurd hl hloweredNe
      | cons l0 lrest =>
        have h := hprefix
        simp only [VInductDecl.typeConstants, hs, hl, List.length_cons, List.map_cons,
          List.take_succ_cons, List.cons.injEq] at h
        simp only [ConstructorBoundary.caseKey, hl, List.head?_cons, Option.map_some,
          Option.getD_some]
        exact congrArg (some ·) (congrArg VConstVal.name h.1)
  have hBcase : B.caseEliminators =
      [(B.caseKey, CaseSchema.ofCompilation E.production.loweredDecl B.sourceSignature [])] := by
    simp [ConstructorBoundary.caseEliminators, hloweredNe, ConstructorBoundary.caseSchema]
  -- the source declaration's families and constructors
  obtain ⟨-, -, -, -, T0, C0, hT0, hC0, -, -⟩ := HsourceWF
  have hle0 : ves.venv (if isUnsafe then .unsafe else .safe) ≤ C0 :=
    (VEnv.addConstVals_le hT0).trans (VEnv.addConstVals_le hC0)
  -- projection names
  have hprojs : σ.ProjNamesRegistered C0 B.caseKey := by
    have hok : ∀ {e : VExpr},
        e.ProjNamesOK (fun S => ∃ info, E.production.initialEnv.projections S info) →
        e.ProjNamesOK (fun S => ∃ info, C0.projections S info) := by
      intro e h
      refine h.mono ?_
      rintro S ⟨info, hi⟩
      rw [hinit] at hi
      exact ⟨info, hle0.projections hi⟩
    obtain ⟨hp1, hp2, hp3, hp4⟩ := B.sourceSignature_pieces_projNamesOK hloweredNe
    have hheadsArgs : ∀ h ∈ σ.restoration.heads, ∀ a ∈ h.arguments,
        a.ProjNamesOK (fun S => ∃ info, C0.projections S info) := by
      intro h hh arg harg
      obtain ⟨a, ha, hh⟩ := List.mem_flatMap.1 hh
      obtain ⟨-, -, -, hargs⟩ := ContainerSpecialization.mem_heads hh
      rw [hargs] at harg
      obtain ⟨-, -, -, -, -, T, hT⟩ := hwellFormedAll _ hPL a ha
      have hok' := (VEnv.IsDefEq.projNamesOK henvTypes.ordered hPL.isType hT).1
      have harg' := (VExpr.ProjNamesOK.mkApps_inv hok').2 arg harg
      refine harg'.mono ?_
      rintro S ⟨info, hi⟩
      rw [VEnv.addConstVals_projections hadded] at hi
      exact ⟨info, hle0.projections hi⟩
    exact CaseSchema.projNamesOK_of_pieces_restored hheadsArgs
      (fun e he => hok (hp1 e he)) (fun f hf e he => hok (hp2 f hf e he))
      (fun c hc e he => hok (hp3 c hc e he)) (fun c hc e he => hok (hp4 c hc e he)) B.caseKey
  -- header agreement
  have hhdr : σ.HeaderAgreement (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl := by
    have hfreshInit : ∀ name ∈ σ.restoration.restorableNames,
        E.production.initialEnv.constants name = none := by
      intro name hname
      rw [hinit]
      exact (VEnv.addConstVals_le hadded).constants_eq_none_left (hfreshAll name hname)
    have hsourceTypes : E.production.initialEnv.addConstVals sourceDecl.typeConstants =
        some envTypes := by rw [hinit]; exact hadded
    have h := B.restored_headerAgreement hloweredNe (schema := σ) rfl hfreshInit hprefix
      hloweredUvars hsourceTypes
    generalize σ = σ' at h ⊢
    rwa [hinit] at h
  have hcert : σ.Certified (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl
      (sourceDecl.caseBlock [(B.caseKey, σ)]) :=
    CaseSchema.ofCaseCompilation_certified (Hdata _) hcertified hrecFresh
  refine ⟨[(B.caseKey, σ)], ⟨T0, C0, hT0, hC0, .inr ⟨B.caseKey, σ, rfl, hcert, hkey,
    hprojs, hhdr⟩⟩, ?_, B.caseKey, B.sourceSignature, auxiliaries, hBel.trans hBcase, rfl,
    envTypes, generated, hadded, henvTypes, Haux, Hexpansion, hparamsSize, D, Hrestoring,
    HauxRestoring⟩
  -- replay
  intro env' hle hfresh' T' C' hT' hC'
  have hwfP : sourceProdEnv.constants.WF := (wf.tr (safety := .unsafe)).map_wf
  have hfreshK : ∀ n, sourceProdEnv.find? n = none → env'.constants n = none := by
    intro n hn
    apply hfresh'
    rwa [Lean.Kernel.Environment.find?, hwfP.find?'_eq_find?] at hn
  -- the lowered declaration installs in `env'`
  have hloweredCtors := E.production.constructors.completed.core.ctorsAdded
  have hlowered := VEnv.addConstVals_append hloweredTypes hloweredCtors
  have hLnodup := VEnv.addConstVals_names_nodup hlowered
  have hLfresh : ∀ ci ∈ E.production.loweredDecl.typeConstants ++
      E.production.loweredDecl.constructorConstants, env'.constants ci.name = none := by
    intro ci hci
    apply hfreshK
    have hwfC : E.production.c.env.constants.WF := by
      rw [E.productionEnv]; exact hwfP
    have h := E.production.fresh_familyNames hwfC (n := ci.name) (by
      apply (familyNames_perm E.production.loweredDecl.types).mem_iff.mpr
      have : ci.name ∈ E.production.loweredDecl.sourceNames := by
        simp only [VInductDecl.sourceNames, ← List.map_append]
        exact List.mem_map_of_mem hci
      simpa only [VInductDecl.sourceNames, VInductDecl.typeConstants,
        VInductDecl.constructorConstants, List.map_map, List.map_flatMap, Function.comp_def]
        using this)
    rwa [E.productionEnv] at h
  obtain ⟨LC', hLC'⟩ := VEnv.addConstVals_exists_of_fresh hLnodup hLfresh
  obtain ⟨LT', hLT', hLCT'⟩ := VEnv.addConstVals_append_inv hLC'
  have Hdata' := (Hdata [(B.caseKey, σ)]).mono hle hT' hC' hLT' hLCT'
  have hrecFresh' := hrecFresh.mono (env' := env') (fun n hn =>
    hfreshK n (E.loweredRecursorNames_fresh wf n (hrecNames n hn)))
  have hC0le : C0 ≤ C' :=
    VEnv.addConstVals_mono (VEnv.addConstVals_mono hle hT0 hT') hC0 hC'
  exact ⟨T', C', hT', hC', .inr ⟨B.caseKey, σ, rfl,
    CaseSchema.ofCaseCompilation_certified Hdata' (hcertified.mono hle) hrecFresh', hkey,
    hprojs.mono hC0le, hhdr.mono hle hT'⟩⟩

end Lean4Lean.VerifyInductive
