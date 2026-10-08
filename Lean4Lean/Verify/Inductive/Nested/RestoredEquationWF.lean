import Lean4Lean.Theory.Inductive.ProjNamesAvoid
import Lean4Lean.Verify.Inductive.Nested.RuleShape
import Lean4Lean.Verify.Inductive.Nested.RecursorProvenance
import Lean4Lean.Verify.Inductive.Nested.AuxiliaryConstructorRestoration
import Lean4Lean.Verify.Inductive.CompletedRuleTranslation
import Lean4Lean.Theory.Inductive.RestorationRenamingOnCtx
import Lean4Lean.Theory.Inductive.BetaSubjectReduction
import Lean4Lean.Verify.Inductive.Nested.RestoredEliminatorFacts

/-! The restored-equation well-formedness hypothesis `HrestoredWF` of
`NestedValidatedRunResult.hruleShape_of` (`Nested/RuleShape.lean`).

Route. Every generated equation of the lowered production is well formed in
the lowered recursor environment (`loweredEquationWF`, from
`CompletedRecursorPhasesResult.equationsWF` and `ruleRhsTranslations`). A
context-carrying renaming restoration substitution
(`Theory/Inductive/RestorationRenamingOnCtx.lean`) from that environment into
the final abstract environment `C.finalBaseVEnv` transports the typing of both
sides to the restored equation (`Restoration.equation_wf_onCtx`), using beta
subject reduction of the well-formed final environment. The substitution
transports the projection rules only in well-formed image contexts
(`VEnv.ProjectionTransportOnCtx`); the equations are stated in the empty
context, so every transported derivation starts in a well-formed context. The substitution
replaces each restoration head (auxiliary family or constructor) by its
restoration lambda `λ params, target levels args`
(`Restoration.lambdaReplacement`) and renames every other constant and every
projection type name by `Restoration.renaming` (auxiliary recursors to their
restored names, auxiliary families in projection position to their
containers). It is built in stages:

* `headerRenamingReplacement`: the lowered header environment (base
  constants and source headers kept, auxiliary headers replaced);
* `constructorRenamingReplacement`: the lowered constructors (source
  constructors kept under their own name with the source constructor type,
  which is definitionally equal to the replaced lowered type by restoration
  at the header stage; auxiliary constructors replaced) and the lowered
  projections;
* `RenamingReplacement.ofAddConstants_recursors`: the lowered recursors,
  kept under their restored names with the restored recursor types, which are
  definitionally equal to the replaced lowered types by restoration at the
  previous stage.

`NestedRestoredEquationGaps` collects the facts the substitution is built
from, proved for the run in later modules (`Nested/RestoredEquationProjNames.lean`,
`Nested/RestoredEquationContainers.lean`,
`Nested/AuxiliaryProjectionTransport.lean`, where
`NestedValidatedRunResult.restoredEquationGaps` and the hypothesis-free
`NestedValidatedRunResult.hrestoredWF_of` are assembled): projection-name
avoidance of the base eliminator schemas, of the lowered
constructor types, of the generated recursor types and of the generated
equations (restoration keeps projection type names, so a projection of an
auxiliary family in a generated equation would make the restored equation
ill-typed); the typing of the restoration lambdas of the auxiliary
constructors at the restored lowered constructor types; and the transport of
the projection rules of the lowered declaration's projections in well-formed
contexts (including those of auxiliary structure-like families, renamed to
their containers).
-/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open InductiveSignature

namespace VExpr

theorem projNamesAvoid_of_containsAnyConst {names : List Name} :
    ∀ {e : VExpr}, e.containsAnyConst names = false → e.projNamesAvoid names = true
  | .bvar _, _ | .sort _, _ | .elim .., _ | .const .., _ => rfl
  | .app f a, h | .lam f a, h | .forallE f a, h => by
    simp only [containsAnyConst, Bool.or_eq_false_iff] at h
    simp [projNamesAvoid, projNamesAvoid_of_containsAnyConst h.1,
      projNamesAvoid_of_containsAnyConst h.2]
  | .proj n i e, h => by
    simp only [containsAnyConst, Bool.or_eq_false_iff] at h
    simp only [projNamesAvoid, Bool.and_eq_true, Bool.not_eq_true']
    exact ⟨h.1, projNamesAvoid_of_containsAnyConst h.2⟩

end VExpr

namespace InductiveSignature

/-- The renaming of a restoration: heads are renamed to their targets (this
only matters for projection type names), every other name by the recursor
renaming. -/
def Restoration.renaming (r : Restoration) (n : Name) : Name :=
  match r.heads.find? (fun h => h.auxiliary == n) with
  | some h => h.target
  | none => r.recursorName n

theorem Restoration.renaming_of_find_none {r : Restoration} {n : Name}
    (h : r.heads.find? (fun h => h.auxiliary == n) = none) :
    r.renaming n = r.recursorName n := by
  simp [Restoration.renaming, h]

theorem Restoration.find?_none_of_not_mem {r : Restoration} {n : Name}
    (h : n ∉ r.heads.map (·.auxiliary)) :
    r.heads.find? (fun h => h.auxiliary == n) = none := by
  apply List.find?_eq_none.mpr
  intro head hmem heq
  exact h (List.mem_map.mpr ⟨head, hmem, by simpa using heq⟩)

theorem Restoration.renaming_eq_self {r : Restoration} {n : Name}
    (h : n ∉ r.restorableNames) : r.renaming n = n := by
  have h1 : n ∉ r.heads.map (·.auxiliary) := fun hm => h (List.mem_append_left _ hm)
  have h2 : n ∉ r.recursors.map Prod.fst := fun hm => h (List.mem_append_right _ hm)
  rw [Restoration.renaming_of_find_none (Restoration.find?_none_of_not_mem h1),
    Restoration.recursorName_of_not_mem h2]

theorem Restoration.lambdaReplacement_eq_none_of_not_restorable {r : Restoration}
    {domains : HeadSpecialization → List VExpr} {n : Name}
    (h : n ∉ r.restorableNames) : r.lambdaReplacement domains n = none :=
  Restoration.lambdaReplacement_eq_none fun hm => h (List.mem_append_left _ hm)

theorem Restoration.replaceRen_eq_self {r : Restoration}
    {domains : HeadSpecialization → List VExpr} {e : VExpr}
    (h : e.containsAnyConst r.restorableNames = false) :
    e.replaceRen (r.lambdaReplacement domains) r.renaming = e :=
  VExpr.replaceRen_eq_self (fun _ hc => Restoration.lambdaReplacement_eq_none_of_not_restorable hc)
    (fun _ hc => Restoration.renaming_eq_self hc) h

theorem Restoration.replaceRen_eq_self_of_mentions {r : Restoration}
    {domains : HeadSpecialization → List VExpr} :
    ∀ {e : VExpr}, e.mentionsAnyConst r.restorableNames = false →
      e.projNamesAvoid r.restorableNames = true →
      e.replaceRen (r.lambdaReplacement domains) r.renaming = e
  | .bvar _, _, _ | .sort _, _, _ | .elim .., _, _ => rfl
  | .const c ls, h, _ => by
    have hc : c ∉ r.restorableNames := by simpa [VExpr.mentionsAnyConst] using h
    rw [VExpr.replaceRen_const_none (Restoration.lambdaReplacement_eq_none_of_not_restorable hc),
      Restoration.renaming_eq_self hc]
  | .app f a, h, h' | .lam f a, h, h' | .forallE f a, h, h' => by
    simp only [VExpr.mentionsAnyConst, Bool.or_eq_false_iff] at h
    simp only [VExpr.projNamesAvoid, Bool.and_eq_true] at h'
    simp only [VExpr.replaceRen, replaceRen_eq_self_of_mentions h.1 h'.1,
      replaceRen_eq_self_of_mentions h.2 h'.2]
  | .proj n i e, h, h' => by
    simp only [VExpr.mentionsAnyConst] at h
    simp only [VExpr.projNamesAvoid, Bool.and_eq_true, Bool.not_eq_true'] at h'
    have hn : n ∉ r.restorableNames := by simpa using h'.1
    simp only [VExpr.replaceRen, replaceRen_eq_self_of_mentions h h'.2,
      Restoration.renaming_eq_self hn]

theorem Restoration.projNamesFixed_of_avoid {r : Restoration} :
    ∀ {e : VExpr}, e.projNamesAvoid r.restorableNames = true → e.ProjNamesFixed r.renaming
  | .bvar _, _ | .sort _, _ | .elim .., _ | .const .., _ => trivial
  | .app f a, h | .lam f a, h | .forallE f a, h => by
    simp only [VExpr.projNamesAvoid, Bool.and_eq_true] at h
    exact ⟨projNamesFixed_of_avoid h.1, projNamesFixed_of_avoid h.2⟩
  | .proj n i e, h => by
    simp only [VExpr.projNamesAvoid, Bool.and_eq_true, Bool.not_eq_true'] at h
    exact ⟨Restoration.renaming_eq_self (by simpa using h.1), projNamesFixed_of_avoid h.2⟩

/-- The lambda replacement over a closed telescope is closed and not a Pi. -/
theorem Restoration.lambdaReplacement_closed {r : Restoration} {P : List VExpr}
    (hnparams : ∀ h ∈ r.heads, h.nparams = P.length)
    (hargs : ∀ h ∈ r.heads, ∀ arg ∈ h.arguments, arg.ClosedN h.nparams)
    (hPclosed : ∀ i (hi : i < P.length), P[i].ClosedN i) :
    VExpr.ReplacementsClosed (r.lambdaReplacement fun _ => P) := by
  intro c t hρ
  refine ⟨?_, Restoration.lambdaReplacement_ne_forallE r hρ⟩
  unfold Restoration.lambdaReplacement at hρ
  cases hf : r.heads.find? (fun h => h.auxiliary == c) with
  | none => simp [hf] at hρ
  | some h =>
    simp only [hf, Option.map_some, Option.some.injEq] at hρ
    subst hρ
    have hmem := List.mem_of_find?_eq_some hf
    refine VExpr.ClosedN.wrapLams_closed (n := 0) (by simpa using hPclosed) ?_
    refine VExpr.ClosedN.mkApps_closed trivial fun arg harg => ?_
    have := hargs h hmem arg harg
    rw [hnparams h hmem] at this
    simpa using this

/-- The lambda replacement and the restoration renaming agree with the
restoration (the agreement clauses of a `RestoredEliminator`). -/
theorem RenamingRestorationAgreement.of_lambda {r : Restoration} {P : List VExpr}
    (hnparams : ∀ h ∈ r.heads, h.nparams = P.length) :
    RenamingRestorationAgreement r (r.lambdaReplacement fun _ => P) r.renaming where
  shape := fun c t hρ =>
    Restoration.lambdaReplacement_shape r (fun h hmem => (hnparams h hmem).symm) hρ
  headsReplaced := fun c h hf => by
    simp [Restoration.lambdaReplacement, hf]
  renamed := fun c hf => Restoration.renaming_of_find_none hf

/-- A renaming replacement along the lambda replacement and the restoration
renaming is a renaming restoration substitution. -/
theorem RenamingRestorationSubstitution.of_lambda {envS envL : VEnv} {r : Restoration}
    {P : List VExpr}
    (S : VEnv.RenamingReplacement envS envL (r.lambdaReplacement fun _ => P) r.renaming)
    (hnparams : ∀ h ∈ r.heads, h.nparams = P.length) :
    RenamingRestorationSubstitution envS envL r (r.lambdaReplacement fun _ => P)
      r.renaming :=
  { S with
    shape := fun c t hρ =>
      Restoration.lambdaReplacement_shape r (fun h hmem => (hnparams h hmem).symm) hρ
    headsReplaced := fun c h hf => by
      simp [Restoration.lambdaReplacement, hf]
    renamed := fun c hf => Restoration.renaming_of_find_none hf }

/-- A context-carrying renaming replacement along the lambda replacement and
the restoration renaming is a context-carrying renaming restoration
substitution. -/
theorem RenamingRestorationSubstitutionOnCtx.of_lambda {envS envL : VEnv} {r : Restoration}
    {P : List VExpr}
    (S : VEnv.RenamingReplacementOnCtx envS envL (r.lambdaReplacement fun _ => P) r.renaming)
    (hnparams : ∀ h ∈ r.heads, h.nparams = P.length) :
    RenamingRestorationSubstitutionOnCtx envS envL r (r.lambdaReplacement fun _ => P)
      r.renaming :=
  { S with
    shape := fun c t hρ =>
      Restoration.lambdaReplacement_shape r (fun h hmem => (hnparams h hmem).symm) hρ
    headsReplaced := fun c h hf => by
      simp [Restoration.lambdaReplacement, hf]
    renamed := fun c hf => Restoration.renaming_of_find_none hf }

end InductiveSignature

namespace VerifyInductive

/-- Every generated equation of the lowered production is well formed in the
lowered recursor environment. -/
theorem NestedValidatedRunResult.loweredEquationWF
    {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceEnv : VEnv} {sourceDecl : VInductDecl} {lparams : List Name}
    {nparams : Nat} {isUnsafe : Bool} {safety : DefinitionSafety}
    {outEnv : Environment}
    (E : NestedValidatedRunResult result sourceProdEnv sourceTypes sourceEnv
      sourceDecl lparams nparams isUnsafe safety outEnv)
    (k : Fin E.production.production.generationSignature.constructors.size) :
    (E.production.production.canonicalGeneration.equation k).WF
      E.production.production.outVEnv := by
  have H := E.production.production.equationsWF
    (E.production.production.generatorBodyTranslations_of
      E.production.production.ruleRhsTranslations)
  exact H _ (by
    simp only [InductiveSignature.Instance.equations, List.mem_map, List.mem_finRange,
      true_and]
    exact ⟨k, rfl⟩)

private theorem nodup_map_inj_RE {f : α → β} :
    ∀ {l : List α}, (l.map f).Nodup → ∀ {x y}, x ∈ l → y ∈ l → f x = f y → x = y
  | [], _, _, _, hx, _, _ => by simp at hx
  | a :: l, hnd, x, y, hx, hy, hxy => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    rcases List.mem_cons.mp hx with hx' | hx' <;> rcases List.mem_cons.mp hy with hy' | hy'
    · exact hx'.trans hy'.symm
    · subst hx'; exact absurd ⟨y, hy', hxy.symm⟩ hnd.1
    · subst hy'; exact absurd ⟨x, hx', hxy⟩ hnd.1
    · exact nodup_map_inj_RE hnd.2 hx' hy' hxy

/-- The projection names of the registered eliminator schemas of the base
environment avoid the restorable names. Eliminator schemas are certified in
expanded environments whose projection tables may contain never-installed
auxiliary structure families (see `Nested.EliminatorAvoidance`), so this is
not a consequence of the formation certificate; it follows from the projection
names certified at registration (`NestedValidatedRunResult.eliminatorProjNames_of`). -/
def EliminatorProjNamesAvoid (env : VEnv) (names : List Name) : Prop :=
  ∀ block schema, env.eliminators block schema →
    (∀ owner type, schema.genericType owner = some type →
      type.projNamesAvoid names = true) ∧
    (∀ owner rules, schema.genericEquations block owner = some rules → ∀ df ∈ rules,
      df.lhs.projNamesAvoid names = true ∧ df.rhs.projNamesAvoid names = true ∧
      df.type.projNamesAvoid names = true)

/-- The setup shared by the stages: the lowered header environment splits as
the source headers followed by the auxiliary headers, and the auxiliary
headers are typed by their restoration lambdas in the source header
environment. -/
theorem NestedValidatedRunResult.headerSetup
    {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}
    (E : NestedValidatedRunResult result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (wf : ves.WFCore sourceProdEnv)
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
      E.production.loweredDecl.types.map (fun t => t.name.str "rec")).Nodup) :
    (ves.venv (if isUnsafe then .unsafe else .safe)).addConstVals
        (sourceDecl.typeConstants ++
          (E.production.loweredDecl.types.drop sourceDecl.types.length).map
            VInductiveType.toVConstVal) =
        some E.production.constructors.completed.headerVEnv ∧
      (compilationRestoration sourceDecl auxiliaries).heads.map (·.auxiliary) =
        familyNames (E.production.loweredDecl.types.drop sourceDecl.types.length) ∧
      (∀ h ∈ (compilationRestoration sourceDecl auxiliaries).heads,
        h.nparams = E.production.compilationSignature.params.length) ∧
      (∀ h ∈ (compilationRestoration sourceDecl auxiliaries).heads, ∀ arg ∈ h.arguments,
        arg.ClosedN h.nparams) ∧
      (∀ i (hi : i < E.production.compilationSignature.params.length),
        E.production.compilationSignature.params[i].ClosedN i) ∧
      (compilationRestoration sourceDecl auxiliaries).Scoped ∧
      (∀ h ∈ (compilationRestoration sourceDecl auxiliaries).heads, ∀ ci,
        E.production.constructors.completed.headerVEnv.constants h.auxiliary = some ci →
        ci.type.containsAnyConst
            (compilationRestoration sourceDecl auxiliaries).restorableNames = false ∧
        envTypes.HasType ci.uvars []
          (VExpr.wrapLams E.production.compilationSignature.params
            (VExpr.mkApps (.const h.target h.levels) h.arguments)) ci.type) := by
  have hfreshAll := E.restorableNames_fresh hadded Haux Hexpansion hnodup
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
  refine ⟨hloweredSplit, hheadNames, hheadsParams,
    fun h hh arg harg => (hscoped.2.2.1 h hh).2 arg harg, hPclosed, hscoped, ?_⟩
  intro h hh ci hci
  rcases lookup_of_addConstVals_append hadded hloweredSplit hci with
    henvT | ⟨entry, hentry, hn, hval⟩
  · rw [hfreshAll _ (List.mem_append_left _ (List.mem_map_of_mem hh))] at henvT; cases henvT
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hentry
  obtain ⟨a, ha, g, hev, hexp⟩ := hfamilyHead t ht
  have hfh : InductiveSignature.HeadSpecialization.mk a.auxiliary sourceDecl.uvars
      sourceDecl.nparams a.source.name a.levels a.arguments ∈
      (compilationRestoration sourceDecl auxiliaries).heads :=
    List.mem_flatMap.mpr ⟨a, ha, List.mem_cons_self⟩
  have heqh := nodup_map_inj_RE hscopedNodup hh hfh
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
  refine ⟨(htypeD.noFreshConsts hordered hfreshAll (by intro _ h; simp at h)).2.1, ?_⟩
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

/-- The head found for a name occurring among the head names. -/
theorem Restoration.find?_of_mem_heads {r : Restoration} {n : Name}
    (h : n ∈ r.heads.map (·.auxiliary)) :
    ∃ hd, r.heads.find? (fun h => h.auxiliary == n) = some hd ∧ hd ∈ r.heads ∧
      hd.auxiliary = n := by
  cases hf : r.heads.find? (fun h => h.auxiliary == n) with
  | none =>
    obtain ⟨hd, hmem, rfl⟩ := List.mem_map.mp h
    exact absurd (List.find?_eq_none.mp hf hd hmem) (by simp)
  | some hd =>
    exact ⟨hd, rfl, List.mem_of_find?_eq_some hf, by simpa using List.find?_some hf⟩

/-- **The header stage**: the renaming replacement from the lowered header
environment into any ordered environment containing the source header
environment. -/
theorem NestedValidatedRunResult.headerRenamingReplacement
    {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}
    (E : NestedValidatedRunResult result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (wf : ves.WFCore sourceProdEnv)
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
    {envT : VEnv} (hT : envT.Ordered) (hle : envTypes ≤ envT)
    (Helim : EliminatorProjNamesAvoid (ves.venv (if isUnsafe then .unsafe else .safe))
      (compilationRestoration sourceDecl auxiliaries).restorableNames) :
    VEnv.RenamingReplacement envT E.production.constructors.completed.headerVEnv
      ((compilationRestoration sourceDecl auxiliaries).lambdaReplacement
        fun _ => E.production.compilationSignature.params)
      (compilationRestoration sourceDecl auxiliaries).renaming := by
  obtain ⟨hsplit, hheadNames, hnp, hargs, hPclosed, -, hrepl⟩ :=
    E.headerSetup wf hadded henvTypes Haux Hexpansion hnodup
  have hfreshAll := E.restorableNames_fresh hadded Haux Hexpansion hnodup
  have hbase : (ves.venv (if isUnsafe then .unsafe else .safe)).WF := TrEnv'.wf wf.tr
  have hbaseLe := VEnv.addConstVals_le hadded
  have hbaseFresh : ∀ n ∈ (compilationRestoration sourceDecl auxiliaries).restorableNames,
      (ves.venv (if isUnsafe then .unsafe else .safe)).constants n = none :=
    fun n hn => hbaseLe.constants_eq_none_left (hfreshAll n hn)
  have hon := hbase.ordered.onTypes_noFreshConsts hbaseFresh
  have hnotR : ∀ {env : VEnv} {c ci},
      (∀ n ∈ (compilationRestoration sourceDecl auxiliaries).restorableNames,
        env.constants n = none) →
      env.constants c = some ci →
      c ∉ (compilationRestoration sourceDecl auxiliaries).restorableNames := by
    intro env c ci hf hc hmem
    rw [hf c hmem] at hc
    cases hc
  have hclosed := Restoration.lambdaReplacement_closed hnp hargs hPclosed
  have helimC := hbase.eliminatorsAvoidConsts hbaseFresh
  have S₀ : VEnv.RenamingReplacement envT (ves.venv (if isUnsafe then .unsafe else .safe))
      ((compilationRestoration sourceDecl auxiliaries).lambdaReplacement
        fun _ => E.production.compilationSignature.params)
      (compilationRestoration sourceDecl auxiliaries).renaming := by
    refine VEnv.RenamingReplacement.of_le hclosed hT hbase.ordered (hbaseLe.trans hle)
      ?_ ?_ ?_
    · intro c ci hc
      have hn := hnotR hbaseFresh hc
      obtain ⟨_, hty, -⟩ := hon.1 hc
      exact ⟨Restoration.lambdaReplacement_eq_none_of_not_restorable hn,
        Restoration.renaming_eq_self hn, Restoration.replaceRen_eq_self hty⟩
    · intro df hdf
      obtain ⟨⟨hl, ht⟩, hr, -⟩ := hon.2 hdf
      exact ⟨Restoration.replaceRen_eq_self hl, Restoration.replaceRen_eq_self hr,
        Restoration.replaceRen_eq_self ht⟩
    · intro block schema hs
      obtain ⟨hty, hrules⟩ := helimC block schema hs
      obtain ⟨hty', hrules'⟩ := Helim block schema hs
      refine ⟨fun owner type h =>
        Restoration.replaceRen_eq_self_of_mentions (hty owner type h) (hty' owner type h), ?_⟩
      intro owner rules h df hdf
      obtain ⟨a, b, c⟩ := hrules owner rules h df hdf
      obtain ⟨a', b', c'⟩ := hrules' owner rules h df hdf
      exact ⟨Restoration.replaceRen_eq_self_of_mentions a a',
        Restoration.replaceRen_eq_self_of_mentions b b',
        Restoration.replaceRen_eq_self_of_mentions c c'⟩
  refine S₀.addConstVals hsplit ?_
  intro c hc
  rcases List.mem_append.mp hc with hsrc | haux
  · have hget := VEnv.addConstVals_get hadded hsrc
    have hn := hnotR hfreshAll hget
    have hρ := Restoration.lambdaReplacement_eq_none_of_not_restorable
      (domains := fun _ => E.production.compilationSignature.params) hn
    obtain ⟨_, hty, -⟩ := (henvTypes.ordered.onTypes_noFreshConsts hfreshAll).1 hget
    obtain ⟨u, hu⟩ := henvTypes.ordered.constWF hget
    refine ⟨fun t ht => (by rw [hρ] at ht; cases ht), fun _ => ?_⟩
    refine ⟨c.toVConstant, by rw [Restoration.renaming_eq_self hn]; exact hle.constants hget,
      rfl, u, ?_⟩
    rw [Restoration.replaceRen_eq_self hty]
    exact hu.mono hle
  · have hget := VEnv.addConstVals_get hsplit (List.mem_append_right _ haux)
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp haux
    have hmem : t.name ∈ (compilationRestoration sourceDecl auxiliaries).heads.map
        (·.auxiliary) := by
      rw [hheadNames]
      exact mem_familyNames.mpr ⟨t, ht, .inl rfl⟩
    obtain ⟨hd, hf, hdmem, hdaux⟩ := Restoration.find?_of_mem_heads hmem
    have hget' : E.production.constructors.completed.headerVEnv.constants hd.auxiliary =
        some t.toVConstVal.toVConstant := by rw [hdaux]; exact hget
    obtain ⟨hfree, htyped⟩ := hrepl hd hdmem _ hget'
    refine ⟨fun t' ht' => ?_, fun hnone => ?_⟩
    · simp only [Restoration.lambdaReplacement, hf, Option.map_some,
        Option.some.injEq] at ht'
      subst ht'
      rw [Restoration.replaceRen_eq_self hfree]
      exact htyped.mono hle
    · simp [Restoration.lambdaReplacement, hf] at hnone

/-- Names of the source prefix of the lowered declaration are not
restorable. -/
theorem not_restorable_of_take {types : List VInductiveType} {k : Nat}
    {sourceDecl : VInductDecl} {auxiliaries : List ContainerSpecialization}
    (hnodup : (familyNames types ++ types.map (fun t => t.name.str "rec")).Nodup)
    (hheadNames : (compilationRestoration sourceDecl auxiliaries).heads.map (·.auxiliary) =
      familyNames (types.drop k))
    (hauxNames : auxiliaries.map (·.auxiliary) = (types.drop k).map (·.name))
    {n : Name} (hn : n ∈ familyNames (types.take k)) :
    n ∉ (compilationRestoration sourceDecl auxiliaries).restorableNames := by
  intro hmem
  have hsplit : familyNames types = familyNames (types.take k) ++ familyNames (types.drop k) := by
    rw [← familyNames_append, List.take_append_drop]
  obtain ⟨hfam, -, hdisj⟩ := List.nodup_append.mp hnodup
  rcases List.mem_append.mp hmem with hh | hr
  · rw [hheadNames] at hh
    rw [hsplit] at hfam
    exact (List.nodup_append.mp hfam).2.2 n hn n hh rfl
  · rw [compilationRestoration_recursors_fst] at hr
    have hr' : n ∈ types.map (fun t => t.name.str "rec") := by
      have : auxiliaries.map (fun a => a.auxiliary.str "rec") =
          (types.drop k).map (fun t => t.name.str "rec") := by
        have := congrArg (List.map (fun n : Name => n.str "rec")) hauxNames
        simpa [List.map_map, Function.comp_def] using this
      rw [this] at hr
      exact List.map_subset _ (List.drop_subset _ _) hr
    have hn' : n ∈ familyNames types := by
      rw [hsplit]; exact List.mem_append_left _ hn
    exact hdisj n hn' n hr' rfl

/-- A structure registered in the base environment is an old constant, so its
name is not restorable. -/
theorem NestedValidatedRunResult.baseProjection_not_restorable
    {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}
    (E : NestedValidatedRunResult result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (wf : ves.WFCore sourceProdEnv)
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
    (hnodup : (familyNames E.production.loweredDecl.types ++
      E.production.loweredDecl.types.map (fun t => t.name.str "rec")).Nodup)
    {S : Name} {info : VProjectionInfo}
    (hS : (ves.venv (if isUnsafe then .unsafe else .safe)).projections S info) :
    S ∉ (compilationRestoration sourceDecl auxiliaries).restorableNames := by
  intro hmem
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hlookup, -⟩ :=
    (wf.tr (safety := if isUnsafe then .unsafe else .safe)).wf.ordered.projectionShape hS
  have h := (VEnv.addConstVals_le hadded).constants hlookup
  rw [E.restorableNames_fresh hadded Haux Hexpansion hnodup S hmem] at h
  cases h

/-- **The constructor stage**: the context-carrying renaming replacement from
the lowered constructor environment with its projections into the final
abstract environment, modulo the typing of the restoration lambdas of the auxiliary
constructors (`HauxCtor`), the transport of the lowered projections
(`Hproj`), and projection-name avoidance (`HprojNames`, `Helim`). -/
theorem NestedValidatedRunResult.constructorRenamingReplacement
    {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}
    (E : NestedValidatedRunResult result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (wf : ves.WFCore sourceProdEnv)
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
    (hauxNames : auxiliaries.map (·.auxiliary) =
      (E.production.loweredDecl.types.drop sourceDecl.types.length).map (·.name))
    {envS : VEnv} (hSwf : envS.WF) (hle : envTypes ≤ envS)
    (Helim : EliminatorProjNamesAvoid (ves.venv (if isUnsafe then .unsafe else .safe))
      (compilationRestoration sourceDecl auxiliaries).restorableNames)
    (hctorsS : ∀ sc ∈ sourceDecl.constructorConstants,
      envS.constants sc.name = some sc.toVConstant)
    (hnames : List.Forall₂ (fun st lt : VInductiveType => List.Forall₂
        (fun sc lc : VConstVal => lc.name = sc.name) st.ctors lt.ctors)
      sourceDecl.types (E.production.loweredDecl.types.take sourceDecl.types.length))
    (Hlowered : List.Forall₂ (fun lowered source : VInductiveType =>
        List.Forall₂ (fun lc sc : VConstVal => ∃ restored,
            (compilationRestoration sourceDecl auxiliaries).expr lc.type = some restored ∧
            envTypes.SimAt sourceDecl.uvars [] restored sc.type)
          lowered.ctors source.ctors)
      (E.production.loweredDecl.types.take sourceDecl.types.length) sourceDecl.types)
    (HprojNamesCtor : ∀ lc ∈ E.production.loweredDecl.constructorConstants,
      lc.type.projNamesAvoid (compilationRestoration sourceDecl auxiliaries).restorableNames =
        true)
    (HauxCtor : ∀ t ∈ E.production.loweredDecl.types.drop sourceDecl.types.length,
      ∀ lc ∈ t.ctors, ∀ h ∈ (compilationRestoration sourceDecl auxiliaries).heads,
        h.auxiliary = lc.name →
        ∃ restored, (compilationRestoration sourceDecl auxiliaries).expr lc.type =
            some restored ∧
          envTypes.HasType sourceDecl.uvars []
            (VExpr.wrapLams E.production.compilationSignature.params
              (VExpr.mkApps (.const h.target h.levels) h.arguments)) restored)
    (Hproj : ∀ entry ∈ E.production.loweredDecl.projectionEntries,
      VEnv.ProjectionTransportOnCtx envS
        ((compilationRestoration sourceDecl auxiliaries).lambdaReplacement
          fun _ => E.production.compilationSignature.params)
        (compilationRestoration sourceDecl auxiliaries).renaming
        entry.typeName entry.info)
    (Hes : ∀ e ∈ E.production.constructors.declared.eliminators, ∃ families r,
      VEnv.RestoredEliminator envS
        ((compilationRestoration sourceDecl auxiliaries).lambdaReplacement
          fun _ => E.production.compilationSignature.params)
        (compilationRestoration sourceDecl auxiliaries).renaming e.1 e.2 families r) :
    VEnv.RenamingReplacementOnCtx envS
      ((E.production.constructors.declared.venvCtors.addEliminators
          E.production.constructors.declared.eliminators).addProjections
        E.production.loweredDecl.projectionEntries)
      ((compilationRestoration sourceDecl auxiliaries).lambdaReplacement
        fun _ => E.production.compilationSignature.params)
      (compilationRestoration sourceDecl auxiliaries).renaming := by
  obtain ⟨hsplit, hheadNames, hnp, hargs, hPclosed, hscoped, hrepl⟩ :=
    E.headerSetup wf hadded henvTypes Haux Hexpansion hnodup
  have ShS := E.headerRenamingReplacement wf hadded henvTypes Haux Hexpansion hnodup
    hSwf.ordered hle Helim
  have ShT := E.headerRenamingReplacement wf hadded henvTypes Haux Hexpansion hnodup
    henvTypes.ordered VEnv.LE.rfl Helim
  have SubT := RenamingRestorationSubstitution.of_lambda ShT hnp
  have hβT : envTypes.BetaSubjectReduction sourceDecl.uvars := henvTypes.betaSubjectReduction
  have hcore := E.production.constructors.core
  -- the lowered constructor constants are well formed in the lowered header environment
  have hloweredUvars : E.production.c.lparams.length = sourceDecl.uvars := by
    have h2 := E.nativeSource.core.uvars
    rw [E.nativeSourceDecl_eq] at h2
    rw [h2, E.production_c, E.productionContext_lparams]
  have hlcWF : ∀ lc ∈ E.production.loweredDecl.constructorConstants,
      lc.uvars = sourceDecl.uvars ∧
        lc.toVConstant.WF E.production.constructors.completed.headerVEnv := by
    intro lc hlc
    obtain ⟨t, ht, hlct⟩ := List.mem_flatMap.mp hlc
    obtain ⟨T, -, hT⟩ := Lean4Lean.List.Forall₂.forall_exists_r hcore.types t ht
    obtain ⟨C, -, hC⟩ := Lean4Lean.List.Forall₂.forall_exists_r hT.ctors lc hlct
    exact ⟨hC.uvars.trans hloweredUvars, hC.wf⟩
  -- transported typing and restoration of a lowered constructor type, in `envTypes`
  have hsim : ∀ lc ∈ E.production.loweredDecl.constructorConstants, ∀ restored,
      (compilationRestoration sourceDecl auxiliaries).expr lc.type = some restored →
      ∃ u, envTypes.IsDefEq sourceDecl.uvars []
        (lc.type.replaceRen ((compilationRestoration sourceDecl auxiliaries).lambdaReplacement
          fun _ => E.production.compilationSignature.params)
          (compilationRestoration sourceDecl auxiliaries).renaming) restored (.sort u) := by
    intro lc hlc restored hr
    obtain ⟨hu, u, hwf⟩ := hlcWF lc hlc
    have H := ShT.isDefEq hwf
    simp only [List.map_nil] at H
    rw [hu] at H
    exact ⟨_, SubT.expr_simAt hβT (Γ := []) trivial
      (Restoration.projNamesFixed_of_avoid (HprojNamesCtor lc hlc)) hr _ H⟩
  refine ((ShS.addConstVals hcore.ctorsAdded ?_).toOnCtx.addEliminators Hes).addProjections Hproj
  intro lc hlc
  obtain ⟨t, ht, hlct⟩ := List.mem_flatMap.mp hlc
  rw [← List.take_append_drop sourceDecl.types.length E.production.loweredDecl.types] at ht
  rcases List.mem_append.mp ht with hprim | hauxT
  · -- a source constructor: kept, with the source constructor type
    have Hboth : List.Forall₂ (fun st lt : VInductiveType => List.Forall₂
        (fun sc lc : VConstVal => lc.name = sc.name ∧ ∃ restored,
          (compilationRestoration sourceDecl auxiliaries).expr lc.type = some restored ∧
          envTypes.SimAt sourceDecl.uvars [] restored sc.type) st.ctors lt.ctors)
        sourceDecl.types (E.production.loweredDecl.types.take sourceDecl.types.length) :=
      Lean4Lean.List.Forall₂.imp (fun st lt h =>
          Lean4Lean.List.Forall₂.imp (fun _ _ h => h)
            (Lean4Lean.List.Forall₂.and h.1 (Lean4Lean.List.Forall₂.flip
              (R := fun sc lc : VConstVal => ∃ restored,
                (compilationRestoration sourceDecl auxiliaries).expr lc.type = some restored ∧
                envTypes.SimAt sourceDecl.uvars [] restored sc.type) h.2)))
        (Lean4Lean.List.Forall₂.and hnames (Lean4Lean.List.Forall₂.flip
          (R := fun st lt : VInductiveType => List.Forall₂ (fun lc sc : VConstVal => ∃ restored,
            (compilationRestoration sourceDecl auxiliaries).expr lc.type = some restored ∧
            envTypes.SimAt sourceDecl.uvars [] restored sc.type) lt.ctors st.ctors) Hlowered))
    obtain ⟨st, hst, hrel⟩ := Lean4Lean.List.Forall₂.forall_exists_r Hboth t hprim
    obtain ⟨sc, hsc, hscName, restored, hr, hsimS⟩ :=
      Lean4Lean.List.Forall₂.forall_exists_r hrel lc hlct
    have hn : lc.name ∉ (compilationRestoration sourceDecl auxiliaries).restorableNames :=
      not_restorable_of_take hnodup hheadNames hauxNames
        (mem_familyNames.mpr ⟨t, hprim, .inr ⟨lc, hlct, rfl⟩⟩)
    have hρ := Restoration.lambdaReplacement_eq_none_of_not_restorable
      (domains := fun _ => E.production.compilationSignature.params) hn
    refine ⟨fun t' ht' => (by rw [hρ] at ht'; cases ht'), fun _ => ?_⟩
    have hscUvars : sc.uvars = lc.uvars := by
      rw [(hlcWF lc hlc).1]
      have Hsource := E.nativeSource.core
      rw [E.nativeSourceDecl_eq] at Hsource
      obtain ⟨T, -, hT⟩ := Lean4Lean.List.Forall₂.forall_exists_r Hsource.types st hst
      obtain ⟨C, -, hC⟩ := Lean4Lean.List.Forall₂.forall_exists_r hT.ctors sc hsc
      rw [hC.uvars, Hsource.uvars]
    obtain ⟨u, hdef⟩ := hsim lc hlc restored hr
    have hdef' := hsimS _ hdef.hasType.2
    have hchain : envTypes.IsDefEq sourceDecl.uvars [] _ sc.type (.sort u) := hdef.trans hdef'
    refine ⟨sc.toVConstant, ?_, hscUvars, u, ?_⟩
    · rw [Restoration.renaming_eq_self hn, hscName]
      exact hctorsS sc (List.mem_flatMap.mpr ⟨st, hst, hsc⟩)
    · rw [(hlcWF lc hlc).1]
      exact (hchain.symm).mono hle
  · -- an auxiliary constructor: replaced by its restoration lambda
    have hmem : lc.name ∈ (compilationRestoration sourceDecl auxiliaries).heads.map
        (·.auxiliary) := by
      rw [hheadNames]
      exact mem_familyNames.mpr ⟨t, hauxT, .inr ⟨lc, hlct, rfl⟩⟩
    obtain ⟨hd, hf, hdmem, hdaux⟩ := Restoration.find?_of_mem_heads hmem
    refine ⟨fun t' ht' => ?_, fun hnone => ?_⟩
    · simp only [Restoration.lambdaReplacement, hf, Option.map_some,
        Option.some.injEq] at ht'
      subst ht'
      obtain ⟨restored, hr, htyped⟩ := HauxCtor t hauxT lc hlct hd hdmem hdaux
      obtain ⟨u, hdef⟩ := hsim lc hlc restored hr
      rw [(hlcWF lc hlc).1]
      exact (VEnv.IsDefEq.defeqDF hdef.symm htyped).mono hle
    · simp [Restoration.lambdaReplacement, hf] at hnone

/-- **The recursor stage**: extending a renaming replacement along an
installation of recursors, each kept under its restored name with its
restored type, which is installed in `envS`. -/
theorem RenamingReplacement.ofAddConstants_recursors
    {r : Restoration} {P : List VExpr} {envS : VEnv} (hSwf : envS.WF)
    (hnp : ∀ h ∈ r.heads, h.nparams = P.length)
    {safety : DefinitionSafety} {env : Environment} {venv : VEnv}
    {entries : List (ConstantInfo × VConstVal)} {outEnv : Environment} {outVEnv : VEnv}
    (H : AddConstants safety env venv entries outEnv outVEnv)
    (S : VEnv.RenamingReplacementOnCtx envS venv (r.lambdaReplacement fun _ => P) r.renaming)
    (hrecs : ∀ v ∈ entries.map Prod.snd,
      r.heads.find? (fun h => h.auxiliary == v.name) = none ∧
      v.type.projNamesAvoid r.restorableNames = true ∧
      ∃ w, r.recursor v = some w ∧ envS.constants w.name = some w.toVConstant) :
    VEnv.RenamingReplacementOnCtx envS outVEnv (r.lambdaReplacement fun _ => P)
      r.renaming := by
  induction H with
  | nil => exact S
  | cons hn hnprim htr hwf hadd hdelta _ ih =>
    rename_i cinfo value venvNext rest outE outV envHead Htail
    apply ih
    · refine S.addConst hadd ⟨?_, ?_⟩
      · obtain ⟨hfind, -, -⟩ := hrecs value (by simp)
        intro t ht
        rw [htr.2] at ht
        simp [Restoration.lambdaReplacement, hfind] at ht
      · intro _
        obtain ⟨hfind, hproj, w, hw, hwS⟩ := hrecs value (by simp)
        simp only [Restoration.recursor, Option.bind_eq_bind, Option.bind_eq_some_iff,
          Option.pure_def, Option.some.injEq] at hw
        obtain ⟨rt, hrt, rfl⟩ := hw
        obtain ⟨u, hu⟩ := hwf
        have H1 := S.isDefEq hu trivial
        simp only [List.map_nil, VExpr.replaceRen] at H1
        have SubS := RenamingRestorationSubstitutionOnCtx.of_lambda S hnp
        have H2 := SubS.expr_simAt hSwf.betaSubjectReduction (Γ := []) trivial
          (Restoration.projNamesFixed_of_avoid hproj) hrt _ H1
        refine ⟨{ uvars := value.uvars, type := rt }, ?_, rfl, u, H2.symm⟩
        rw [htr.2, Restoration.renaming_of_find_none hfind]
        exact hwS
    · exact fun v hv => hrecs v (by simp only [List.map_cons, List.mem_cons]; exact .inr hv)

/-- The facts used by `hrestoredWF_of_gaps`, for a restoration table
`auxiliaries` and a final assembly shape `C` (see the module documentation;
proved for the run by `NestedValidatedRunResult.restoredEquationGaps`). -/
structure NestedRestoredEquationGaps
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
  /-- Projection names of the base eliminator schemas avoid the restorable
  names. -/
  eliminatorProjNames : EliminatorProjNamesAvoid
    (ves.venv (if isUnsafe then .unsafe else .safe))
    (compilationRestoration sourceDecl auxiliaries).restorableNames
  /-- Projection names of the lowered constructor types avoid the restorable
  names. -/
  constructorProjNames : ∀ lc ∈ E.production.loweredDecl.constructorConstants,
    lc.type.projNamesAvoid (compilationRestoration sourceDecl auxiliaries).restorableNames =
      true
  /-- Projection names of the generated recursor types avoid the restorable
  names. -/
  recursorProjNames :
    ∀ owner : Fin E.production.production.generationSignature.families.size,
      (E.production.production.canonicalGeneration.recursorType owner).projNamesAvoid
        (compilationRestoration sourceDecl auxiliaries).restorableNames = true
  /-- Projection names of the generated equations avoid the restorable names. -/
  equationProjNames :
    ∀ k : Fin E.production.production.generationSignature.constructors.size,
      (E.production.production.canonicalGeneration.equation k).lhs.projNamesAvoid
          (compilationRestoration sourceDecl auxiliaries).restorableNames = true ∧
      (E.production.production.canonicalGeneration.equation k).rhs.projNamesAvoid
          (compilationRestoration sourceDecl auxiliaries).restorableNames = true ∧
      (E.production.production.canonicalGeneration.equation k).type.projNamesAvoid
          (compilationRestoration sourceDecl auxiliaries).restorableNames = true
  /-- The restoration lambda `λ params, J.c levels args` of every auxiliary
  constructor head has the restored type of the lowered auxiliary
  constructor. -/
  auxiliaryConstructors : ∀ envTypes : VEnv,
    (ves.venv (if isUnsafe then .unsafe else .safe)).addConstVals
      sourceDecl.typeConstants = some envTypes →
    ∀ t ∈ E.production.loweredDecl.types.drop sourceDecl.types.length,
      ∀ lc ∈ t.ctors, ∀ h ∈ (compilationRestoration sourceDecl auxiliaries).heads,
        h.auxiliary = lc.name →
        ∃ restored, (compilationRestoration sourceDecl auxiliaries).expr lc.type =
            some restored ∧
          envTypes.HasType sourceDecl.uvars []
            (VExpr.wrapLams E.production.compilationSignature.params
              (VExpr.mkApps (.const h.target h.levels) h.arguments)) restored
  /-- The projection rules of the lowered declaration's projections
  transport to the final abstract environment. -/
  projections : ∀ entry ∈ E.production.loweredDecl.projectionEntries,
    VEnv.ProjectionTransportOnCtx C.finalBaseVEnv
      ((compilationRestoration sourceDecl auxiliaries).lambdaReplacement
        fun _ => E.production.compilationSignature.params)
      (compilationRestoration sourceDecl auxiliaries).renaming
      entry.typeName entry.info

/-- **The case eliminator of the lowered window is matched by the restored schema of a final
assembly shape** (`VEnv.RestoredEliminator`): the shape registers the schema with the same key
and signature, restored by a specialisation list whose restoration tables are those of the run,
so its restoration agrees with the lambda replacement and renaming of every restoration table of
the run (`RestorationTableData.find_eq`). The lowered schema projects only out of base
structures (its certificate `OrdinaryCaseEliminators`), which are not restorable, and the
restoration succeeds on its generic equations because it succeeds on its generic case type, the
registered source case type. -/
theorem NestedValidatedRunResult.restoredEliminators
    {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}
    (E : NestedValidatedRunResult result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (wf : ves.WFCore sourceProdEnv)
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
    (hnodup : (familyNames E.production.loweredDecl.types ++
      E.production.loweredDecl.types.map (fun t => t.name.str "rec")).Nodup)
    (D : RestorationTableData sourceDecl auxiliaries result E.loweredEnv
      (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 lparams)
    (hnp : ∀ h ∈ (compilationRestoration sourceDecl auxiliaries).heads,
      h.nparams = E.production.compilationSignature.params.length)
    (C : NestedFinalAssemblyShape E.restoration
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe))
    (hC : C.production = E.production) (hSwf : C.finalBaseVEnv.WF) :
    ∀ e ∈ E.production.constructors.declared.eliminators, ∃ families r,
      VEnv.RestoredEliminator C.finalBaseVEnv
        ((compilationRestoration sourceDecl auxiliaries).lambdaReplacement
          fun _ => E.production.compilationSignature.params)
        (compilationRestoration sourceDecl auxiliaries).renaming e.1 e.2 families r := by
  obtain ⟨key, sL, auxC, hcompEl, hesEq, DC⟩ := C.eliminatorsRestored
  rw [hC] at hcompEl
  intro e he
  change e ∈ E.production.constructors.completed.eliminators at he
  rw [hcompEl, List.mem_singleton] at he
  subst he
  -- the lowered schema projects only out of base structures
  have Havoid :
      (∀ owner type, (CaseSchema.ofCompilation E.production.loweredDecl sL []).genericType
          owner = some type →
        type.projNamesAvoid (compilationRestoration sourceDecl auxiliaries).restorableNames =
          true) ∧
      (∀ owner rules, (CaseSchema.ofCompilation E.production.loweredDecl sL []).genericEquations
          key owner = some rules → ∀ df ∈ rules,
        df.lhs.projNamesAvoid (compilationRestoration sourceDecl auxiliaries).restorableNames =
          true ∧
        df.rhs.projNamesAvoid (compilationRestoration sourceDecl auxiliaries).restorableNames =
          true ∧
        df.type.projNamesAvoid (compilationRestoration sourceDecl auxiliaries).restorableNames =
          true) := by
    have Hord := E.production.constructors.completed.eliminatorsOrdinary
    rw [hcompEl] at Hord
    rcases Hord with ⟨hE, -⟩ | ⟨s, key', hE', -, -, -, -, envTypes', envCtors', ht', hc', -,
      hprojs, -⟩
    · cases hE
    · simp only [List.cons.injEq, Prod.mk.injEq, and_true] at hE'
      obtain ⟨rfl, hs⟩ := hE'
      rw [← hs] at hprojs
      have hnot : ∀ S, (∃ info, envCtors'.projections S info) →
          S ∉ (compilationRestoration sourceDecl auxiliaries).restorableNames := by
        rintro S ⟨info, hinfo⟩
        rw [VEnv.addConstVals_projections_eq hc', VEnv.addConstVals_projections_eq ht',
          E.production_initialEnv] at hinfo
        exact E.baseProjection_not_restorable wf hadded Haux Hexpansion hnodup hinfo
      refine ⟨fun owner type h => (hprojs.1 owner type h).projNamesAvoid hnot,
        fun owner rules h df hdf => ?_⟩
      obtain ⟨hl, hr, ht⟩ := hprojs.2 owner rules h df hdf
      exact ⟨hl.projNamesAvoid hnot, hr.projNamesAvoid hnot, ht.projNamesAvoid hnot⟩
  -- the restored schema is registered in the final environment
  have hreg : C.finalBaseVEnv.eliminators key
      (CaseSchema.ofCompilation sourceDecl sL auxC) := by
    have hle := C.canonical.recursorsAdded.le
    refine hle.eliminators ?_
    rw [VEnv.addProjections_eliminators, hesEq]
    exact VEnv.addEliminators_iff.mpr (.inl (List.mem_singleton_self _))
  have A := (RenamingRestorationAgreement.of_lambda hnp).congr (D.find_eq DC)
    (fun n => (D.recursorName n).trans (DC.recursorName n).symm)
  refine ⟨sourceDecl.types.map fun t : VInductiveType => t.name,
    compilationRestoration sourceDecl auxC,
    VEnv.RestoredEliminator.of_wf hSwf rfl hreg A
      (fun owner type h => Restoration.projNamesFixed_of_avoid (Havoid.1 owner type h)) ?_⟩
  intro owner rules h df hdf
  obtain ⟨hl, hr, ht⟩ := Havoid.2 owner rules h df hdf
  refine ⟨Restoration.projNamesFixed_of_avoid hl, Restoration.projNamesFixed_of_avoid hr,
    Restoration.projNamesFixed_of_avoid ht, ?_⟩
  refine CaseSchema.genericEquations_restorable rfl key owner (fun type htype => ?_) h df hdf
  obtain ⟨type', h', -⟩ := ShapeModel.VEnv.WF.eliminator_genericType_closed hSwf hreg owner
  have := CaseSchema.genericType_withRestoration (schema :=
    CaseSchema.ofCompilation E.production.loweredDecl sL []) rfl htype
    (sourceDecl.types.map fun t : VInductiveType => t.name)
    (compilationRestoration sourceDecl auxC)
  change (CaseSchema.ofCompilation sourceDecl sL auxC).genericType owner = _ at this
  rw [h'] at this
  rw [← this]
  rfl

/-- **The renaming restoration substitution of a nested run**, from the
lowered recursor environment into the final abstract environment of a final
assembly shape, for the restoration table of
`restorationTablesRestoringAll`, modulo `NestedRestoredEquationGaps`. -/
theorem NestedValidatedRunResult.restoredEquationSubstitution
    {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}
    (E : NestedValidatedRunResult result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (wf : ves.WFCore sourceProdEnv) (Hsources : SourceSyntaxChecks sourceTypes)
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
    (hparamsSize : result.params.size = result.nparams)
    (D : RestorationTableData sourceDecl auxiliaries result E.loweredEnv
      (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 lparams)
    (Hrestoring : List.Forall₂ (fun source lowered : VInductiveType => List.Forall₂
          (fun sc lc : VConstVal => VExpr.NestedExprExpansion
            ((compilationRestoration sourceDecl auxiliaries).RestoringLeaf
              (VLevel.params sourceDecl.uvars)) 0 sc.type lc.type)
          source.ctors lowered.ctors)
        sourceDecl.types (E.production.loweredDecl.types.take sourceDecl.types.length))
    (C : NestedFinalAssemblyShape E.restoration
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe))
    (hC : C.production = E.production)
    (hV : CheckingEnv.Valid (if isUnsafe then .unsafe else .safe)
      (Lean4Lean.stripRecursorRules outEnv
        (Lean4Lean.restoredRecursorNames
          (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 sourceTypes
          (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).1)) C.finalBaseVEnv)
    (G : NestedRestoredEquationGaps E C auxiliaries) :
    RenamingRestorationSubstitutionOnCtx C.finalBaseVEnv
      E.production.production.outVEnv
      (compilationRestoration sourceDecl auxiliaries)
      ((compilationRestoration sourceDecl auxiliaries).lambdaReplacement
        fun _ => E.production.compilationSignature.params)
      (compilationRestoration sourceDecl auxiliaries).renaming := by
  have hnodup :
      (familyNames E.production.loweredDecl.types ++
        E.production.loweredDecl.types.map (fun t => t.name.str "rec")).Nodup := by
    rcases E.containerSpecializations wf Hsources with
      ⟨_, _, _, _, _, _, _, h, _⟩
    exact h
  obtain ⟨-, -, hauxNames, hheadNames', -, -, -, hscoped, -⟩ :=
    E.restorationPrefix_of wf hadded henvTypes Haux Hexpansion hnodup D True.intro
  obtain ⟨-, -, hnp, -, -, -, -⟩ := E.headerSetup wf hadded henvTypes Haux Hexpansion hnodup
  have hfreshAll := E.restorableNames_fresh hadded Haux Hexpansion hnodup
  have hSwf : C.finalBaseVEnv.WF := hV.tr.wf
  -- the source header environment of the shape
  have hvenvTypes : C.canonical.venvTypes = envTypes := by
    have h1 := C.canonical.typesAdded.abstract
    rw [C.typeValues, hadded] at h1
    exact (Option.some.inj h1).symm
  have hctorsAdded := C.canonical.ctorsAdded.abstract
  rw [C.constructorValues, hvenvTypes] at hctorsAdded
  have hleCtors : C.canonical.venvCtors ≤ C.finalBaseVEnv :=
    VEnv.addEliminators_addProjections_le.trans C.canonical.recursorsAdded.le
  have hle : envTypes ≤ C.finalBaseVEnv :=
    (VEnv.addConstVals_le hctorsAdded).trans hleCtors
  have hctorsS : ∀ sc ∈ sourceDecl.constructorConstants,
      C.finalBaseVEnv.constants sc.name = some sc.toVConstant :=
    fun sc hsc => hleCtors.constants (VEnv.addConstVals_get hctorsAdded hsc)
  -- constructor names of the source prefix
  have hnames : List.Forall₂ (fun st lt : VInductiveType => List.Forall₂
        (fun sc lc : VConstVal => lc.name = sc.name) st.ctors lt.ctors)
      sourceDecl.types (E.production.loweredDecl.types.take sourceDecl.types.length) := by
    have h := C.formationAssembly.types
    rw [C.formationExpanded, hC] at h
    have hlen : sourceDecl.types.length =
        (E.production.loweredDecl.types.take sourceDecl.types.length).length := by
      have := Lean4Lean.List.Forall₂.length_eq h
      simp only [List.length_append] at this
      simp only [List.length_take]
      omega
    rw [← List.take_append_drop sourceDecl.types.length E.production.loweredDecl.types] at h
    have h1 := ((Lean4Lean.List.Forall₂.append_of_left hlen).mp h).1
    exact Lean4Lean.List.Forall₂.imp (fun _ _ hx =>
      Lean4Lean.List.Forall₂.imp (fun _ _ hc => hc.name) hx.constructors) h1
  have hlevels := E.loweredConstructorLevels_heads wf Hsources hheadNames'
  have Hlowered := E.loweredConstructors_of_evidence hadded henvTypes hfreshAll Hrestoring
    hlevels
  have S₁ := E.constructorRenamingReplacement wf hadded henvTypes Haux Hexpansion hnodup
    hauxNames hSwf hle G.eliminatorProjNames hctorsS hnames Hlowered G.constructorProjNames
    (G.auxiliaryConstructors envTypes hadded) G.projections
    (E.restoredEliminators wf hadded Haux Hexpansion hnodup D hnp C hC hSwf)
  -- the restored recursors
  have hrestoredRecs := E.restoredRecursorEntries_of_hitShape C hC wf Hsources hadded Haux
    Hexpansion hnodup hparamsSize D hscoped
  have hrecAdded := C.canonical.recursorsAdded.abstract
  rw [C.recursorValues] at hrecAdded
  have hrecs : ∀ v ∈ E.production.production.entries.map Prod.snd,
      (compilationRestoration sourceDecl auxiliaries).heads.find?
          (fun h => h.auxiliary == v.name) = none ∧
      v.type.projNamesAvoid (compilationRestoration sourceDecl auxiliaries).restorableNames =
        true ∧
      ∃ w, (compilationRestoration sourceDecl auxiliaries).recursor v = some w ∧
        C.finalBaseVEnv.constants w.name = some w.toVConstant := by
    intro v hv
    have hcanon := E.production.production.canonicalRecursors
    change E.production.production.entries.map Prod.snd = _ at hcanon
    rw [hcanon] at hv
    simp only [InductiveSignature.Instance.recursors, List.mem_map, List.mem_finRange,
      true_and] at hv
    obtain ⟨owner, rfl⟩ := hv
    obtain ⟨w, hw, hrw⟩ := Lean4Lean.List.Forall₂.forall_exists_l hrestoredRecs owner
      (List.mem_finRange owner)
    refine ⟨E.recursorName_not_head Haux Hexpansion hnodup owner,
      G.recursorProjNames owner, w, hrw.1, VEnv.addConstVals_get hrecAdded hw⟩
  rw [← E.production.constructors.declared.contextVEnv] at S₁
  have S₂ := RenamingReplacement.ofAddConstants_recursors hSwf hnp
    E.production.production.installed S₁ hrecs
  exact RenamingRestorationSubstitutionOnCtx.of_lambda S₂ hnp

/-- `HrestoredWF` from a renaming restoration substitution from the lowered
recursor environment to the final abstract environment of each shape, under
which the projection names of the generated equations are fixed. -/
theorem NestedValidatedRunResult.hrestoredWF_of_substitution
    {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}
    (E : NestedValidatedRunResult result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (HS : ∀ auxiliaries : List ContainerSpecialization,
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
        ∃ ρ σ, RenamingRestorationSubstitution C.finalBaseVEnv
            E.production.production.outVEnv
            (compilationRestoration sourceDecl auxiliaries) ρ σ ∧
          ∀ k : Fin E.production.production.generationSignature.constructors.size,
            (E.production.production.canonicalGeneration.equation k).lhs.ProjNamesFixed σ ∧
            (E.production.production.canonicalGeneration.equation k).rhs.ProjNamesFixed σ ∧
            (E.production.production.canonicalGeneration.equation k).type.ProjNamesFixed
              σ) :
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
        ∀ (k : Fin E.production.production.generationSignature.constructors.size)
          (rule : VDefEq),
          (compilationRestoration sourceDecl auxiliaries).equation
              (E.production.production.canonicalGeneration.equation k) =
            some rule →
          rule.WF C.finalBaseVEnv := by
  intro auxiliaries D C hC hV k rule hrule
  obtain ⟨ρ, σ, S, hfix⟩ := HS auxiliaries D C hC hV
  obtain ⟨hl, hr, ht⟩ := hfix k
  exact Restoration.equation_wf' S hV.tr.wf.betaSubjectReduction (E.loweredEquationWF k)
    hl hr ht hrule

/-- **`HrestoredWF` of `NestedValidatedRunResult.hruleShape_of`**: every
restored generated equation is well formed in the final abstract environment
of a final assembly shape in which the stripped output environment is valid,
modulo `NestedRestoredEquationGaps` (the hypothesis-free form is
`NestedValidatedRunResult.hrestoredWF_of`,
`Nested/AuxiliaryProjectionTransport.lean`).

The generated equation is well formed in the lowered recursor environment
(`loweredEquationWF`); the context-carrying renaming restoration substitution
of the run
(`restoredEquationSubstitution`, for the table of
`restorationTablesRestoringAll`, whose restoration agrees with that of every
table by `RestorationTableData.expr_eq`) transports it to the final abstract
environment, where beta subject reduction holds by well-formedness. -/
theorem NestedValidatedRunResult.hrestoredWF_of_gaps
    {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}
    (E : NestedValidatedRunResult result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (wf : ves.WFCore sourceProdEnv) (Hsources : SourceSyntaxChecks sourceTypes)
    (G : ∀ auxiliaries : List ContainerSpecialization,
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
        NestedRestoredEquationGaps E C auxiliaries) :
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
        ∀ (k : Fin E.production.production.generationSignature.constructors.size)
          (rule : VDefEq),
          (compilationRestoration sourceDecl auxiliaries).equation
              (E.production.production.canonicalGeneration.equation k) =
            some rule →
          rule.WF C.finalBaseVEnv := by
  intro auxiliaries D C hC hV k rule hrule
  rcases E.restorationTablesRestoringAll wf Hsources with
    ⟨envTypes, generated, aux', hadded, henvTypes, Haux, Hexpansion, hparamsSize, D',
      Hrestoring, -⟩
  have G' := G aux' D' C hC hV
  have S := E.restoredEquationSubstitution wf Hsources hadded henvTypes Haux Hexpansion
    hparamsSize D' Hrestoring C hC hV G'
  have hrule' : (compilationRestoration sourceDecl aux').equation
      (E.production.production.canonicalGeneration.equation k) = some rule := by
    simp only [Restoration.equation, D.expr_eq D'] at hrule ⊢
    exact hrule
  obtain ⟨hl, hr, ht⟩ := G'.equationProjNames k
  exact Restoration.equation_wf_onCtx S hV.tr.wf.betaSubjectReduction (E.loweredEquationWF k)
    (Restoration.projNamesFixed_of_avoid hl) (Restoration.projNamesFixed_of_avoid hr)
    (Restoration.projNamesFixed_of_avoid ht) hrule'

end VerifyInductive
end Lean4Lean
