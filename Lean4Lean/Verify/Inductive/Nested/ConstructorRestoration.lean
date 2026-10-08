import Lean4Lean.Theory.Inductive.RestorationDefEq
import Lean4Lean.Theory.Inductive.BetaSubjectReduction
import Lean4Lean.Verify.Inductive.Nested.CompilationDataAssembly
import Lean4Lean.Theory.Typing.EnvLemmas
import Lean4Lean.Theory.Inductive.CaseProjections
import Lean4Lean.Verify.Typing.ConstSupport
import Lean4Lean.Verify.Inductive.Nested.EliminatorAvoidance
import Lean4Lean.Std.List

/-! Restoration of the constructor types of the source families of a
validated nested run (the `sourceConstructors` field of
`NestedCompilationPending`).

The lowered header environment `envL` is the source header environment
`envTypes` extended by the opaque auxiliary family headers. Replacing each
restoration head by the lambda abstraction of its container specialization
over the common parameters (`Restoration.lambdaReplacement`) is a
`RestorationSubstitution envTypes envL`; with beta subject reduction of the
well-formed `envTypes` it transports the defeq of `Models.constructors`
between a normalized and a lowered constructor type to the source
environment (`RestoresType.of_models_constructor'`).

The facts not derived from the run are collected in
`NestedConstructorRestorationGaps`. The specialization list and the freshness
of its restoration names are hypotheses here; `Nested.CompilationDataConstructors`
supplies them from `NestedValidatedRunResult.restorationTablesRestoring` and
`NestedValidatedRunResult.restorableNames_fresh`.
-/

namespace Lean4Lean

open InductiveSignature

namespace InductiveSignature

/-! ### Lambda replacement on terms avoiding the restoration heads -/

theorem Restoration.replaceConsts_lambdaReplacement {r : Restoration}
    {domains : HeadSpecialization → List VExpr} :
    ∀ {e : VExpr}, e.containsAnyConst (r.heads.map (·.auxiliary)) = false →
      e.replaceConsts (r.lambdaReplacement domains) = e
  | .bvar _, _ | .sort _, _ | .elim .., _ => rfl
  | .const c ls, h => by
    have hc : c ∉ r.heads.map (·.auxiliary) := by
      simpa [VExpr.containsAnyConst] using h
    exact VExpr.replaceConsts_const_none (Restoration.lambdaReplacement_eq_none hc)
  | .app f a, h | .lam f a, h | .forallE f a, h => by
    simp only [VExpr.containsAnyConst, Bool.or_eq_false_iff] at h
    simp only [VExpr.replaceConsts, replaceConsts_lambdaReplacement h.1,
      replaceConsts_lambdaReplacement h.2]
  | .proj n i e, h => by
    simp only [VExpr.containsAnyConst, Bool.or_eq_false_iff] at h
    simp only [VExpr.replaceConsts, replaceConsts_lambdaReplacement h.2]

/-! ### The lambda replacement is a restoration substitution -/

/-- Lookups of the extended header environment: either a lookup of the
source header environment or one of the appended headers. -/
theorem lookup_of_addConstVals_append {env envTypes envL : VEnv}
    {sourceTC auxTC : List VConstVal}
    (htypes : env.addConstVals sourceTC = some envTypes)
    (hlowered : env.addConstVals (sourceTC ++ auxTC) = some envL)
    (hc : envL.constants c = some ci) :
    envTypes.constants c = some ci ∨
      ∃ entry ∈ auxTC, entry.name = c ∧ entry.toVConstant = ci := by
  rcases VEnv.addConstVals_lookup_origin hlowered hc with hbase | ⟨entry, hmem, hname, hval⟩
  · exact .inl ((VEnv.addConstVals_le htypes).constants hbase)
  · rcases List.mem_append.mp hmem with hsrc | haux
    · left
      rw [← hname, ← hval]
      exact VEnv.addConstVals_get htypes hsrc
    · exact .inr ⟨entry, haux, hname, hval⟩

theorem addConstVals_append_defeqs {env envTypes envL : VEnv}
    {sourceTC auxTC : List VConstVal}
    (htypes : env.addConstVals sourceTC = some envTypes)
    (hlowered : env.addConstVals (sourceTC ++ auxTC) = some envL) :
    envL.defeqs = envTypes.defeqs ∧ envL.eliminators = envTypes.eliminators ∧
      envL.projections = envTypes.projections :=
  ⟨(VEnv.addConstVals_defeqs hlowered).trans (VEnv.addConstVals_defeqs htypes).symm,
    (VEnv.addConstVals_eliminators hlowered).trans
      (VEnv.addConstVals_eliminators htypes).symm,
    (VEnv.addConstVals_projections hlowered).trans
      (VEnv.addConstVals_projections htypes).symm⟩

/-- The lambda replacement of a restoration table over a common closed
parameter telescope `P` is a `RestorationSubstitution` from the extended
header environment to the source header environment. -/
theorem Restoration.lambdaReplacement_substitution {env envTypes envL : VEnv}
    {sourceTC auxTC : List VConstVal} {r : Restoration} {P : List VExpr}
    (henvTypes : envTypes.WF)
    (htypes : env.addConstVals sourceTC = some envTypes)
    (hlowered : env.addConstVals (sourceTC ++ auxTC) = some envL)
    (hnparams : ∀ h ∈ r.heads, h.nparams = P.length)
    (hargs : ∀ h ∈ r.heads, ∀ arg ∈ h.arguments, arg.ClosedN h.nparams)
    (hPclosed : ∀ i (hi : i < P.length), P[i].ClosedN i)
    (hfresh : ∀ name ∈ r.heads.map (·.auxiliary), envTypes.constants name = none)
    (hauxHeads : ∀ entry ∈ auxTC, entry.name ∈ r.heads.map (·.auxiliary))
    (hrecFresh : ∀ p ∈ r.recursors, envTypes.constants p.1 = none)
    (hreplaced : ∀ h ∈ r.heads, ∀ ci, envL.constants h.auxiliary = some ci →
      ci.type.containsAnyConst (r.heads.map (·.auxiliary)) = false ∧
      envTypes.HasType ci.uvars []
        (VExpr.wrapLams P (VExpr.mkApps (.const h.target h.levels) h.arguments)) ci.type)
    (helim : EliminatorsAvoidConsts envTypes (r.heads.map (·.auxiliary))) :
    RestorationSubstitution envTypes envL r (r.lambdaReplacement fun _ => P) := by
  have hordered := henvTypes.ordered
  have hon := hordered.onTypes_noFreshConsts hfresh
  have hfix : ∀ {e : VExpr}, e.containsAnyConst (r.heads.map (·.auxiliary)) = false →
      e.replaceConsts (r.lambdaReplacement fun _ => P) = e :=
    Restoration.replaceConsts_lambdaReplacement
  have hfixConst : ∀ {c ci}, envTypes.constants c = some ci →
      ci.type.replaceConsts (r.lambdaReplacement fun _ => P) = ci.type := by
    intro c ci hci
    obtain ⟨_, h, _⟩ := hon.1 hci
    exact hfix h
  have hnotHead : ∀ {c ci}, envTypes.constants c = some ci →
      r.lambdaReplacement (fun _ => P) c = none := by
    intro c ci hci
    apply Restoration.lambdaReplacement_eq_none
    intro hmem
    rw [hfresh c hmem] at hci
    cases hci
  have hfind : ∀ {c h}, r.heads.find? (fun h => h.auxiliary == c) = some h →
      h ∈ r.heads ∧ h.auxiliary = c := by
    intro c h hf
    exact ⟨List.mem_of_find?_eq_some hf, by simpa using List.find?_some hf⟩
  have ⟨hdf, hel, hpr⟩ := addConstVals_append_defeqs htypes hlowered
  refine {
    closed := ?_
    ordered := hordered
    replaced := ?_
    kept := ?_
    defeqs := ?_
    eliminators := ?_
    projections := ?_
    shape := ?_
    headsFresh := ?_
    recursorsFresh := hrecFresh }
  · intro c t hρ
    refine ⟨?_, Restoration.lambdaReplacement_ne_forallE r hρ⟩
    unfold Restoration.lambdaReplacement at hρ
    cases hf : r.heads.find? (fun h => h.auxiliary == c) with
    | none => simp [hf] at hρ
    | some h =>
      simp only [hf, Option.map_some, Option.some.injEq] at hρ
      subst hρ
      obtain ⟨hmem, -⟩ := hfind hf
      refine VExpr.ClosedN.wrapLams_closed (n := 0) (by simpa using hPclosed) ?_
      refine VExpr.ClosedN.mkApps_closed trivial fun arg harg => ?_
      have := hargs h hmem arg harg
      rw [hnparams h hmem] at this
      simpa using this
  · intro c ci t hci hρ
    unfold Restoration.lambdaReplacement at hρ
    cases hf : r.heads.find? (fun h => h.auxiliary == c) with
    | none => simp [hf] at hρ
    | some h =>
      simp only [hf, Option.map_some, Option.some.injEq] at hρ
      subst hρ
      obtain ⟨hmem, rfl⟩ := hfind hf
      obtain ⟨hfree, htyped⟩ := hreplaced h hmem ci hci
      rw [hfix hfree]
      exact htyped
  · intro c ci hci hρ
    rcases lookup_of_addConstVals_append htypes hlowered hci with h | ⟨entry, hmem, rfl, -⟩
    · exact ⟨ci, h, rfl, (hfixConst h).symm⟩
    · exfalso
      obtain ⟨h, hh, heq⟩ := List.mem_map.mp (hauxHeads entry hmem)
      have hsome : (r.heads.find? (fun h => h.auxiliary == entry.name)).isSome :=
        List.find?_isSome.mpr ⟨h, hh, by simp [heq]⟩
      unfold Restoration.lambdaReplacement at hρ
      cases hf : r.heads.find? (fun h => h.auxiliary == entry.name) with
      | none => rw [hf] at hsome; cases hsome
      | some _ => rw [hf] at hρ; cases hρ
  · intro df hdf'
    rw [hdf] at hdf'
    obtain ⟨h1, h2⟩ := hon.2 hdf'
    exact ⟨df, hdf', rfl, (hfix h1.1).symm, (hfix h2.1).symm, (hfix h1.2).symm⟩
  · intro block schema hs
    rw [hel] at hs
    obtain ⟨ht, hrules⟩ := helim block schema hs
    have hfix' : ∀ {e : VExpr}, e.mentionsAnyConst (r.heads.map (·.auxiliary)) = false →
        e.replaceConsts (r.lambdaReplacement fun _ => P) = e :=
      VExpr.replaceConsts_lambdaReplacement_of_mentions
    refine ⟨hs, fun owner type h => hfix' (ht owner type h), ?_⟩
    intro owner rules h df hdf
    obtain ⟨a, b, c⟩ := hrules owner rules h df hdf
    exact ⟨hfix' a, hfix' b, hfix' c⟩
  · intro typeName info hp
    rw [hpr] at hp
    obtain ⟨_, htn⟩ := hordered.projectionConstant hp
    have hctor := hordered.projectionConstructor hp
    exact ⟨hp, hnotHead htn, hnotHead hctor, hfixConst hctor⟩
  · intro c t hρ
    exact Restoration.lambdaReplacement_shape r (fun h hmem => (hnparams h hmem).symm) hρ
  · intro c h hf
    obtain ⟨hmem, rfl⟩ := hfind hf
    exact hfresh _ (List.mem_map_of_mem hmem)

/-! ### Constructor correspondence from a restoration substitution -/

/-- Split a constructor-list correspondence along families of equal
constructor counts. -/
theorem forall₂_ctors_split {R : VConstVal → VConstVal → Prop} :
    ∀ {A B : List VInductiveType},
      List.Forall₂ (fun a b => a.ctors.length = b.ctors.length) A B →
      List.Forall₂ R (A.flatMap (·.ctors)) (B.flatMap (·.ctors)) →
      List.Forall₂ (fun a b => List.Forall₂ R a.ctors b.ctors) A B
  | _, _, .nil, _ => .nil
  | _, _, .cons hlen hrest, H => by
    simp only [List.flatMap_cons] at H
    obtain ⟨h1, h2⟩ := (Lean4Lean.List.Forall₂.append_of_left hlen).mp H
    exact .cons h1 (forall₂_ctors_split hrest h2)

theorem forall₂_take' {R : α → β → Prop} :
    ∀ {l : List α} {r : List β} (_ : List.Forall₂ R l r) (k : Nat),
      List.Forall₂ R (l.take k) (r.take k)
  | _, _, .nil, _ => by simp
  | _, _, .cons _ _, 0 => by simp
  | _, _, .cons h t, k + 1 => by
    simp only [List.take_succ_cons]
    exact .cons h (forall₂_take' t k)

/-- The constructor correspondence of the source families, from a restoration
substitution, the defeq of normalized and lowered constructor types in the
lowered header environment, the restoration of the lowered constructor types
to the source ones, and totality of restoration on the normalized types. -/
theorem sourceConstructors_of_substitution {envS envL : VEnv} {r : Restoration}
    {ρ : Name → Option VExpr} {U : Nat}
    (S : RestorationSubstitution envS envL r ρ) (hβ : envS.BetaSubjectReduction U)
    {normalized lowered source : List VInductiveType}
    (Hdefeq : List.Forall₂ (fun n l => List.Forall₂
      (fun nc lc : VConstVal => envL.IsDefEqU U [] nc.type lc.type) n.ctors l.ctors)
      normalized lowered)
    (Hlowered : List.Forall₂ (fun l src => List.Forall₂
      (fun lc sc : VConstVal => ∃ restored, r.expr lc.type = some restored ∧
        envS.SimAt U [] restored sc.type) l.ctors src.ctors) lowered source)
    (Htotal : ∀ n ∈ normalized, ∀ c ∈ n.ctors, ∃ restored, r.expr c.type = some restored) :
    List.Forall₂ (fun n src => List.Forall₂
      (fun nc sc : VConstVal => RestoresType r envS U nc.type sc.type) n.ctors src.ctors)
      normalized source := by
  refine Lean4Lean.List.Forall₂.trans (fun n l src hnl hls => ?_)
    (Lean4Lean.List.Forall₂.and_mem Hdefeq) Hlowered
  obtain ⟨hnl, hn, -⟩ := hnl
  refine Lean4Lean.List.Forall₂.trans (fun nc lc sc hd hl => ?_)
    (Lean4Lean.List.Forall₂.and_mem hnl) hls
  obtain ⟨hd, hnc, -⟩ := hd
  obtain ⟨restored, hr, hsim⟩ := hl
  exact RestoresType.of_models_constructor' S hβ hd hr hsim (Htotal n hn nc hnc)

end InductiveSignature

namespace VerifyInductive

open Lean hiding Environment Exception
open Kernel

/-- The facts used here that are not derived from a validated nested run.

* `loweredConstructors`: each lowered constructor type of a source family
  restores to (a term defeq at every type to) the source constructor type.
  The abstract expansion relation `NestedAuxiliarySourceAbsolute` records the
  leaf's container, levels and arguments only up to definitional equality of
  the auxiliary family's type, not syntactically as the specialization of
  the auxiliary, so it does not determine the restoration of a leaf.
* `normalizedTotal`: restoration is defined on every normalized constructor
  type of a source family, i.e. every auxiliary head in the consumed field
  domains is applied to at least the parameters at the source universe
  arity. -/
structure NestedConstructorRestorationGaps (envTypes : VEnv)
    (sourceDecl loweredDecl : VInductDecl) (s : InductiveSignature)
    (auxiliaries : List ContainerSpecialization) : Prop where
  loweredConstructors : List.Forall₂ (fun lowered source : VInductiveType =>
      List.Forall₂ (fun lc sc : VConstVal => ∃ restored,
          (compilationRestoration sourceDecl auxiliaries).expr lc.type = some restored ∧
          envTypes.SimAt sourceDecl.uvars [] restored sc.type)
        lowered.ctors source.ctors)
    (loweredDecl.types.take sourceDecl.types.length) sourceDecl.types
  normalizedTotal : ∀ normalized ∈ s.declaration.types.take sourceDecl.types.length,
    ∀ ctor ∈ normalized.ctors, ∃ restored,
      (compilationRestoration sourceDecl auxiliaries).expr ctor.type = some restored

theorem mem_familyNames {types : List VInductiveType} {name : Name} :
    name ∈ familyNames types ↔ ∃ t ∈ types, name = t.name ∨ ∃ c ∈ t.ctors, name = c.name := by
  simp only [familyNames, List.mem_flatMap, List.mem_cons, List.mem_map]
  constructor
  · rintro ⟨t, ht, h | ⟨c, hc, rfl⟩⟩
    · exact ⟨t, ht, .inl h⟩
    · exact ⟨t, ht, .inr ⟨c, hc, rfl⟩⟩
  · rintro ⟨t, ht, h | ⟨c, hc, rfl⟩⟩
    · exact ⟨t, ht, .inl h⟩
    · exact ⟨t, ht, .inr ⟨c, hc, rfl⟩⟩

/-- **Restoration of the source constructor types of a validated nested run**
(the `sourceConstructors` field of `NestedCompilationPending`), for any
specialization list with exact lowering evidence whose restoration heads and
recursors are fresh in the source header environment, modulo
`NestedConstructorRestorationGaps`. The specializations are supplied by the
caller (in `Nested.CompilationDataConstructors`, by
`NestedValidatedRunResult.restorationTablesRestoring`). -/
theorem NestedValidatedRunResult.sourceConstructors_of_evidence
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
    (hfresh : ∀ name ∈ (compilationRestoration sourceDecl auxiliaries).heads.map
      (·.auxiliary), envTypes.constants name = none)
    (hrecFresh : ∀ p ∈ (compilationRestoration sourceDecl auxiliaries).recursors,
      envTypes.constants p.1 = none)
    (G : NestedConstructorRestorationGaps envTypes sourceDecl E.production.loweredDecl
      E.production.compilationSignature auxiliaries) :
    ∀ envTypes', (ves.venv (if isUnsafe then .unsafe else .safe)).addConstVals
        sourceDecl.typeConstants = some envTypes' →
      List.Forall₂ (fun normalized family : VInductiveType =>
          List.Forall₂ (fun normalized ctor : VConstVal =>
            RestoresType (compilationRestoration sourceDecl auxiliaries) envTypes'
              sourceDecl.uvars normalized.type ctor.type)
            normalized.ctors family.ctors)
        (E.production.compilationSignature.declaration.types.take
          sourceDecl.types.length) sourceDecl.types := by
  intro envTypes' hadded'
  rw [hadded] at hadded'
  cases hadded'
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
  -- the base and lowered header environments
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
  -- the common parameter telescope
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
  -- the family head of each auxiliary, and its evidence
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
    have heqh := Lean4Lean.List.nodup_map_inj hscopedNodup hh hfh
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
      VEnv.IsDefEqCtx.trans_empty henvTypes hP (hctx.symm hordered)
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
  -- the restoration substitution
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
  -- the lowered defeq of normalized and lowered constructor types
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
  have Hdefeq := forall₂_take' (forall₂_ctors_split (R := fun nc lc : VConstVal =>
      E.production.constructors.completed.headerVEnv.IsDefEqU sourceDecl.uvars []
        nc.type lc.type) Hlengths
    (Lean4Lean.List.Forall₂.imp (fun _ _ h => by
      rw [hloweredUvars] at h
      exact h.2.2) Hctors)) sourceDecl.types.length
  exact sourceConstructors_of_substitution S henvTypes.betaSubjectReduction Hdefeq
    G.loweredConstructors G.normalizedTotal

end VerifyInductive

end Lean4Lean
