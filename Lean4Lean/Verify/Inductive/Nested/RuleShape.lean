import Lean4Lean.Verify.Inductive.Nested.LoweredRulesAvoid

/-! The rule-shape hypothesis `HruleShape` of `NestedValidatedRunResult.hrules_of`.

The final assembly shapes produced by `assemblyShapeNative` carry the rule
validator's equations, whose left-hand sides and types are not syntactically
the restored generated ones. `NestedValidatedRunResult.hruleShape_of` rebuilds
the shape of `assemblyShapeNativeValid` (which also records that the stripped
output environment is valid in the shape's final abstract environment) with
the restored generated equations themselves as its rule lists
(`NestedFinalAssemblyShape.withRules`), keeping every other field:

* realization of the executable restored rules
  (`restoredRuleRealization_of_equation`): the right-hand side of each
  restored rule translates (rule validator) and its translation is the
  restored generated right-hand side (`restoredRuleRhs_of_trail`, with the
  freshness of the non-renamed restorable names and the input-side avoidance
  `loweredRulesAvoid_renamed`, so no naming hypothesis is needed);
* the primary iota trace (`RestoredPrimaryIotaSemanticTrace.replaceRules`):
  every restored generated equation of a source constructor is a nested iota
  rule of the restored block (`primaryNestedIotaRule`); its left-hand side and
  type clauses are computed from the generator, its right-hand-side clauses
  are the rule validator's (the right-hand sides coincide by uniqueness of
  translation);
* the auxiliary traces (`RestoredAuxiliaryFinalWFTrace.replaceRules`): rule
  counts, and guardedness of the right-hand sides (rule validator).

The one semantic obligation of the traces that is not derived is the
well-formedness of the restored generated equations in the final abstract
environment (`HrestoredWF`). Restoring a typing derivation of the lowered
environment is available only for terms over the family headers
(`Restoration.expr_hasType` with a `RestorationSubstitution`), whereas the
generated left-hand sides, minor premises and types mention the lowered
auxiliary constructors and the primary constructors, whose source types are
the restorations of their lowered types only up to definitional equality. -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open InductiveSignature

namespace VerifyInductive

/-! ### The restoration is determined by the restoration table data

(as in `RecursorProvenance`, kept local) -/

section TableUniqueness

variable {decl : VInductDecl} {result : Lean4Lean.ElimNestedInductive.Result}
  {env : Environment} {auxRec : NameMap Name} {Us₀ : List Name}

private theorem heads_nodup_RS {aux : List ContainerSpecialization}
    (D : RestorationTableData decl aux result env auxRec Us₀) :
    ((compilationRestoration decl aux).heads.map (·.auxiliary)).Nodup := by
  rw [compilationRestoration_heads_auxiliary]
  exact D.headNodup

/-- The family data of a specialization is fixed by the tables. -/
private theorem RestorationTableData.family_transfer_RS {aux₀ aux₁ : List ContainerSpecialization}
    (D₀ : RestorationTableData decl aux₀ result env auxRec Us₀)
    (D₁ : RestorationTableData decl aux₁ result env auxRec Us₀)
    {a : ContainerSpecialization} (ha : a ∈ aux₁) :
    ∃ b ∈ aux₀, b.auxiliary = a.auxiliary ∧ b.source.name = a.source.name ∧
      b.levels = a.levels ∧ b.arguments = a.arguments := by
  obtain ⟨nested, hn⟩ := D₁.familyLookup a ha
  obtain ⟨b, hb, hbaux, hbspec⟩ := D₀.familyKey _ nested hn
  obtain ⟨a', ha', ha'aux, ha'spec⟩ := D₁.familyKey _ nested hn
  -- `a` and `a'` have the same family head
  let hA : HeadSpecialization :=
    ⟨a.auxiliary, decl.uvars, decl.nparams, a.source.name, a.levels, a.arguments⟩
  let hA' : HeadSpecialization :=
    ⟨a'.auxiliary, decl.uvars, decl.nparams, a'.source.name, a'.levels, a'.arguments⟩
  have hmemA : hA ∈ (compilationRestoration decl aux₁).heads :=
    List.mem_flatMap.mpr ⟨a, ha, List.mem_cons_self⟩
  have hmemA' : hA' ∈ (compilationRestoration decl aux₁).heads :=
    List.mem_flatMap.mpr ⟨a', ha', List.mem_cons_self⟩
  have h1 := Restoration.find?_of_nodup (heads_nodup_RS D₁) hmemA
  have h2 := Restoration.find?_of_nodup (heads_nodup_RS D₁) hmemA'
  have hauxEq : hA'.auxiliary = hA.auxiliary := ha'aux
  rw [hauxEq, h1] at h2
  have hAA : hA = hA' := Option.some.inj h2
  simp only [hA, hA', HeadSpecialization.mk.injEq] at hAA
  obtain ⟨-, -, -, hsrc, hlev, hargs⟩ := hAA
  obtain ⟨hs, hl, hr⟩ := AuxNestedSpec.unique hbspec ha'spec
  exact ⟨b, hb, hbaux, hs.trans hsrc.symm, hl.trans hlev.symm,
    hr.trans hargs.symm⟩

/-- Every head of one table is a head of any other table of the same run. -/
private theorem RestorationTableData.find_transfer_RS {aux₀ aux₁ : List ContainerSpecialization}
    (D₀ : RestorationTableData decl aux₀ result env auxRec Us₀)
    (D₁ : RestorationTableData decl aux₁ result env auxRec Us₀)
    {n : Name} {h : HeadSpecialization}
    (hfind : (compilationRestoration decl aux₁).heads.find? (fun h => h.auxiliary == n) =
      some h) :
    (compilationRestoration decl aux₀).heads.find? (fun h => h.auxiliary == n) = some h := by
  have hmem := List.mem_of_find?_eq_some hfind
  have hn : h.auxiliary = n := by simpa using List.find?_some hfind
  subst hn
  obtain ⟨a, ha, hh⟩ := List.mem_flatMap.mp hmem
  obtain ⟨b, hb, hbaux, hbsrc, hblev, hbargs⟩ := D₀.family_transfer_RS D₁ ha
  simp only [ContainerSpecialization.heads, List.mem_cons, List.mem_map] at hh
  rcases hh with rfl | ⟨ctor, hctor, rfl⟩
  · let hB : HeadSpecialization :=
      ⟨b.auxiliary, decl.uvars, decl.nparams, b.source.name, b.levels, b.arguments⟩
    have hmemB : hB ∈ (compilationRestoration decl aux₀).heads :=
      List.mem_flatMap.mpr ⟨b, hb, List.mem_cons_self⟩
    have := Restoration.find?_of_nodup (heads_nodup_RS D₀) hmemB
    simp only [hB, hbaux, hbsrc, hblev, hbargs] at this
    exact this
  · obtain ⟨info, hc, hind⟩ := D₁.ctorInstalled a ha ctor hctor
    obtain ⟨ctor', hctor', hcname⟩ :=
      D₀.ctorLookup _ info hc b hb (hind.trans hbaux.symm)
    have hrenA : (a.constructorName ctor).replacePrefix a.auxiliary a.source.name =
        ctor.name :=
      (namePrefix_of_replacePrefix_ne (D₁.ctorRenamed a ha ctor hctor)).replacePrefix_replacePrefix _
    have hrenB : (b.constructorName ctor').replacePrefix b.auxiliary b.source.name =
        ctor'.name :=
      (namePrefix_of_replacePrefix_ne (D₀.ctorRenamed b hb ctor' hctor')).replacePrefix_replacePrefix _
    have hname : ctor'.name = ctor.name := by
      rw [← hrenA, ← hrenB, ← hcname, hbaux, hbsrc]
    let hB : HeadSpecialization :=
      ⟨b.constructorName ctor', decl.uvars, decl.nparams, ctor'.name, b.levels, b.arguments⟩
    have hmemB : hB ∈ (compilationRestoration decl aux₀).heads :=
      List.mem_flatMap.mpr ⟨b, hb, List.mem_cons_of_mem _
        (List.mem_map.mpr ⟨ctor', hctor', rfl⟩)⟩
    have := Restoration.find?_of_nodup (heads_nodup_RS D₀) hmemB
    simp only [hB, ← hcname, hname, hblev, hbargs] at this
    exact this

private theorem RestorationTableData.find_eq_RS {aux₀ aux₁ : List ContainerSpecialization}
    (D₀ : RestorationTableData decl aux₀ result env auxRec Us₀)
    (D₁ : RestorationTableData decl aux₁ result env auxRec Us₀) (n : Name) :
    (compilationRestoration decl aux₀).heads.find? (fun h => h.auxiliary == n) =
      (compilationRestoration decl aux₁).heads.find? (fun h => h.auxiliary == n) := by
  cases h1 : (compilationRestoration decl aux₁).heads.find? (fun h => h.auxiliary == n) with
  | some h => exact D₀.find_transfer_RS D₁ h1
  | none =>
    cases h0 : (compilationRestoration decl aux₀).heads.find? (fun h => h.auxiliary == n) with
    | none => rfl
    | some h =>
      have := D₁.find_transfer_RS D₀ h0
      rw [h1] at this
      cases this

private theorem Restoration.go_congr_RS {r r' : Restoration}
    (hfind : ∀ n, r.heads.find? (fun h => h.auxiliary == n) =
      r'.heads.find? (fun h => h.auxiliary == n))
    (hrec : ∀ n, r.recursorName n = r'.recursorName n) :
    ∀ (e : VExpr) (args : List VExpr),
      Restoration.expr.go r e args = Restoration.expr.go r' e args := by
  intro e
  induction e with
  | bvar | sort | elim => intro args; rfl
  | const name levels =>
    intro args
    simp only [Restoration.expr.go, hfind name, hrec name]
  | app fn arg ihf iha =>
    intro args
    simp only [Restoration.expr.go, iha, ihf]
  | lam d b ihd ihb =>
    intro args
    simp only [Restoration.expr.go, ihd, ihb]
  | forallE d b ihd ihb =>
    intro args
    simp only [Restoration.expr.go, ihd, ihb]
  | proj n i m ih =>
    intro args
    simp only [Restoration.expr.go, ih]

/-- **The restoration is determined by the restoration table data.** -/
private theorem RestorationTableData.expr_eq_RS {aux₀ aux₁ : List ContainerSpecialization}
    (D₀ : RestorationTableData decl aux₀ result env auxRec Us₀)
    (D₁ : RestorationTableData decl aux₁ result env auxRec Us₀) (e : VExpr) :
    (compilationRestoration decl aux₀).expr e = (compilationRestoration decl aux₁).expr e :=
  Restoration.go_congr_RS (D₀.find_eq_RS D₁)
    (fun n => (D₀.recursorName n).trans (D₁.recursorName n).symm) e []

end TableUniqueness

/-! ### Replacing the rule lists of the final traces -/

/-- Replace the abstract rules of a primary rule trace by rules with the same
nested-iota shape and well-formedness obligations. -/
theorem RestoredPrimaryIotaRuleTrace.replaceRules
    {decl : VInductDecl} {block : VInductBlock} {owner : VInductiveType}
    {result : Lean4Lean.ElimNestedInductive.Result} {prodEnv : Environment}
    {P : NestedInstalledProduction prodEnv} {targetVEnv : VEnv} {auxRec : NameMap Name}
    {oldRecName newRecName : Name} {oldRules newRules : List RecursorRule}
    {Hrules : RulesRestoration result prodEnv auxRec oldRecName newRecName oldRules newRules}
    {ctors : List VConstVal} {rules : List VDefEq}
    (H : RestoredPrimaryIotaRuleTrace decl block owner result prodEnv P targetVEnv auxRec
      oldRecName newRecName Hrules ctors rules)
    {rules' : List VDefEq}
    (H' : List.Forall₂ (fun ctor rule =>
      Nonempty (decl.NestedIotaRule block owner ctor rule) ∧ rule.WF targetVEnv) ctors rules') :
    RestoredPrimaryIotaRuleTrace decl block owner result prodEnv P targetVEnv auxRec
      oldRecName newRecName Hrules ctors rules' := by
  induction H generalizing rules' with
  | nil => cases H'; exact .nil
  | cons Hrule Hrules abstractRule Hshape Hwf Hrest ih =>
    cases H' with
    | cons h t => exact .cons Hrule Hrules _ (Classical.choice h.1) h.2 (ih t)

private theorem forall₂_append_left_split_RS {R : α → β → Prop} :
    ∀ {l₁ l₂ : List α} {r : List β}, List.Forall₂ R (l₁ ++ l₂) r →
      ∃ r₁ r₂, r = r₁ ++ r₂ ∧ List.Forall₂ R l₁ r₁ ∧ List.Forall₂ R l₂ r₂
  | [], _, _, H => ⟨[], _, rfl, .nil, H⟩
  | _ :: _, _, _, .cons h t => by
    obtain ⟨r₁, r₂, rfl, H₁, H₂⟩ := forall₂_append_left_split_RS t
    exact ⟨_ :: r₁, r₂, rfl, .cons h H₁, H₂⟩

/-- Replace the abstract rules of a primary semantic trace, family by family. -/
theorem RestoredPrimaryIotaSemanticTrace.replaceRules
    {decl : VInductDecl} {block : VInductBlock} {targetVEnv : VEnv}
    {lparams : List Name} {safety : DefinitionSafety}
    {sourceVEnv envTypes envCtors : VEnv}
    {result : Lean4Lean.ElimNestedInductive.Result}
    {loweredEnv : Environment} {P : NestedInstalledProduction loweredEnv}
    {auxRec : NameMap Name} {allIndNames : List Name}
    {sourceTypes : List InductiveType} {sourceProdEnv targetProdEnv : Environment}
    {Htrace : StateForMTrace
      (RestoredInductiveStep result loweredEnv auxRec allIndNames)
      sourceTypes sourceProdEnv targetProdEnv}
    {owners : List VInductiveType} {recursors : List VConstVal}
    {Hsource : RestoredSourceInductiveSemanticTrace decl lparams safety sourceVEnv
      envTypes envCtors Htrace owners recursors}
    {owners' : List VInductiveType} {rules : List VDefEq}
    (H : RestoredPrimaryIotaSemanticTrace decl block targetVEnv P Hsource owners' rules)
    {rules' : List VDefEq}
    (H' : List.Forall₂ (fun (oc : VInductiveType × VConstVal) rule =>
      Nonempty (decl.NestedIotaRule block oc.1 oc.2 rule) ∧ rule.WF targetVEnv)
      (ownedConstructorsFor owners') rules') :
    RestoredPrimaryIotaSemanticTrace decl block targetVEnv P Hsource owners' rules' := by
  induction H generalizing rules' with
  | nil => cases H'; exact .nil _
  | cons Hstep Htail Hheader Hconstructors Hrecursor Hrest Hhead Hrules ih =>
    obtain ⟨r₁, r₂, rfl, Hh, Ht⟩ := forall₂_append_left_split_RS H'
    rw [Lean4Lean.List.forall₂_map_left_iff] at Hh
    exact .cons Hstep Htail Hheader Hconstructors Hrecursor Hrest
      (Hhead.replaceRules Hh) (ih Ht)

theorem RestoredAuxiliaryShapeTrace.rulesPrefix
    {decl : VInductDecl} {block : VInductBlock} {main : VInductiveType}
    {safety : DefinitionSafety} {trEnv : VEnv}
    {result : Lean4Lean.ElimNestedInductive.Result}
    {loweredEnv : Environment} {auxRec : NameMap Name} {allIndNames : List Name}
    {names : List Name} {sourceEnv targetEnv : Environment}
    {Htrace : StateForMTrace
      (RestoredRecursorStep result loweredEnv auxRec allIndNames)
      names sourceEnv targetEnv}
    {priorRecursors finalRecursors : List VConstVal}
    {priorRules finalRules : List VDefEq}
    (H : RestoredAuxiliaryShapeTrace decl block main safety trEnv Htrace
      priorRecursors priorRules finalRecursors finalRules) :
    priorRules.length ≤ finalRules.length := by
  induction H with
  | nil => exact Nat.le_refl _
  | cons Hstep Htail Hsemantic Hrest ih =>
    simp only [List.length_append] at ih
    omega

/-- Replace the abstract rules of an auxiliary semantic/well-formedness fold,
moving to a block `block'`: the new rules need only have the right count,
guarded right-hand sides for `block'`, and be well formed. -/
theorem RestoredAuxiliaryFinalWFTrace.replaceRules
    {decl : VInductDecl} {block : VInductBlock} {main : VInductiveType}
    {safety : DefinitionSafety} {trEnv recursorEnv ruleEnv : VEnv}
    {result : Lean4Lean.ElimNestedInductive.Result}
    {loweredEnv : Environment} {auxRec : NameMap Name} {allIndNames : List Name}
    {names : List Name} {sourceEnv targetEnv : Environment}
    {Htrace : StateForMTrace
      (RestoredRecursorStep result loweredEnv auxRec allIndNames)
      names sourceEnv targetEnv}
    {priorRecursors finalRecursors : List VConstVal}
    {priorRules finalRules : List VDefEq}
    {Hsemantic : RestoredAuxiliaryShapeTrace decl block main safety trEnv Htrace
      priorRecursors priorRules finalRecursors finalRules}
    (H : RestoredAuxiliaryFinalWFTrace decl block main safety trEnv recursorEnv
      ruleEnv Hsemantic priorRecursors priorRules finalRecursors finalRules)
    (block' : VInductBlock) (priorRules' added final' : List VDefEq)
    (hfinal' : final' = priorRules' ++ added)
    (hlen : priorRules.length + added.length = finalRules.length)
    (Hguard : ∀ rule ∈ added, rule.rhs.GuardedRuleRhs (block'.recursors.map (·.name)))
    (Hwf : ∀ rule ∈ added, rule.WF ruleEnv) :
    ∃ Hsemantic' : RestoredAuxiliaryShapeTrace decl block' main safety trEnv Htrace
        priorRecursors priorRules' finalRecursors final',
      RestoredAuxiliaryFinalWFTrace decl block' main safety trEnv recursorEnv ruleEnv
        Hsemantic' priorRecursors priorRules' finalRecursors final' :=
  match H with
  | .nil sourceEnv recursors rules => by
    have hnil : added = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hnil
    simp only [List.append_nil] at hfinal'
    subst final'
    exact ⟨.nil sourceEnv recursors priorRules', .nil sourceEnv recursors priorRules'⟩
  | .cons Hstep Htail Hsemantic Hrest Hrecursor _ Hfinal => by
    have hpre := Hrest.rulesPrefix
    simp only [List.length_append] at hpre
    let m := Hsemantic.rules.length
    let Hsemantic' : RestoredAuxiliaryStepShape decl block' main safety trEnv Hstep
        priorRecursors := {
      recursor := Hsemantic.recursor
      rules := added.take m
      translated := Hsemantic.translated
      rulesLength := by
        rw [List.length_take, ← Hsemantic.rulesLength]
        omega }
    obtain ⟨Hrest', Hfinal'⟩ := Hfinal.replaceRules block' (priorRules' ++ added.take m)
      (added.drop m) final'
      (by rw [hfinal', List.append_assoc, List.take_append_drop])
      (by simp only [List.length_append, List.length_drop]; omega)
      (fun rule hrule => Hguard rule (List.mem_of_mem_drop hrule))
      (fun rule hrule => Hwf rule (List.mem_of_mem_drop hrule))
    exact ⟨.cons Hstep Htail Hsemantic' Hrest', .cons Hstep Htail Hsemantic' Hrest' Hrecursor
      (fun rule hrule => Hwf rule (List.mem_of_mem_take hrule)) Hfinal'⟩

/-- A final assembly shape with its rule lists and their three rule traces
replaced. Every other field is kept. -/
noncomputable def NestedFinalAssemblyShape.withRules
    {result : Lean4Lean.ElimNestedInductive.Result}
    {loweredEnv sourceProdEnv : Environment} {auxRec : NameMap Name}
    {allIndNames : List Name} {sourceTypes : List InductiveType}
    {auxRecNames : List Name} {outEnv : Environment}
    {H : RestoredNestedDeclarationsResult result loweredEnv sourceProdEnv
      auxRec allIndNames sourceTypes auxRecNames ((), outEnv)}
    {sourceEnv : VEnv} {decl : VInductDecl} {lparams : List Name}
    {nparams : Nat} {isUnsafe : Bool} {safety : DefinitionSafety}
    (C : NestedFinalAssemblyShape H sourceEnv decl lparams nparams isUnsafe safety)
    (primaryRules auxiliaryRules : List VDefEq)
    (Hprimary : RestoredPrimaryIotaSemanticTrace decl
      (canonicalRestoredShapeBlock decl C.primaryRecursors C.auxiliaryRecursors)
      C.finalBaseVEnv C.production C.sourceSemantics (C.main :: C.rest) primaryRules)
    (Hauxiliary : RestoredAuxiliaryShapeTrace decl
      (canonicalRestoredBlock decl C.primaryRecursors C.auxiliaryRecursors
        primaryRules auxiliaryRules) C.main safety
      ((C.canonical.venvCtors.addEliminators C.canonical.eliminators).addProjections decl.projectionEntries) H.auxiliaries
      [] [] C.auxiliaryRecursors auxiliaryRules)
    (HauxiliaryWF : RestoredAuxiliaryFinalWFTrace decl
      (canonicalRestoredBlock decl C.primaryRecursors C.auxiliaryRecursors
        primaryRules auxiliaryRules) C.main safety
      ((C.canonical.venvCtors.addEliminators C.canonical.eliminators).addProjections decl.projectionEntries)
      ((C.canonical.venvCtors.addEliminators C.canonical.eliminators).addProjections decl.projectionEntries)
      C.finalBaseVEnv Hauxiliary [] [] C.auxiliaryRecursors auxiliaryRules) :
    NestedFinalAssemblyShape H sourceEnv decl lparams nparams isUnsafe safety :=
  { C with
    primaryRules := primaryRules
    auxiliaryRules := auxiliaryRules
    primaryIota := Hprimary
    auxiliarySemantics := Hauxiliary
    auxiliaryWF := HauxiliaryWF }

/-! ### Realization of the restored generated equations -/

theorem _root_.Lean4Lean.InductiveSignature.Restoration.equation_eq_some
    {r : Restoration} {eq rule : VDefEq} (h : r.equation eq = some rule) :
    rule.uvars = eq.uvars ∧ r.expr eq.lhs = some rule.lhs ∧
      r.expr eq.rhs = some rule.rhs ∧ r.expr eq.type = some rule.type := by
  simp only [Restoration.equation, Option.bind_eq_bind, Option.pure_def] at h
  cases hl : r.expr eq.lhs with
  | none => simp [hl] at h
  | some lhs =>
    cases hr : r.expr eq.rhs with
    | none => simp [hl, hr] at h
    | some rhs =>
      cases ht : r.expr eq.type with
      | none => simp [hl, hr, ht] at h
      | some ty =>
        simp only [hl, hr, ht, Option.bind_some, Option.some.injEq] at h
        subst h
        exact ⟨rfl, rfl, rfl, rfl⟩

/-- A restored recursor rule's right-hand side translates in any environment
in which the stripped output environment is valid (the rule validator). -/
theorem NestedValidatedRunResult.restoredRuleRhs_translation
    {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}
    (E : NestedValidatedRunResult result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    {venv : VEnv}
    (hvalid : CheckingEnv.Valid (if isUnsafe then .unsafe else .safe)
      (Lean4Lean.stripRecursorRules outEnv
        (Lean4Lean.restoredRecursorNames
          (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 sourceTypes
          (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).1)) venv)
    {recName : Name}
    (hrecName : recName ∈ sourceTypes.map (fun t => Lean.mkRecName t.name) ++
      (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).1)
    {s t : Environment}
    (Hstep : RestoredRecursorStep result E.loweredEnv
      (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2
      (sourceTypes.map (·.name)) recName s t)
    (j : Nat) (hj : j < Hstep.restored.newInfo.rules.length) :
    ∃ target, TrExprS venv Hstep.restored.newInfo.levelParams []
      (Hstep.restored.newInfo.rules[j]'hj).rhs target := by
  have hrun := E.recursorRuleValidation
  obtain ⟨rule, hrule⟩ : ∃ rule, Hstep.restored.newInfo.rules[j]'hj = rule := ⟨_, rfl⟩
  rw [hrule]
  have hmem : rule ∈ Hstep.restored.newInfo.rules := hrule ▸ List.getElem_mem hj
  have hmem' := hmem
  rw [Hstep.restored.produced] at hmem'
  rcases List.mem_append.mp hrecName with hp | ha
  · obtain ⟨indType, hind, hname⟩ := List.mem_map.mp hp
    subst hname
    obtain ⟨_, target, _, Hty⟩ :=
      validateRestoredRecursorRules.primaryTranslation_of_run hvalid hrun hind Hstep.lookup hmem'
    refine ⟨target, ?_⟩
    have h := Hty.2.1
    rw [← Hstep.restored.produced] at h
    exact h
  · obtain ⟨_, target, _, Hty⟩ :=
      validateRestoredRecursorRules.auxiliaryTranslation_of_run hvalid hrun ha Hstep.lookup hmem'
    refine ⟨target, ?_⟩
    have h := Hty.2.1
    rw [← Hstep.restored.produced] at h
    exact h

/-- **Realization of a restored generated equation.** In the final abstract
environment of an assembly shape in which the stripped output environment is
valid and the restorable names are fresh, the abstract restoration of the
`k`-th generated equation realizes the executable restored rule at `k`. -/
theorem NestedValidatedRunResult.restoredRuleRealization_of_equation
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
    (hparamsSize : result.params.size = result.nparams)
    (D : RestorationTableData sourceDecl auxiliaries result E.loweredEnv
      (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 lparams)
    (hscoped : (compilationRestoration sourceDecl auxiliaries).Scoped)
    (C : NestedFinalAssemblyShape E.restoration
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe))
    (hC : C.production = E.production)
    (hvalid : CheckingEnv.Valid (if isUnsafe then .unsafe else .safe)
      (Lean4Lean.stripRecursorRules outEnv
        (Lean4Lean.restoredRecursorNames
          (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 sourceTypes
          (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).1)) C.finalBaseVEnv)
    {X : List Name}
    (Hfresh : ∀ n ∈ (compilationRestoration sourceDecl auxiliaries).restorableNames,
      n ∉ X → C.finalBaseVEnv.constants n = none)
    (HL : E.LoweredRulesAvoid E.auxHeads X)
    (k : Fin E.production.production.generationSignature.constructors.size)
    {rule : VDefEq}
    (hrule : (compilationRestoration sourceDecl auxiliaries).equation
      (E.production.production.canonicalGeneration.equation k) = some rule) :
    E.RestoredRuleRealization (compilationRestoration sourceDecl auxiliaries)
      C.finalBaseVEnv k rule := by
  let P := E.production.production
  have hwf : sourceProdEnv.constants.WF := (wf.tr (safety := .safe)).map_wf
  have hinfos := E.restoredRecursorEntryInfos C hC wf Hsources hadded Haux Hexpansion
    hnodup hparamsSize D hscoped hwf
  let owner := P.generationSignature.constructors[k].owner
  obtain ⟨entry, -, s, t, Hstep, -, -, -⟩ :=
    Lean4Lean.List.Forall₂.forall_exists_l hinfos owner (List.mem_finRange owner)
  obtain ⟨hi, hinfo⟩ := E.generatedEntryOfStep owner Hstep
  have hmap := P.ownedConstructors_map_val owner hi
  have hmem : k ∈ P.generationSignature.ownedConstructors owner := by
    simp [InductiveSignature.ownedConstructors, owner]
  obtain ⟨j, hj, hjk⟩ := List.getElem_of_mem hmem
  have hval := RuleAssembly.getElem_of_map_val_eq hmap j hj
  rw [hjk] at hval
  have hlenOwned : (P.generationSignature.ownedConstructors owner).length =
      Hstep.oldInfo.rules.length := by
    have h := congrArg List.length hmap
    simp only [List.length_map, List.length_range'] at h
    rw [h, hinfo]
  have hjNew : j < Hstep.restored.newInfo.rules.length := by
    rw [Hstep.restored.restoration.rules.length, ← hlenOwned]
    exact hj
  have hnames := E.recursorNames_order C.sourceNonempty
  have hn : P.canonicalGeneration.recursorName owner ∈
      sourceTypes.map (fun t => Lean.mkRecName t.name) ++
        (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).1 := by
    rw [← hnames]
    exact List.mem_map_of_mem (List.mem_finRange owner)
  obtain ⟨target, Ht⟩ := E.restoredRuleRhs_translation hvalid hn Hstep j hjNew
  have hheads : (compilationRestoration sourceDecl auxiliaries).heads.map (·.auxiliary) =
      E.auxHeads := by
    rw [compilationRestoration_heads_auxiliary]
    exact auxiliarySpecializations_headNames Haux Hexpansion
  have hrhs := E.restoredRuleRhs_of_trail wf Hsources hheads hparamsSize D hscoped Hfresh
    owner Hstep (fun rule hrule => by
      rw [hheads]; exact HL owner Hstep.oldInfo Hstep.lookup rule hrule) j hjNew k hval Ht
  obtain ⟨huvars, hlhs, hrhs', htype⟩ := Restoration.equation_eq_some hrule
  have htarget : target = rule.rhs := Option.some.inj (hrhs.symm.trans hrhs')
  subst htarget
  exact ⟨owner, j, s, t, Hstep, hjNew, hval, huvars, Ht, hlhs, htype⟩

/-! ### Rule counts along the traces -/

theorem RestoredPrimaryIotaRuleTrace.ctors_length
    {decl : VInductDecl} {block : VInductBlock} {owner : VInductiveType}
    {result : Lean4Lean.ElimNestedInductive.Result} {prodEnv : Environment}
    {P : NestedInstalledProduction prodEnv} {targetVEnv : VEnv} {auxRec : NameMap Name}
    {oldRecName newRecName : Name} {oldRules newRules : List RecursorRule}
    {Hrules : RulesRestoration result prodEnv auxRec oldRecName newRecName oldRules newRules}
    {ctors : List VConstVal} {rules : List VDefEq}
    (H : RestoredPrimaryIotaRuleTrace decl block owner result prodEnv P targetVEnv auxRec
      oldRecName newRecName Hrules ctors rules) :
    ctors.length = oldRules.length := by
  induction H with
  | nil => rfl
  | cons _ _ _ _ _ _ ih => simp [ih]

/-- Family by family, the number of constructors of a primary owner is the
number of rules of the lowered recursor of its restoration step. -/
theorem RestoredPrimaryIotaSemanticTrace.familyCounts
    {decl : VInductDecl} {block : VInductBlock} {targetVEnv : VEnv}
    {lparams : List Name} {safety : DefinitionSafety}
    {sourceVEnv envTypes envCtors : VEnv}
    {result : Lean4Lean.ElimNestedInductive.Result}
    {loweredEnv : Environment} {P : NestedInstalledProduction loweredEnv}
    {auxRec : NameMap Name} {allIndNames : List Name}
    {sourceTypes : List InductiveType} {sourceProdEnv targetProdEnv : Environment}
    {Htrace : StateForMTrace
      (RestoredInductiveStep result loweredEnv auxRec allIndNames)
      sourceTypes sourceProdEnv targetProdEnv}
    {owners : List VInductiveType} {recursors : List VConstVal}
    {Hsource : RestoredSourceInductiveSemanticTrace decl lparams safety sourceVEnv
      envTypes envCtors Htrace owners recursors}
    {owners' : List VInductiveType} {rules : List VDefEq}
    (H : RestoredPrimaryIotaSemanticTrace decl block targetVEnv P Hsource owners' rules) :
    List.Forall₂ (fun (indType : InductiveType) (owner : VInductiveType) =>
      ∃ (s m : Environment) (Hstep : RestoredInductiveStep result loweredEnv auxRec
          allIndNames indType s m),
        owner.ctors.length = Hstep.restored.recursor.oldInfo.rules.length)
      sourceTypes owners' := by
  induction H with
  | nil => exact .nil
  | cons Hstep Htail Hheader Hconstructors Hrecursor Hrest Hhead Hrules ih =>
    exact .cons ⟨_, _, Hstep, Hhead.ctors_length⟩ ih

/-- The number of rules accumulated by an auxiliary shape trace. -/
theorem RestoredAuxiliaryShapeTrace.rulesLength_eq
    {decl : VInductDecl} {block : VInductBlock} {main : VInductiveType}
    {safety : DefinitionSafety} {trEnv : VEnv}
    {result : Lean4Lean.ElimNestedInductive.Result}
    {loweredEnv : Environment} {auxRec : NameMap Name} {allIndNames : List Name}
    {names : List Name} {sourceEnv targetEnv : Environment}
    {Htrace : StateForMTrace
      (RestoredRecursorStep result loweredEnv auxRec allIndNames)
      names sourceEnv targetEnv}
    {priorRecursors finalRecursors : List VConstVal}
    {priorRules finalRules : List VDefEq}
    (H : RestoredAuxiliaryShapeTrace decl block main safety trEnv Htrace
      priorRecursors priorRules finalRecursors finalRules)
    {counts : List Nat}
    (Hc : List.Forall₂ (fun (name : Name) (c : Nat) =>
      ∀ (s t : Environment) (Hstep : RestoredRecursorStep result loweredEnv auxRec
        allIndNames name s t), Hstep.restored.newInfo.rules.length = c) names counts) :
    finalRules.length = priorRules.length + counts.sum := by
  induction H generalizing counts with
  | nil => cases Hc; simp
  | cons Hstep Htail Hsemantic Hrest ih =>
    cases Hc with
    | cons hc Hc =>
      rw [ih Hc, List.length_append, Hsemantic.rulesLength, hc _ _ Hstep]
      simp only [List.sum_cons]
      omega

/-! ### Owned-constructor enumeration by offsets -/

theorem offsets_mono {α : Type _} (cs : List α) (len : α → Nat) (O : Nat → Nat)
    (hO : ∀ i (hi : i < cs.length), O (i + 1) = O i + len cs[i]) :
    ∀ i j, i ≤ j → j ≤ cs.length → O i ≤ O j := by
  intro i j hij hj
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hij
  induction d with
  | zero => exact Nat.le_refl _
  | succ d ih =>
    have h1 := hO (i + d) (by omega)
    have h2 := ih (by omega) (by omega)
    rw [← Nat.add_assoc, h1]
    omega

/-- Enumerate the owned constructors of a list of owners against a list of
rules, given the owners' rule offsets. -/
theorem forall₂_ownedConstructorsFor_offsets {β : Type _}
    {R : VInductiveType × VConstVal → β → Prop} :
    ∀ (owners : List VInductiveType) (rules : List β) (O : Nat → Nat),
      O 0 = 0 →
      (∀ i (hi : i < owners.length), O (i + 1) = O i + owners[i].ctors.length) →
      rules.length = O owners.length →
      (∀ i (hi : i < owners.length) j (hj : j < owners[i].ctors.length)
        (hk : O i + j < rules.length), R (owners[i], owners[i].ctors[j]) rules[O i + j]) →
      List.Forall₂ R (ownedConstructorsFor owners) rules
  | [], rules, O, h0, _, hlen, _ => by
    simp only [List.length_nil, h0] at hlen
    rw [List.eq_nil_of_length_eq_zero hlen]
    exact .nil
  | o :: os, rules, O, h0, hO, hlen, H => by
    have hsplit : ownedConstructorsFor (o :: os) =
        o.ctors.map (o, ·) ++ ownedConstructorsFor os := rfl
    rw [hsplit]
    have hO1 : O 1 = o.ctors.length := by
      have := hO 0 (by simp)
      simpa [h0] using this
    have hmono := offsets_mono (o :: os) (·.ctors.length) O hO
    have hge : ∀ i, i ≤ os.length → o.ctors.length ≤ O (i + 1) := by
      intro i hi
      rw [← hO1]
      exact hmono 1 (i + 1) (by omega) (by simp; omega)
    have hlenc : o.ctors.length ≤ rules.length := by
      have := hge os.length (Nat.le_refl _)
      rw [hlen]; simpa using this
    rw [← List.take_append_drop o.ctors.length rules]
    refine (Lean4Lean.List.Forall₂.append_of_left (by simp; omega)).mpr ⟨?_, ?_⟩
    · apply Lean4Lean.List.forall₂_of_getElem (by simp; omega)
      intro j hj hj'
      simp only [List.getElem_map, List.getElem_take]
      have hj0 : j < o.ctors.length := by simpa using hj
      have := H 0 (by simp) j hj0 (by rw [h0]; omega)
      simpa [h0] using this
    · apply forall₂_ownedConstructorsFor_offsets os _
        (fun i => O (i + 1) - o.ctors.length)
      · simp [hO1]
      · intro i hi
        have h1 := hO (i + 1) (by simp; omega)
        have h2 := hge i (by omega)
        simp only [List.getElem_cons_succ] at h1
        omega
      · simp only [List.length_drop, hlen, List.length_cons]
      · intro i hi j hj hk
        have h2 := hge i (by omega)
        simp only [List.getElem_drop]
        have hidx : o.ctors.length + (O (i + 1) - o.ctors.length + j) = O (i + 1) + j := by
          omega
        have := H (i + 1) (by simp; omega) j (by simpa using hj)
          (by simp only [List.length_drop] at hk; omega)
        simp only [List.getElem_cons_succ] at this
        simp only [hidx]
        exact this

/-! ### Rule counts and guardedness of the restored rules -/

theorem NestedValidatedRunResult.stepRules_length
    {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceEnv : VEnv} {sourceDecl : VInductDecl} {lparams : List Name}
    {nparams : Nat} {isUnsafe : Bool} {safety : DefinitionSafety}
    {outEnv : Environment}
    (E : NestedValidatedRunResult result sourceProdEnv sourceTypes sourceEnv
      sourceDecl lparams nparams isUnsafe safety outEnv)
    (owner : Fin E.production.production.generationSignature.families.size)
    {auxRec : NameMap Name} {allIndNames : List Name} {nm : Name} {s t : Environment}
    (Hs : RestoredRecursorStep result E.loweredEnv auxRec allIndNames nm s t)
    (hnm : nm = E.production.production.canonicalGeneration.recursorName owner) :
    Hs.oldInfo.rules.length = E.production.indTypes[owner.val]!.ctors.length ∧
      Hs.restored.newInfo.rules.length = E.production.indTypes[owner.val]!.ctors.length := by
  subst hnm
  obtain ⟨hi, hinfo⟩ := E.generatedEntryOfStep owner Hs
  have h := (E.production.production.generated.entry owner.val hi).rules.length
  rw [hinfo] at h
  exact ⟨h, Hs.restored.restoration.rules.length.trans h⟩

/-- The right-hand side of a restored auxiliary rule is guarded for the
restored recursor names (the rule validator). -/
theorem NestedValidatedRunResult.restoredRuleRhs_guarded
    {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}
    (E : NestedValidatedRunResult result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    {venv : VEnv}
    (hvalid : CheckingEnv.Valid (if isUnsafe then .unsafe else .safe)
      (Lean4Lean.stripRecursorRules outEnv
        (Lean4Lean.restoredRecursorNames
          (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 sourceTypes
          (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).1)) venv)
    {recName : Name}
    (hrecName : recName ∈ (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).1)
    {s t : Environment}
    (Hstep : RestoredRecursorStep result E.loweredEnv
      (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2
      (sourceTypes.map (·.name)) recName s t)
    (j : Nat) (hj : j < Hstep.restored.newInfo.rules.length) {target : VExpr}
    (Ht : TrExprS venv Hstep.restored.newInfo.levelParams []
      (Hstep.restored.newInfo.rules[j]'hj).rhs target) :
    target.GuardedRuleRhs
      ((sourceTypes.map (·.name)).map (fun name =>
          let oldName := Lean.mkRecName name
          (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2.getD oldName oldName) ++
        (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).1.map fun oldName =>
          (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2.getD oldName oldName) := by
  have hrun := E.recursorRuleValidation
  obtain ⟨rule, hrule⟩ : ∃ rule, Hstep.restored.newInfo.rules[j]'hj = rule := ⟨_, rfl⟩
  rw [hrule] at Ht
  have hmem : rule ∈ Hstep.restored.newInfo.rules := hrule ▸ List.getElem_mem hj
  rw [Hstep.restored.produced] at hmem Ht
  obtain ⟨_, _, abstractRule, -, Hrhs, -, -, -, -, Hguard⟩ :=
    validateRestoredRecursorRules.auxiliaryValidatedAbstractRule_of_run hvalid hrun hrecName
      Hstep.lookup hmem
  rw [Ht.uniqueS Hrhs]
  exact Hguard

/-- Offsets telescope: the rule counts of a run of consecutive families sum
to the difference of their offsets. -/
theorem recursorMinorOffset_sum (indTypes : Array InductiveType) (p : Nat) :
    ∀ m, p + m ≤ indTypes.size →
      ((List.range m).map (fun a => indTypes[p + a]!.ctors.length)).sum =
        recursorMinorOffset indTypes (p + m) - recursorMinorOffset indTypes p
  | 0, _ => by simp
  | m + 1, h => by
    rw [List.range_succ, List.map_append, List.sum_append,
      recursorMinorOffset_sum indTypes p m (by omega)]
    have hstep := recursorMinorOffset_step indTypes (p + m) (by omega)
    have hmono := recursorMinorOffset_mono indTypes p (p + m) (by omega) (by omega)
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
    rw [← Nat.add_assoc, hstep]
    omega

theorem stepValues_names {result : Lean4Lean.ElimNestedInductive.Result}
    {loweredEnv : Environment} {auxRec : NameMap Name} {allIndNames : List Name}
    {env : VEnv} :
    ∀ {names : List Name} {added : List VConstVal},
      List.Forall₂ (fun (name : Name) (w : VConstVal) =>
        ∃ (s t : Environment) (Hstep : RestoredRecursorStep result loweredEnv
          auxRec allIndNames name s t), RestoredRecursorStepValue env Hstep w) names added →
      added.map (·.name) = names.map (fun oldName => auxRec.getD oldName oldName)
  | _, _, .nil => rfl
  | _, _, .cons h t => by
    obtain ⟨_, _, Hstep, hname, -, -⟩ := h
    simp only [List.map_cons, stepValues_names t, hname, Hstep.restored.mappedName]

/-! ### The restored generated equation of a source constructor -/

theorem VExpr.wrapLams_inj_of_length :
    ∀ {D₁ D₂ : List VExpr} {b₁ b₂ : VExpr}, D₁.length = D₂.length →
      VExpr.wrapLams D₁ b₁ = VExpr.wrapLams D₂ b₂ → D₁ = D₂ ∧ b₁ = b₂
  | [], [], _, _, _, h => by simpa [VExpr.wrapLams] using h
  | d₁ :: D₁, d₂ :: D₂, _, _, hlen, h => by
    simp only [VExpr.wrapLams, List.foldr_cons] at h
    injection h with hd hb
    obtain ⟨hD, hbody⟩ := VExpr.wrapLams_inj_of_length (by simpa using hlen) hb
    exact ⟨by rw [hd, hD], hbody⟩

private theorem Restoration.expr_wrapLams_eq_RS (r : Restoration) (doms : List VExpr)
    (body : VExpr) :
    r.expr (VExpr.wrapLams doms body) =
      (doms.mapM r.expr).bind fun doms' =>
        (r.expr body).map (VExpr.wrapLams doms') := by
  induction doms with
  | nil => cases hb : r.expr body <;> simp [VExpr.wrapLams, hb]
  | cons d ds ih =>
    change Restoration.expr.go r (.lam d (VExpr.wrapLams ds body)) [] = _
    simp only [Restoration.expr.go, List.mapM_cons]
    rw [← Restoration.expr_eq_go, ← Restoration.expr_eq_go, ih]
    cases hd : r.expr d <;> cases hds : ds.mapM r.expr <;>
      cases hb : r.expr body <;> simp [VExpr.mkApps, VExpr.wrapLams]

theorem Restoration.expr_mkApps_const_of_find_none {r : Restoration} {c : Name}
    {ls : List VLevel} (args : List VExpr)
    (h : r.heads.find? (fun h => h.auxiliary == c) = none) :
    r.expr (VExpr.mkApps (.const c ls) args) =
      (args.mapM r.expr).map fun args' => VExpr.mkApps (.const (r.recursorName c) ls) args' := by
  rw [Restoration.expr_mkApps]
  cases ha : args.mapM r.expr with
  | none => rfl
  | some args' => simp [Restoration.expr.go, h]

/-- The restored generated equation of a constructor whose owner's recursor
name and whose own name are not restoration heads. -/
theorem Restoration.equation_primary_structure {s : InductiveSignature}
    (g : Instance s) (r : Restoration) (k : Fin s.constructors.size) {rule : VDefEq}
    (hrule : r.equation (g.equation k) = some rule)
    (hrec : r.heads.find? (fun h => h.auxiliary ==
      g.recursorName s.constructors[k].owner) = none)
    (hctor : r.heads.find? (fun h => h.auxiliary == s.constructors[k].name) = none) :
    ∃ D idx,
      (g.params ++ g.motives ++ g.minors ++
        insertBinders ((s.fieldTypes s.constructors[k]).map (·.instL g.levels))
          (s.families.size + s.constructors.size)).mapM r.expr = some D ∧
      (s.constructors[k].indices.map fun e =>
        (e.instL g.levels).liftN (s.families.size + s.constructors.size)
          s.constructors[k].fields.length).mapM r.expr = some idx ∧
      rule.lhs = VExpr.wrapLams D (VExpr.mkApps
        (.const (r.recursorName (g.recursorName s.constructors[k].owner))
          (VLevel.params g.uvars))
        (vars (s.params.length + (s.families.size + s.constructors.size))
            s.constructors[k].fields.length ++ idx ++
          [VExpr.mkApps (.const (r.recursorName s.constructors[k].name) g.levels)
            (vars s.params.length
                (s.families.size + s.constructors.size + s.constructors[k].fields.length + 0) ++
              vars s.constructors[k].fields.length 0)])) ∧
      (∃ X, rule.rhs = VExpr.wrapLams D X) ∧
      (∃ T, rule.type = VExpr.wrapForalls D T) := by
  obtain ⟨-, hlhs, hrhs, htype⟩ := Restoration.equation_eq_some hrule
  simp only [Instance.equation, Instance.recursorHead, Instance.constructorApp] at hlhs hrhs htype
  rw [Restoration.expr_wrapLams_eq_RS] at hlhs hrhs
  rw [Restoration.expr_wrapForalls] at htype
  obtain ⟨D, hD, hlhs⟩ := Option.bind_eq_some_iff.mp hlhs
  rw [hD, Option.bind_some] at hrhs htype
  obtain ⟨lb, hlb, hlhs⟩ := Option.map_eq_some_iff.mp hlhs
  obtain ⟨X, -, hX⟩ := Option.map_eq_some_iff.mp hrhs
  obtain ⟨T, -, hT⟩ := Option.map_eq_some_iff.mp htype
  rw [Restoration.expr_mkApps_const_of_find_none _ hrec] at hlb
  obtain ⟨args, hargs, hlb⟩ := Option.map_eq_some_iff.mp hlb
  simp only [List.mapM_append, Restoration.mapM_expr_vars, List.mapM_cons,
    List.mapM_nil, Restoration.expr_mkApps_const_of_find_none _ hctor] at hargs
  simp only [bind, pure, Option.bind_some, Option.map_some] at hargs
  obtain ⟨pre, hpre, hargs⟩ := Option.bind_eq_some_iff.mp hargs
  obtain ⟨idx, hidx, hpre⟩ := Option.bind_eq_some_iff.mp hpre
  refine ⟨D, idx, hD, hidx, ?_, ⟨X, hX.symm⟩, ⟨T, hT.symm⟩⟩
  rw [← hlhs, ← hlb]
  simp only [Option.some.injEq] at hargs hpre
  rw [← hargs, ← hpre]

/-! ### Helpers for the restored primary equations -/

/-- The data of a source semantic trace at one family position. -/
theorem RestoredSourceInductiveSemanticTrace.at
    {decl : VInductDecl} {lparams : List Name} {safety : DefinitionSafety}
    {sourceVEnv envTypes envCtors : VEnv}
    {result : Lean4Lean.ElimNestedInductive.Result}
    {loweredEnv : Environment} {auxRec : NameMap Name} {allIndNames : List Name}
    {types : List InductiveType} {sourceProdEnv targetProdEnv : Environment}
    {Htrace : StateForMTrace
      (RestoredInductiveStep result loweredEnv auxRec allIndNames)
      types sourceProdEnv targetProdEnv}
    {owners : List VInductiveType} {recursors : List VConstVal}
    (H : RestoredSourceInductiveSemanticTrace decl lparams safety sourceVEnv
      envTypes envCtors Htrace owners recursors) :
    ∀ (f : Nat) (hf : f < types.length), ∃ (ho : f < owners.length)
      (hr : f < recursors.length) (s m : Environment)
      (Hstep : RestoredInductiveStep result loweredEnv auxRec allIndNames types[f] s m)
      (Hrecursor : RestoredPrimaryRecursorSemantics decl owners[f] safety
        Hstep.restored.recursor envCtors),
      Nonempty (RestoredSourceConstructorTrace result loweredEnv lparams safety envTypes
        Hstep.oldInfo.ctors Hstep.restored.headerEnv Hstep.restored.constructorEnv
        types[f].ctors owners[f].ctors) ∧
      Hrecursor.recursor = recursors[f] := by
  induction H with
  | nil => intro f hf; simp at hf
  | cons Hstep Htail Hheader Hconstructors Hrecursor Hrest ih =>
    intro f hf
    cases f with
    | zero => exact ⟨by simp, by simp, _, _, Hstep, Hrecursor, ⟨Hconstructors⟩, rfl⟩
    | succ f =>
      obtain ⟨ho, hr, s, m, Hs, Hr, Hc, heq⟩ := ih f (by simpa using hf)
      exact ⟨by simpa using ho, by simpa using hr, s, m, Hs, Hr, Hc, heq⟩

theorem RestoredRecursorStep.info_eq'
    {result : Lean4Lean.ElimNestedInductive.Result} {loweredEnv : Environment}
    {auxRec : NameMap Name} {allIndNames : List Name} {n₁ n₂ : Name}
    {s₁ t₁ s₂ t₂ : Environment}
    (H₁ : RestoredRecursorStep result loweredEnv auxRec allIndNames n₁ s₁ t₁)
    (H₂ : RestoredRecursorStep result loweredEnv auxRec allIndNames n₂ s₂ t₂)
    (hn : n₁ = n₂) :
    H₁.oldInfo = H₂.oldInfo ∧ H₁.restored.newInfo = H₂.restored.newInfo := by
  subst hn
  exact H₁.info_eq H₂

theorem InductiveSignature.declaration_ctors_names (s : InductiveSignature)
    (f : Fin s.families.size) (h : f.val < s.declaration.types.length) :
    (s.declaration.types[f.val]'h).ctors.map (·.name) =
      (s.ownedConstructors f).map (fun i => s.constructors[i].name) := by
  simp only [InductiveSignature.declaration, List.getElem_map, List.getElem_zipIdx,
    InductiveSignature.ownedConstructors]
  rw [List.map_filterMap]
  have : s.constructors.toList =
      (List.finRange s.constructors.size).map (fun i => s.constructors[i]) := by
    apply List.ext_getElem <;> simp
  rw [this, List.filterMap_map]
  induction (List.finRange s.constructors.size) with
  | nil => rfl
  | cons i l ih =>
    rw [List.filterMap_cons, List.filter_cons, ih]
    simp only [Function.comp, Nat.zero_add, Fin.getElem_fin]
    by_cases hi : (s.constructors[i.val]).owner = f
    · simp [hi]
    · have : ¬ (s.constructors[i.val].owner.val = f.val) := fun h' => hi (Fin.ext h')
      simp [this, hi]

theorem vars_take (n m k : Nat) :
    (vars (n + m) k).take n = vars n (k + m) := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.getElem_take, vars, List.getElem_map, List.getElem_reverse,
      List.getElem_range, List.length_range]
    congr 1
    simp only [vars, List.length_map, List.length_reverse, List.length_range] at h2
    omega

theorem vars_canonicalRuleFieldVars (n : Nat) :
    vars n 0 = (Lean4Lean.validateRestoredRecursorRules.canonicalRuleFieldVars n).map
      VExpr.bvar := by
  apply List.ext_getElem
  · simp [Lean4Lean.validateRestoredRecursorRules.canonicalRuleFieldVars]
  · intro i h1 h2
    simp [vars, Lean4Lean.validateRestoredRecursorRules.canonicalRuleFieldVars]

theorem Restoration.find_none_of_mem_prefix {r : Restoration} {types : List VInductiveType}
    {p : Nat} (hheads : r.heads.map (·.auxiliary) = familyNames (types.drop p))
    (hnodup : (familyNames types).Nodup) {n : Name} (hn : n ∈ familyNames (types.take p)) :
    r.heads.find? (fun h => h.auxiliary == n) = none := by
  apply List.find?_eq_none.mpr
  intro h hh heq
  have heq' : h.auxiliary = n := by simpa using heq
  have hmem : h.auxiliary ∈ familyNames (types.drop p) := by
    rw [← hheads]; exact List.mem_map_of_mem hh
  have hsplit : familyNames types = familyNames (types.take p) ++ familyNames (types.drop p) := by
    simp only [familyNames, ← List.flatMap_append, List.take_append_drop]
  rw [hsplit] at hnodup
  exact (List.nodup_append.mp hnodup).2.2 _ hn _ hmem heq'.symm

/-! ### The restored primary equations are nested iota rules -/

theorem NestedFinalAssemblyShape.recursors_names
    {result : Lean4Lean.ElimNestedInductive.Result}
    {loweredEnv sourceProdEnv : Environment} {auxRec : NameMap Name}
    {allIndNames : List Name} {sourceTypes : List InductiveType}
    {auxRecNames : List Name} {outEnv : Environment}
    {H : RestoredNestedDeclarationsResult result loweredEnv sourceProdEnv
      auxRec allIndNames sourceTypes auxRecNames ((), outEnv)}
    {sourceEnv : VEnv} {decl : VInductDecl} {lparams : List Name}
    {nparams : Nat} {isUnsafe : Bool} {safety : DefinitionSafety}
    (C : NestedFinalAssemblyShape H sourceEnv decl lparams nparams isUnsafe safety) :
    (C.primaryRecursors ++ C.auxiliaryRecursors).map (·.name) =
      sourceTypes.map (fun indType =>
        let oldName := Lean.mkRecName indType.name
        auxRec.getD oldName oldName) ++
      auxRecNames.map (fun oldName => auxRec.getD oldName oldName) := by
  obtain ⟨added, hadded', Hadded⟩ := C.auxiliarySemantics.recursorSteps
  simp only [List.nil_append] at hadded'
  rw [List.map_append, C.sourceSemantics.recursorNames, hadded', stepValues_names Hadded]

/-- The canonical left-hand-side spine of a restored generated primary equation. -/
def canonicalPrimaryLhsSpine_ofRestored {recInfo : RecursorVal} {rule : RecursorRule}
    {plan : Lean4Lean.validateRestoredRecursorRules.EquationLhsPlan} {D : List VExpr}
    (np nfam nctors nf : Nat) (recName ctorName : Name) (ls levels : List VLevel)
    (idx : List VExpr)
    (hname : recName = recInfo.name) (hctor : ctorName = rule.ctor)
    (hrl : ls.length = recInfo.levelParams.length)
    (hcl : levels.length = plan.ctorLevels.length)
    (hnp : recInfo.numParams = np)
    (hmm : recInfo.numMotives + recInfo.numMinors = nfam + nctors)
    (hidx : idx.length = plan.indices.size) (hnf : rule.nfields = nf) :
    validateRestoredRecursorRules.CanonicalPrimaryLhsSpine recInfo rule plan D
      (VExpr.mkApps (.const recName ls)
        (vars (np + (nfam + nctors)) nf ++ idx ++
          [VExpr.mkApps (.const ctorName levels)
            (vars np (nfam + nctors + nf + 0) ++ vars nf 0)])) where
  recursorLevels := ls
  leadingArgs := vars (np + (nfam + nctors)) nf ++ idx
  ctorLevels := levels
  ctorArgs := vars np (nfam + nctors + nf + 0) ++ vars nf 0
  lhs_pattern := by rw [hname, hctor, List.append_assoc]
  recursor_levels := hrl
  ctor_levels := hcl
  leading_arity := by
    simp only [List.length_append, vars_length', ← hidx]
    omega
  constructor_arity := by
    simp only [List.length_append, vars_length', hnp, hnf]
  parameter_args := by
    rw [hnp, List.take_append_of_le_length (by simp), List.take_append_of_le_length (by simp)]
    rw [List.take_of_length_le (by simp), vars_take]
    congr 1
    omega
  field_args := by
    rw [hnp, List.drop_append_of_le_length (by simp)]
    rw [List.drop_of_length_le (by simp), List.nil_append, hnf]
    exact vars_canonicalRuleFieldVars _

set_option maxHeartbeats 4000000 in
/-- **The restored generated equation of a source constructor is a nested
iota rule** of the restored block of a final assembly shape (in whose final
abstract environment the stripped output environment is valid), for the
source owner and constructor at its position. Its right-hand side is the rule
validator's (by uniqueness of translation), so the right-hand-side clauses
are those of the validator's equation; the left-hand side and type clauses
are computed from the generator. -/
theorem NestedValidatedRunResult.primaryNestedIotaRule
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
    (hparamsSize : result.params.size = result.nparams)
    (D : RestorationTableData sourceDecl auxiliaries result E.loweredEnv
      (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 lparams)
    (hscoped : (compilationRestoration sourceDecl auxiliaries).Scoped)
    (C : NestedFinalAssemblyShape E.restoration
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe))
    (hC : C.production = E.production)
    (hvalid : CheckingEnv.Valid (if isUnsafe then .unsafe else .safe)
      (Lean4Lean.stripRecursorRules outEnv
        (Lean4Lean.restoredRecursorNames
          (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 sourceTypes
          (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).1)) C.finalBaseVEnv)
    {X : List Name}
    (Hfresh : ∀ n ∈ (compilationRestoration sourceDecl auxiliaries).restorableNames,
      n ∉ X → C.finalBaseVEnv.constants n = none)
    (HL : E.LoweredRulesAvoid E.auxHeads X)
    (hcount : ∀ (f : Nat) (hf : f < sourceDecl.types.length),
      (sourceDecl.types[f]'hf).ctors.length = E.production.indTypes[f]!.ctors.length)
    (hauxNames : auxiliaries.map (·.auxiliary) =
      (E.production.loweredDecl.types.drop sourceDecl.types.length).map (·.name))
    (k : Fin E.production.production.generationSignature.constructors.size)
    {rule : VDefEq}
    (hrule : (compilationRestoration sourceDecl auxiliaries).equation
      (E.production.production.canonicalGeneration.equation k) = some rule)
    (f : Nat) (hf : f < sourceDecl.types.length) (j : Nat)
    (hj : j < (sourceDecl.types[f]'hf).ctors.length)
    (hk : k.val = recursorMinorOffset E.production.indTypes f + j) :
    Nonempty (sourceDecl.NestedIotaRule
      (canonicalRestoredShapeBlock sourceDecl C.primaryRecursors C.auxiliaryRecursors)
      (sourceDecl.types[f]'hf) ((sourceDecl.types[f]'hf).ctors[j]'hj) rule) := by
  -- the realization of the rule
  obtain ⟨owner', j', s', t', Hs', hj', hk', huvars, Ht, -, -⟩ :=
    E.restoredRuleRealization_of_equation wf Hsources hadded Haux Hexpansion hnodup
      hparamsSize D hscoped C hC hvalid Hfresh HL k hrule
  have hfamSize : E.production.production.generationSignature.families.size =
      E.production.indTypes.size := by
    rw [← E.production.production.entries_length_eq,
      E.production.production.generated.length,
      E.production.production.recInfos_size_eq_source]
  have hnames := E.recursorNames_order C.sourceNonempty
  have hnamesLen := congrArg List.length hnames
  simp only [List.length_map, List.length_finRange, List.length_append] at hnamesLen
  have hp : (C.main :: C.rest).length = sourceTypes.length :=
    (Lean4Lean.List.Forall₂.length_eq C.primaryIota.familyCounts).symm
  rw [← C.typesSource] at hp
  have hf' : f < sourceTypes.length := by omega
  have hfFam : f < E.production.production.generationSignature.families.size := by
    omega
  have hpSize' : sourceDecl.types.length ≤ E.production.indTypes.size := by omega
  -- the owner and position of the rule
  have hlocal : j < E.production.indTypes[f]!.ctors.length := hcount f hf ▸ hj
  have hlocal' : j' < E.production.indTypes[owner'.val]!.ctors.length :=
    (E.stepRules_length owner' Hs' rfl).2 ▸ hj'
  obtain ⟨howner, hjj⟩ := recursorMinorOffset_unique E.production.indTypes (by omega)
    (by omega) hlocal hlocal' (hk.symm.trans hk')
  subst hjj
  have hown : owner' = ⟨f, hfFam⟩ := Fin.ext howner.symm
  subst hown
  -- the source family
  obtain ⟨ho, hr, s0, m0, Hstep, Hrecursor, ⟨Hcons⟩, hrecEq⟩ := C.sourceSemantics.at f hf'
  have hprimName : Lean.mkRecName (sourceTypes[f]'hf').name =
      E.production.production.canonicalGeneration.recursorName ⟨f, hfFam⟩ := by
    have h := List.getElem_of_eq hnames (i := f) (by simp; omega)
    simp only [List.getElem_map, List.getElem_finRange, List.getElem_append_left
      (as := sourceTypes.map _) (by simpa using hf')] at h
    exact h.symm
  obtain ⟨holdEq, hnewEq⟩ := RestoredRecursorStep.info_eq' Hstep.restored.recursor Hs'
    hprimName
  -- the rule validator at this rule
  have hjOld : j < Hstep.restored.recursor.oldInfo.rules.length := by
    rw [holdEq, (E.stepRules_length ⟨f, hfFam⟩ Hs' rfl).1]; exact hlocal
  have hjNew : j < Hstep.restored.recursor.restored.newInfo.rules.length := by
    rw [Hstep.restored.recursor.restored.restoration.rules.length]; exact hjOld
  have Hexact := validateRestoredRecursorRules.primaryValidatedExactRule_of_run hvalid E.recursorRuleValidation (List.getElem_mem hf') Hstep.restored.recursor.lookup
    (List.getElem_mem hjOld)
  dsimp only at Hexact
  rw [← Hstep.restored.recursor.restored.produced] at Hexact
  have HnewRule : Hstep.restored.recursor.restored.newInfo.rules[j] =
      result.restoreRule E.loweredEnv (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2
        (Lean.mkRecName (sourceTypes[f]'hf').name)
        ((Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2.getD
          (Lean.mkRecName (sourceTypes[f]'hf').name)
          (Lean.mkRecName (sourceTypes[f]'hf').name))
        Hstep.restored.recursor.oldInfo.rules[j] := by
    have HrulesEq : Hstep.restored.recursor.restored.newInfo.rules =
        Hstep.restored.recursor.oldInfo.rules.map
          (result.restoreRule E.loweredEnv (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2
            (Lean.mkRecName (sourceTypes[f]'hf').name)
            ((Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2.getD
              (Lean.mkRecName (sourceTypes[f]'hf').name)
              (Lean.mkRecName (sourceTypes[f]'hf').name))) := by
      simpa only [Lean4Lean.ElimNestedInductive.Result.restoreRecursor] using
        congrArg RecursorVal.rules Hstep.restored.recursor.restored.produced
    apply (List.getElem_eq_iff hjNew).2
    rw [HrulesEq, List.getElem?_map, List.getElem?_eq_getElem hjOld]
    rfl
  rw [← HnewRule] at Hexact
  rcases Hexact with
    ⟨_lhs, _lhsInferred, _residual, _plan, _canonicalPlan, domains, _lhsBody,
      rhsBody, _typeBody, abstractRule, _Hbuild, _Hplan, _Hindices,
      _HctorUvars, _Hprefix, _Hcanonical, Hrhs, _Hlhs, _HruleUvars,
      _, _Htelescope, _hresidual, hdomains, _HlhsWrapped,
      HrhsWrapped, _HtypeWrapped, Hguard, _, shape, ⟨HrhsSpine⟩⟩
  -- the right-hand side is the validator's
  have Ht' : TrExprS C.finalBaseVEnv Hstep.restored.recursor.restored.newInfo.levelParams []
      (Hstep.restored.recursor.restored.newInfo.rules[j]'hjNew).rhs rule.rhs := by
    have key : ∀ (info : RecursorVal) (h : j < info.rules.length),
        info = Hs'.restored.newInfo →
        TrExprS C.finalBaseVEnv info.levelParams [] (info.rules[j]'h).rhs rule.rhs := by
      intro info h hinfo
      subst hinfo
      exact Ht
    exact key _ hjNew hnewEq
  have hrhsEq : abstractRule.rhs = rule.rhs := Hrhs.uniqueS Ht'
  -- the generated constructor
  have hkOwner : E.production.production.generationSignature.constructors[k].owner =
      ⟨f, hfFam⟩ := by
    apply Fin.ext
    have h := E.production.production.generatedConstructor_owner f (by omega) j
      hlocal (hk ▸ k.isLt)
    simp only [Fin.getElem_fin, hk]
    exact h
  have hi : f < E.production.production.entries.length := by
    rw [E.production.production.entries_length_eq]; exact hfFam
  have hmap := E.production.production.ownedConstructors_map_val ⟨f, hfFam⟩ hi
  have hjOwned : j < (E.production.production.generationSignature.ownedConstructors
      ⟨f, hfFam⟩).length := by
    have h := congrArg List.length hmap
    simp only [List.length_map, List.length_range'] at h
    rw [h, (E.production.production.generated.entry f hi).rules.length]
    exact hlocal
  have hownedJ : (E.production.production.generationSignature.ownedConstructors
      ⟨f, hfFam⟩)[j] = k := by
    apply Fin.ext
    rw [RuleAssembly.getElem_of_map_val_eq hmap j hjOwned, hk]
  -- constructor names
  have hloweredDecl : C.formationAssembly.expanded = E.production.loweredDecl := by
    rw [C.formationExpanded, hC]
  have HT := C.formationAssembly.types
  rw [hloweredDecl] at HT
  have hlenHT := Lean4Lean.List.Forall₂.length_eq HT
  simp only [List.length_append] at hlenHT
  have hfLow : f < E.production.loweredDecl.types.length := by omega
  have HTf := Lean4Lean.List.forall₂_getElem HT f (by simp; omega) hfLow
  rw [List.getElem_append_left hf] at HTf
  have HM := E.production.loweredConstruction.consumedGeneration.models.families
  have hlenHM := Lean4Lean.List.Forall₂.length_eq HM
  have hfDecl : f < E.production.compilationSignature.declaration.types.length := by
    have h : f < E.production.compilationSignature.families.size := hfFam
    simpa [InductiveSignature.declaration] using h
  have HMf := Lean4Lean.List.forall₂_getElem HM f hfDecl hfLow
  have hjLow : j < (E.production.loweredDecl.types[f]'hfLow).ctors.length := by
    rw [← Lean4Lean.List.Forall₂.length_eq HTf.constructors]; exact hj
  have hctorNameSrc : ((sourceDecl.types[f]'hf).ctors[j]'hj).name =
      E.production.production.generationSignature.constructors[k].name := by
    have h1 := (Lean4Lean.List.forall₂_getElem HTf.constructors j hj hjLow).name
    have h2 := HMf.2.2.2.2
    have h3 := InductiveSignature.declaration_ctors_names
      E.production.production.generationSignature ⟨f, hfFam⟩ hfDecl
    have h4 := List.getElem_of_eq (h3.symm.trans h2) (i := j) (by simpa using hjOwned)
    simp only [List.getElem_map, hownedJ] at h4
    rw [← h1, ← h4]
  have hctorLow : ((E.production.loweredDecl.types[f]'hfLow).ctors[j]'hjLow).name =
      E.production.production.generationSignature.constructors[k].name := by
    rw [← hctorNameSrc]
    exact (Lean4Lean.List.forall₂_getElem HTf.constructors j hj hjLow).name
  -- names of the source family are not restoration heads
  have hheadsAux : (compilationRestoration sourceDecl auxiliaries).heads.map (·.auxiliary) =
      familyNames (E.production.loweredDecl.types.drop sourceDecl.types.length) := by
    rw [compilationRestoration_heads_auxiliary]
    exact auxiliarySpecializations_headNames Haux Hexpansion
  have hnodupFam : (familyNames E.production.loweredDecl.types).Nodup :=
    (List.nodup_append.mp hnodup).1
  have hlowMem : E.production.loweredDecl.types[f]'hfLow ∈
      E.production.loweredDecl.types.take sourceDecl.types.length := by
    rw [List.mem_iff_getElem]
    exact ⟨f, by simp; omega, by simp⟩
  have hctorHead : (compilationRestoration sourceDecl auxiliaries).heads.find? (fun h =>
      h.auxiliary ==
        E.production.production.generationSignature.constructors[k].name) = none :=
    Restoration.find_none_of_mem_prefix hheadsAux hnodupFam
      (mem_familyNames.mpr ⟨_, hlowMem, .inr ⟨_, List.getElem_mem hjLow, hctorLow.symm⟩⟩)
  have hfamName : E.production.production.generationSignature.families[f].name =
      (E.production.loweredDecl.types[f]'hfLow).name := by
    have h := HMf.1
    simp only [InductiveSignature.declaration, List.getElem_map, List.getElem_zipIdx] at h
    exact h
  have hfamHead : (compilationRestoration sourceDecl auxiliaries).heads.find? (fun h =>
      h.auxiliary ==
        E.production.production.generationSignature.families[f].name) = none :=
    Restoration.find_none_of_mem_prefix hheadsAux hnodupFam
      (mem_familyNames.mpr ⟨_, hlowMem, .inl hfamName⟩)
  -- the primary recursor is not renamed
  have hrecNames := E.production.loweredConstruction.consumedGeneration.names
  have hnotRec : E.production.production.canonicalGeneration.recursorName ⟨f, hfFam⟩ ∉
      (compilationRestoration sourceDecl auxiliaries).recursors.map Prod.fst := by
    intro hmem
    obtain ⟨pair, hpair, hpairName⟩ := List.mem_map.mp hmem
    obtain ⟨⟨a, i⟩, hai, rfl⟩ := List.mem_map.mp hpair
    have ha : a ∈ auxiliaries := List.fst_mem_of_mem_zipIdx hai
    have hfamName' : E.production.production.generationSignature.families[f].name =
        a.auxiliary := by
      have h := hpairName.trans (hrecNames ⟨f, hfFam⟩)
      exact (Name.str.inj h).1.symm
    have hmemHead : (⟨a.auxiliary, sourceDecl.uvars, sourceDecl.nparams, a.source.name,
        a.levels, a.arguments⟩ : HeadSpecialization) ∈
          (compilationRestoration sourceDecl auxiliaries).heads :=
      List.mem_flatMap.mpr ⟨a, ha, List.mem_cons_self⟩
    have := List.find?_eq_none.mp hfamHead _ hmemHead
    simp only [beq_iff_eq] at this
    exact this (by simpa using hfamName'.symm)
  have hsame : Hstep.restored.recursor.restored.newRecName =
      Lean.mkRecName (sourceTypes[f]'hf').name := by
    rw [Hstep.restored.recursor.restored.mappedName, nameMap_getD_eq, ← D.recursorName,
      hprimName]
    exact Restoration.recursorName_of_not_mem hnotRec
  -- the old and new rule at the position
  have Rj := Hstep.restored.recursor.restored.restoration.rules.entry j hjOld hjNew
  obtain ⟨hi', hinfo⟩ := E.generatedEntryOfStep ⟨f, hfFam⟩ Hs'
  have RR := E.production.production.ruleRealizations
    E.production.production.ruleRhsTranslations ⟨f, hfFam⟩ hi'
  have hjEntry : j < (E.production.production.generated.entry f hi').info.rules.length := by
    rw [hinfo, ← holdEq]; exact hjOld
  have RRj := Lean4Lean.List.forall₂_getElem RR j hjOwned hjEntry
  have hentryEq : (E.production.production.generated.entry f hi').info =
      Hstep.restored.recursor.oldInfo := hinfo.trans holdEq.symm
  have holdRule : (E.production.production.generated.entry f hi').info.rules[j] =
      Hstep.restored.recursor.oldInfo.rules[j] :=
    List.getElem_of_eq (congrArg RecursorVal.rules hentryEq) hjEntry
  have hctorOld : (Hstep.restored.recursor.restored.newInfo.rules[j]'hjNew).ctor =
      (Hstep.restored.recursor.oldInfo.rules[j]'hjOld).ctor := by
    have h := Rj.ctor
    have hb : (Hstep.restored.recursor.restored.newRecName ==
        Lean.mkRecName (sourceTypes[f]'hf').name) = true := by
      rw [hsame]; exact beq_self_eq_true _
    rw [hb, if_pos rfl] at h
    exact h
  have hctorGen : (Hstep.restored.recursor.oldInfo.rules[j]'hjOld).ctor =
      E.production.production.generationSignature.constructors[k].name := by
    have h := RRj.ctor
    rw [holdRule] at h
    rw [h, hownedJ]
  have hnewCtor : (Hstep.restored.recursor.restored.newInfo.rules[j]'hjNew).ctor =
      E.production.production.generationSignature.constructors[k].name :=
    hctorOld.trans hctorGen
  have hnewFields : (Hstep.restored.recursor.restored.newInfo.rules[j]'hjNew).nfields =
      E.production.production.generationSignature.constructors[k].fields.length := by
    have h := RRj.nfields
    rw [holdRule] at h
    rw [Rj.nfields, h, hownedJ]
  -- counts of the restored recursor
  obtain ⟨⟨rtype, hrtype, hrconst⟩, hnumP, hnumI, hnumM, hnumMin⟩ :=
    E.restoredRecursorShapeFields C hC wf Hsources hadded Haux Hexpansion hnodup hparamsSize D
      hscoped ⟨f, hfFam⟩ Hs'
  rw [← hnewEq] at hnumP hnumI hnumM hnumMin hrconst
  have hnp : result.nparams =
      E.production.production.generationSignature.params.length := by
    rw [← E.statsParamsSize]; exact E.production.production.params_size_eq
  have hdeclNp : sourceDecl.nparams =
      E.production.production.generationSignature.params.length :=
    D.nparams.trans hnp
  -- the restored generated equation
  obtain ⟨D0, idx, hD0, hidx, hlhsEq, ⟨X0, hrhsEq0⟩, ⟨T0, htypeEq0⟩⟩ :=
    Restoration.equation_primary_structure _ _ k hrule
      (by rw [hkOwner]; exact E.recursorName_not_head Haux Hexpansion hnodup ⟨f, hfFam⟩)
      hctorHead
  have hD0len : D0.length =
      E.production.production.generationSignature.params.length +
        E.production.production.generationSignature.families.size +
        E.production.production.generationSignature.constructors.size +
        E.production.production.generationSignature.constructors[k].fields.length := by
    rw [← Lean4Lean.List.Forall₂.length_eq (List.mapM_eq_some.mp hD0)]
    simp [InductiveSignature.Instance.params, InductiveSignature.Instance.motives,
      InductiveSignature.Instance.minors, insertBinders, InductiveSignature.fieldTypes]
    omega
  have hidxLen : idx.length =
      E.production.production.generationSignature.constructors[k].indices.length := by
    rw [← Lean4Lean.List.Forall₂.length_eq (List.mapM_eq_some.mp hidx)]
    simp
  have hdomLen : domains.length =
      Hstep.restored.recursor.restored.newInfo.numParams +
        Hstep.restored.recursor.restored.newInfo.numMotives +
        Hstep.restored.recursor.restored.newInfo.numMinors +
        (Hstep.restored.recursor.restored.newInfo.rules[j]'hjNew).nfields :=
    hdomains.trans shape.source_arity |>.trans shape.arity_eq
  have hlenEq : domains.length = D0.length := by
    rw [hdomLen, hD0len, hnumP, hnumM, hnumMin, hnewFields]
  obtain ⟨hdomEq, hbodyEq⟩ := VExpr.wrapLams_inj_of_length hlenEq
    (HrhsWrapped.symm.trans (hrhsEq.trans hrhsEq0))
  subst hdomEq
  subst hbodyEq
  -- the restored recursor of the family
  have howner : (C.main :: C.rest)[f]'ho = sourceDecl.types[f]'hf :=
    List.getElem_of_eq C.typesSource.symm ho
  obtain ⟨S0⟩ := Hrecursor.shape
  have hS0name : Hrecursor.recursor.name = sourceDecl.recursorName (sourceDecl.types[f]'hf) :=
    S0.name.trans (congrArg sourceDecl.recursorName howner)
  have hS0uvars := S0.uvars
  have hrecMemPrim : Hrecursor.recursor ∈ C.primaryRecursors := hrecEq ▸ List.getElem_mem hr
  have hrecMem : Hrecursor.recursor ∈
      (canonicalRestoredShapeBlock sourceDecl C.primaryRecursors C.auxiliaryRecursors).recursors := by
    simp only [canonicalRestoredShapeBlock, canonicalRestoredBlock]
    exact List.mem_append_left _ hrecMemPrim
  have hrecName : Hrecursor.recursor.name = Hstep.restored.recursor.restored.newInfo.name :=
    Hrecursor.name.trans Hstep.restored.recursor.restored.restoration.name.symm
  have hrecUvars : Hrecursor.recursor.uvars =
      Hstep.restored.recursor.restored.newInfo.levelParams.length := by
    rw [Hstep.restored.recursor.restored.restoration.levelParams]; exact Hrecursor.uvars.symm
  have hadd := C.canonical.recursorsAdded.abstract
  rw [C.recursorValues] at hadd
  have hinst := VEnv.addConstVals_get hadd (List.mem_append_left _ hrecMemPrim)
  rw [hrecName, hrconst] at hinst
  have hrecType : Hrecursor.recursor.type = rtype :=
    (congrArg VConstant.type (Option.some.inj hinst)).symm
  obtain ⟨pre, major, hpre, -, htypeEq⟩ := Restoration.expr_recursorType_eq_some _ hrtype
  have hpreLen : pre.length =
      E.production.production.generationSignature.params.length +
        E.production.production.generationSignature.families.size +
        E.production.production.generationSignature.constructors.size +
        (E.production.production.generationSignature.families[f]'hfFam).indices.length := by
    rw [← Lean4Lean.List.Forall₂.length_eq (List.mapM_eq_some.mp hpre)]
    exact Instance.recursorPrefix_length _ _
  -- index counts and universe levels
  have hownerIdx : (sourceDecl.types[f]'hf).numIndices =
      (E.production.production.generationSignature.families[f]'hfFam).indices.length := by
    have h1 := HTf.numIndices
    have h2 := HMf.2.2.1
    simp only [InductiveSignature.declaration, List.getElem_map, List.getElem_zipIdx] at h2
    rw [← h1, ← h2]
    rfl
  have hctorIdx : E.production.production.generationSignature.constructors[k].indices.length =
      (E.production.production.generationSignature.families[f]'hfFam).indices.length := by
    have h := E.production.loweredConstruction.consumedGeneration.models.constructorArity
      _ (Array.getElem_mem_toList k.isLt)
    simp only [Fin.getElem_fin] at hkOwner ⊢
    refine h.trans ?_
    simp only [hkOwner]
    rfl
  have hlevels : E.production.production.canonicalGeneration.levels.length =
      sourceDecl.uvars := by
    have h1 := E.production.loweredConstruction.consumedGeneration.admissible.levels_length
    have h2 := E.production.loweredConstruction.consumedGeneration.models.uvars
    have h3 := C.formationAssembly.uvars
    rw [hloweredDecl] at h3
    exact h1.trans (h2.trans h3)
  -- the nested recursor shape of the restored recursor
  obtain ⟨Lp, Lm, Lmi, Li, Lma, hsplit, hLp, hLm, hLmi, hLi, hLma⟩ :=
    List.exists_append_five_of_length_eq (pre ++ [major])
      E.production.production.generationSignature.params.length
      E.production.production.generationSignature.families.size
      E.production.production.generationSignature.constructors.size
      (E.production.production.generationSignature.families[f]'hfFam).indices.length 1
      (by simp only [List.length_append, List.length_singleton, hpreLen])
  have hownedLen : sourceDecl.ownedConstructors.length ≤
      E.production.production.generationSignature.constructors.size := by
    have hsum : sourceDecl.ownedConstructors.length =
        recursorMinorOffset E.production.indTypes sourceDecl.types.length := by
      rw [← ownedConstructorsFor_eq]
      have key : ∀ (types : List VInductiveType) (f0 : Nat),
          (∀ i (hi : i < types.length), (types[i]'hi).ctors.length =
            E.production.indTypes[f0 + i]!.ctors.length) →
          f0 + types.length ≤ E.production.indTypes.size →
          (ownedConstructorsFor types).length =
            recursorMinorOffset E.production.indTypes (f0 + types.length) -
              recursorMinorOffset E.production.indTypes f0 := by
        intro types
        induction types with
        | nil => intro f0 _ _; simp [ownedConstructorsFor]
        | cons t ts ih =>
          intro f0 hc hle
          have h0 : t.ctors.length = E.production.indTypes[f0]!.ctors.length := by
            have := hc 0 (by simp)
            simp only [List.getElem_cons_zero, Nat.add_zero] at this
            exact this
          have hstep := recursorMinorOffset_step E.production.indTypes f0 (by simp at hle; omega)
          have hrest := ih (f0 + 1) (fun i hi => by
            have := hc (i + 1) (by simp; omega)
            simpa [Nat.add_assoc, Nat.add_comm 1 i] using this) (by simp at hle; omega)
          have hmono := recursorMinorOffset_mono E.production.indTypes (f0 + 1)
            (f0 + 1 + ts.length) (by omega) (by simp at hle; omega)
          have hsplit' : ownedConstructorsFor (t :: ts) =
              t.ctors.map (t, ·) ++ ownedConstructorsFor ts := rfl
          rw [hsplit', List.length_append, List.length_map, hrest]
          simp only [List.length_cons]
          rw [show f0 + (ts.length + 1) = f0 + 1 + ts.length by omega]
          omega
      have := key sourceDecl.types 0 (fun i hi => by simpa using hcount i hi) (by simpa using hpSize')
      simpa [recursorMinorOffset] using this
    rw [hsum, ← E.production.production.constructors_size_offset.symm]
    exact recursorMinorOffset_mono _ _ _ hpSize' (Nat.le_refl _)
  have htype' : Hrecursor.recursor.type = VExpr.wrapForalls (Lp ++ Lm ++ Lmi ++ Li ++ Lma)
      (E.production.production.canonicalGeneration.recursorBody ⟨f, hfFam⟩) := by
    rw [hrecType, htypeEq, hsplit]
  have hresult : E.production.production.canonicalGeneration.recursorBody ⟨f, hfFam⟩ =
      sourceDecl.recursorResultWithCounts f Lm.length Lmi.length (sourceDecl.types[f]'hf) := by
    simp only [Instance.recursorBody, VInductDecl.recursorResultWithCounts, hLm, hLmi,
      hownerIdx, vars]
    congr 1
    · congr 1
      simp only [Fin.getElem_fin]
      omega
    · congr 1
      apply List.map_congr_left
      intro i _
      rw [Nat.add_comm]
  let S1 : sourceDecl.NestedRecursorShape (sourceDecl.types[f]'hf) Hrecursor.recursor :=
    VInductDecl.NestedRecursorShape.ofWrapped hf rfl hS0name hS0uvars
      (by rw [hLp, hdeclNp]) (by rw [hLm]; omega) (by rw [hLmi]; exact hownedLen)
      (by rw [hLi, hownerIdx]) hLma htype' hresult
  -- the restored names in the left-hand side
  have hrecRestored : (compilationRestoration sourceDecl auxiliaries).recursorName
      (E.production.production.canonicalGeneration.recursorName
        E.production.production.generationSignature.constructors[k].owner) =
      Hstep.restored.recursor.restored.newInfo.name :=
    (congrArg (fun o => (compilationRestoration sourceDecl auxiliaries).recursorName
      (E.production.production.canonicalGeneration.recursorName o)) hkOwner).trans
      ((Restoration.recursorName_of_not_mem hnotRec).trans (hprimName.symm.trans
        (hsame.symm.trans Hstep.restored.recursor.restored.restoration.name.symm)))
  have hctorRestored : (compilationRestoration sourceDecl auxiliaries).recursorName
      E.production.production.generationSignature.constructors[k].name =
      (Hstep.restored.recursor.restored.newInfo.rules[j]'hjNew).ctor := by
    rw [hnewCtor]
    apply Restoration.recursorName_of_not_mem
    rw [compilationRestoration_recursors_fst]
    intro hmem
    obtain ⟨a, ha, haName⟩ := List.mem_map.mp hmem
    have haLow : a.auxiliary ∈ E.production.loweredDecl.types.map (·.name) := by
      have h1 : a.auxiliary ∈ auxiliaries.map (·.auxiliary) := List.mem_map_of_mem ha
      rw [hauxNames] at h1
      obtain ⟨t, ht, htn⟩ := List.mem_map.mp h1
      exact List.mem_map.mpr ⟨t, List.mem_of_mem_drop ht, htn⟩
    have hrecMem' : E.production.production.generationSignature.constructors[k].name ∈
        E.production.loweredDecl.types.map (fun t => t.name.str "rec") := by
      obtain ⟨t, ht, htn⟩ := List.mem_map.mp haLow
      rw [← haName, ← htn]
      exact List.mem_map_of_mem ht
    have hfamMem : E.production.production.generationSignature.constructors[k].name ∈
        familyNames E.production.loweredDecl.types :=
      mem_familyNames.mpr ⟨_, List.getElem_mem hfLow, .inr ⟨_, List.getElem_mem hjLow,
        hctorLow.symm⟩⟩
    exact (List.nodup_append.mp hnodup).2.2 _ hfamMem _ hrecMem' rfl
  -- the uvars
  have M := E.recursorMetadataOfStep ⟨f, hfFam⟩ Hs'
  have hguvars : E.production.production.canonicalGeneration.uvars =
      Hstep.restored.recursor.restored.newInfo.levelParams.length := by
    rw [Hstep.restored.recursor.restored.restoration.levelParams, holdEq, M.uvars]
  -- the left-hand side spine
  let plan : Lean4Lean.validateRestoredRecursorRules.EquationLhsPlan := {
    ctorLevels := List.replicate
      E.production.production.canonicalGeneration.levels.length Level.zero
    ctorParams := #[]
    indices := (List.replicate idx.length (default : Expr)).toArray }
  have Hlhs := canonicalPrimaryLhsSpine_ofRestored (plan := plan) (D := domains)
    (rule := Hstep.restored.recursor.restored.newInfo.rules[j]'hjNew)
    E.production.production.generationSignature.params.length
    E.production.production.generationSignature.families.size
    E.production.production.generationSignature.constructors.size
    E.production.production.generationSignature.constructors[k].fields.length
    _ _ (VLevel.params E.production.production.canonicalGeneration.uvars)
    E.production.production.canonicalGeneration.levels idx
    hrecRestored hctorRestored (by simp [VLevel.params, hguvars]) (by simp [plan]) hnumP
    (by rw [hnumM, hnumMin]) (by simp [plan]) hnewFields
  have Hguard' : rhsBody.GuardedIota
      ((canonicalRestoredShapeBlock sourceDecl C.primaryRecursors C.auxiliaryRecursors).recursors.map
        (·.name))
      (Lean4Lean.validateRestoredRecursorRules.recursiveFieldVars
        ((sourceTypes.map (·.name)).map Lean.mkRecName ++
          (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).1)
        (Hstep.restored.recursor.oldInfo.rules[j]'hjOld).rhs) 0 := by
    simp only [canonicalRestoredShapeBlock, canonicalRestoredBlock]
    rw [C.recursors_names]
    simpa [List.map_map, Function.comp_def] using Hguard
  exact ⟨validateRestoredRecursorRules.nestedIotaRule_of_canonicalSpines Hrecursor.recursor
    hrecMem S1 hrecName hrecUvars (hdeclNp.trans hnumP.symm)
    (by show sourceDecl.nparams + Lm.length + Lmi.length = _
        rw [hLm, hLmi, hdeclNp, hnumP, hnumM, hnumMin])
    (by simp [plan, hownerIdx, ← hctorIdx, hidxLen])
    (by simp [plan, hlevels])
    (hctorNameSrc.trans hnewCtor.symm) hdomLen hlhsEq hrhsEq0 htypeEq0
    (huvars.trans hguvars) Hlhs shape HrhsSpine Hguard'⟩

/-! ### The rule-shape hypothesis -/

/-- **The rule-shape hypothesis `HruleShape` of `hrules_of`.** The shape
produced by `assemblyShapeNativeValid` is rebuilt with the restored generated
equations as its rule lists. Everything is derived from the run except:

* `hnested`: the run is a nested one (as in `assemblyShapeNative`);
* `HrestoredWF`: every restored generated equation is well formed in the
  final abstract environment of a final assembly shape of the run in which
  the stripped output environment is valid. -/
theorem NestedValidatedRunResult.hruleShape_of
    {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}
    (E : NestedValidatedRunResult result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (wf : ves.WFCore sourceProdEnv) (Hsources : SourceSyntaxChecks sourceTypes)
    (hnested : result.aux2nested.size ≠ 0)
    (HrestoredWF : ∀ auxiliaries : List ContainerSpecialization,
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
          rule.WF C.finalBaseVEnv) :
    ∀ auxiliaries : List ContainerSpecialization,
      RestorationTableData sourceDecl auxiliaries result E.loweredEnv
        (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 lparams →
      ∃ C : NestedFinalAssemblyShape E.restoration
          (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
          nparams isUnsafe (if isUnsafe then .unsafe else .safe),
        C.production = E.production ∧
        List.Forall₂
          (E.RestoredRuleRealization (compilationRestoration sourceDecl auxiliaries)
            C.finalBaseVEnv)
          (List.finRange E.production.compilationSignature.constructors.size)
          (C.primaryRules ++ C.auxiliaryRules) := by
  intro auxiliaries D
  rcases E.restorationTablesRestoringAll wf Hsources with
    ⟨envTypes, generated, aux', hadded, henvTypes, Haux, Hexpansion, hparamsSize, D', -, -⟩
  have hnodup :
      (familyNames E.production.loweredDecl.types ++
        E.production.loweredDecl.types.map (fun t => t.name.str "rec")).Nodup := by
    rcases E.containerSpecializations wf Hsources with
      ⟨_, _, _, _, _, _, _, h, _⟩
    exact h
  obtain ⟨-, -, hauxNames, -, -, -, -, hscoped, -⟩ :=
    E.restorationPrefix_of wf hadded henvTypes Haux Hexpansion hnodup D' True.intro
  rcases E.assemblyShapeNativeValid wf Hsources hnested with ⟨⟨C₀, hC₀, hV⟩⟩
  have hfresh := fresh_filter_restorable
    (E.finalBaseVEnv_restorableNames_fresh_of_not_renamed wf Hsources C₀ hC₀ D')
  have HL := E.loweredRulesAvoid_renamed wf Hsources Haux Hexpansion D'
  -- the restored generated equations
  have hrecs := E.restoredRecursors_of_hitShape C₀ hC₀ wf Hsources hadded Haux Hexpansion
    hnodup hparamsSize D' hscoped
  have hrecTypes : ∀ owner, ∃ t, (compilationRestoration sourceDecl aux').expr
      (E.production.compilationInstance.recursorType owner) = some t := by
    intro owner
    have Hm := List.mapM_eq_some.mp hrecs
    obtain ⟨v, -, hv⟩ := Lean4Lean.List.Forall₂.forall_exists_l Hm _
      (List.mem_map_of_mem (List.mem_finRange owner))
    simp only [Restoration.recursor, Option.bind_eq_bind, Option.pure_def] at hv
    cases ht : (compilationRestoration sourceDecl aux').expr
        (E.production.compilationInstance.recursor owner).type with
    | none => simp [ht] at hv
    | some t => exact ⟨t, ht⟩
  obtain ⟨rules, hrulesEq⟩ := E.production.compilationInstance.restoredEquations_isSome _
    hrecTypes (fun owner => E.recursorName_not_head Haux Hexpansion hnodup owner)
  have Hrules : List.Forall₂ (fun k rule => (compilationRestoration sourceDecl aux').equation
      (E.production.production.canonicalGeneration.equation k) = some rule)
      (List.finRange E.production.production.generationSignature.constructors.size)
      rules := by
    have h := List.mapM_eq_some.mp hrulesEq
    simp only [InductiveSignature.Instance.equations] at h
    exact (Lean4Lean.List.forall₂_map_left_iff).mp h
  have hlenRules : rules.length =
      E.production.production.generationSignature.constructors.size := by
    have := Lean4Lean.List.Forall₂.length_eq Hrules
    simpa using this.symm
  -- realization, in the canonical and in the given table
  have Hreal : List.Forall₂
      (E.RestoredRuleRealization (compilationRestoration sourceDecl aux') C₀.finalBaseVEnv)
      (List.finRange E.production.production.generationSignature.constructors.size)
      rules :=
    Lean4Lean.List.Forall₂.imp (fun k _ h => E.restoredRuleRealization_of_equation wf Hsources
      hadded Haux Hexpansion hnodup hparamsSize D' hscoped C₀ hC₀ hV hfresh HL k h) Hrules
  have hexpr : ∀ e, (compilationRestoration sourceDecl auxiliaries).expr e =
      (compilationRestoration sourceDecl aux').expr e := D.expr_eq_RS D'
  have Hreal' : List.Forall₂
      (E.RestoredRuleRealization (compilationRestoration sourceDecl auxiliaries)
        C₀.finalBaseVEnv)
      (List.finRange E.production.production.generationSignature.constructors.size)
      rules :=
    Lean4Lean.List.Forall₂.imp (fun _ _ h => by
      obtain ⟨owner, j, s, t, Hstep, hj, hk, hu, Ht, hl, hty⟩ := h
      exact ⟨owner, j, s, t, Hstep, hj, hk, hu, Ht, (hexpr _).trans hl, (hexpr _).trans hty⟩)
      Hreal
  -- families and offsets
  have hnames := E.recursorNames_order C₀.sourceNonempty
  have hfamSize : E.production.production.generationSignature.families.size =
      E.production.indTypes.size := by
    rw [← E.production.production.entries_length_eq,
      E.production.production.generated.length,
      E.production.production.recInfos_size_eq_source]
  have hnamesLen := congrArg List.length hnames
  simp only [List.length_map, List.length_finRange, List.length_append] at hnamesLen
  have Hcounts := C₀.primaryIota.familyCounts
  have hp : (C₀.main :: C₀.rest).length = sourceTypes.length :=
    (Lean4Lean.List.Forall₂.length_eq Hcounts).symm
  rw [← C₀.typesSource] at hp
  have hprimName : ∀ (f : Nat) (hf : f < sourceTypes.length),
      Lean.mkRecName (sourceTypes[f]'hf).name =
        E.production.production.canonicalGeneration.recursorName
          ⟨f, by omega⟩ := by
    intro f hf
    have h := List.getElem_of_eq hnames (i := f) (by simp; omega)
    simp only [List.getElem_map, List.getElem_finRange, List.getElem_append_left
      (as := sourceTypes.map _) (by simpa using hf)] at h
    exact h.symm
  have hauxName : ∀ (a : Nat) (ha : a < (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).1.length),
      (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).1[a] =
        E.production.production.canonicalGeneration.recursorName
          ⟨sourceTypes.length + a, by omega⟩ := by
    intro a ha
    have h := List.getElem_of_eq hnames (i := sourceTypes.length + a) (by simp; omega)
    rw [List.getElem_append_right (by simp)] at h
    simp only [List.getElem_map, List.getElem_finRange, List.length_map,
      Nat.add_sub_cancel_left] at h
    exact h.symm
  -- offsets
  have hOn : recursorMinorOffset E.production.indTypes E.production.indTypes.size =
      E.production.production.generationSignature.constructors.size :=
    E.production.production.constructors_size_offset.symm
  have hpSize : sourceDecl.types.length ≤ E.production.indTypes.size := by omega
  have hOp : recursorMinorOffset E.production.indTypes sourceDecl.types.length ≤
      E.production.production.generationSignature.constructors.size := by
    rw [← hOn]
    exact recursorMinorOffset_mono _ _ _ hpSize (Nat.le_refl _)
  -- the constructor counts of the source families
  have hcountPrim : ∀ (f : Nat) (hf : f < sourceDecl.types.length),
      (sourceDecl.types[f]'hf).ctors.length = E.production.indTypes[f]!.ctors.length := by
    intro f hf
    have hf' : f < sourceTypes.length := by omega
    have hf'' : f < (C₀.main :: C₀.rest).length := by rw [← C₀.typesSource]; exact hf
    obtain ⟨s, m, Hstep, hcnt⟩ := Lean4Lean.List.forall₂_getElem Hcounts f hf' hf''
    have howner : (C₀.main :: C₀.rest)[f]'hf'' = sourceDecl.types[f]'hf := by
      simp only [C₀.typesSource]
    rw [howner] at hcnt
    rw [hcnt]
    exact (E.stepRules_length ⟨f, by omega⟩ Hstep.restored.recursor (hprimName f hf')).1
  -- the primary rules
  have Hprim : List.Forall₂ (fun (oc : VInductiveType × VConstVal) rule =>
      Nonempty (sourceDecl.NestedIotaRule
        (canonicalRestoredShapeBlock sourceDecl C₀.primaryRecursors C₀.auxiliaryRecursors)
        oc.1 oc.2 rule) ∧ rule.WF C₀.finalBaseVEnv)
      (ownedConstructorsFor (C₀.main :: C₀.rest))
      (rules.take (recursorMinorOffset E.production.indTypes sourceDecl.types.length)) := by
    rw [← C₀.typesSource]
    apply forall₂_ownedConstructorsFor_offsets sourceDecl.types _
      (recursorMinorOffset E.production.indTypes)
    · simp [recursorMinorOffset]
    · intro i hi
      rw [recursorMinorOffset_step _ _ (by omega), hcountPrim i hi]
    · simp only [List.length_take, hlenRules]
      omega
    · intro i hi j hj hk
      simp only [List.length_take] at hk
      have hk' : recursorMinorOffset E.production.indTypes i + j < rules.length := by omega
      have hkn : recursorMinorOffset E.production.indTypes i + j <
          E.production.production.generationSignature.constructors.size := by
        omega
      simp only [List.getElem_take]
      have Hk := Lean4Lean.List.forall₂_getElem Hrules _ (by simpa using hkn) hk'
      simp only [List.getElem_finRange] at Hk
      exact ⟨E.primaryNestedIotaRule wf Hsources hadded Haux Hexpansion hnodup hparamsSize D'
          hscoped C₀ hC₀ hV hfresh HL hcountPrim hauxNames _ Hk i hi j hj rfl,
        HrestoredWF aux' D' C₀ hC₀ hV _ _ Hk⟩
  have Hprimary := C₀.primaryIota.replaceRules Hprim
  -- the auxiliary rules
  have hauxLen : C₀.auxiliaryRules.length =
      ([] : List VDefEq).length +
        ((List.range (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).1.length).map
          (fun a => E.production.indTypes[sourceTypes.length + a]!.ctors.length)).sum := by
    apply C₀.auxiliarySemantics.rulesLength_eq
    apply Lean4Lean.List.forall₂_of_getElem (by simp)
    intro a ha _ s t Hstep
    simp only [List.getElem_map, List.getElem_range]
    exact (E.stepRules_length ⟨sourceTypes.length + a, by omega⟩ Hstep (hauxName a ha)).2
  rw [recursorMinorOffset_sum _ _ _ (by omega)] at hauxLen
  have hsrcLen : sourceTypes.length = sourceDecl.types.length := by omega
  rw [hsrcLen, show sourceDecl.types.length +
      (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).1.length =
        E.production.indTypes.size by omega, hOn] at hauxLen
  -- block names
  have hblockNames : (canonicalRestoredBlock sourceDecl C₀.primaryRecursors
      C₀.auxiliaryRecursors
      (rules.take (recursorMinorOffset E.production.indTypes sourceDecl.types.length))
      (rules.drop (recursorMinorOffset E.production.indTypes sourceDecl.types.length))).recursors.map
        (·.name) =
      (sourceTypes.map (·.name)).map (fun name =>
          let oldName := Lean.mkRecName name
          (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2.getD oldName oldName) ++
        (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).1.map fun oldName =>
          (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2.getD oldName oldName := by
    simp only [canonicalRestoredBlock, List.map_append, List.map_map]
    obtain ⟨added, hadded', Hadded⟩ := C₀.auxiliarySemantics.recursorSteps
    simp only [List.nil_append] at hadded'
    rw [C₀.sourceSemantics.recursorNames, hadded']
    congr 1
    exact stepValues_names Hadded
  have Hguard : ∀ rule ∈ rules.drop
      (recursorMinorOffset E.production.indTypes sourceDecl.types.length),
      rule.rhs.GuardedRuleRhs ((canonicalRestoredBlock sourceDecl C₀.primaryRecursors
        C₀.auxiliaryRecursors
        (rules.take (recursorMinorOffset E.production.indTypes sourceDecl.types.length))
        (rules.drop (recursorMinorOffset E.production.indTypes
          sourceDecl.types.length))).recursors.map (·.name)) := by
    intro rule hrule
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hrule
    simp only [List.length_drop] at hi
    simp only [List.getElem_drop]
    have hm : recursorMinorOffset E.production.indTypes sourceDecl.types.length + i <
        rules.length := by omega
    have hmn : recursorMinorOffset E.production.indTypes sourceDecl.types.length + i <
        E.production.production.generationSignature.constructors.size := by omega
    obtain ⟨owner, j, s, t, Hstep, hj, hk, -, Ht, -, -⟩ :=
      Lean4Lean.List.forall₂_getElem Hreal _ (by simpa using hmn) hm
    simp only [List.getElem_finRange, Fin.val_cast] at hk
    have hjcnt := (E.stepRules_length owner Hstep rfl).2
    have howner : sourceTypes.length ≤ owner.val := by
      apply Classical.byContradiction
      intro hlt
      have hstep := recursorMinorOffset_step E.production.indTypes owner.val (by omega)
      have hmono := recursorMinorOffset_mono E.production.indTypes (owner.val + 1)
        sourceDecl.types.length (by omega) hpSize
      omega
    have hrecAux : E.production.production.canonicalGeneration.recursorName owner ∈
        (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).1 := by
      have h := hauxName (owner.val - sourceTypes.length) (by omega)
      have hown : (⟨sourceTypes.length + (owner.val - sourceTypes.length), by omega⟩ :
          Fin E.production.production.generationSignature.families.size) = owner :=
        Fin.ext (by simp only; omega)
      rw [hown] at h
      rw [← h]
      exact List.getElem_mem _
    rw [hblockNames]
    exact E.restoredRuleRhs_guarded hV hrecAux Hstep j hj Ht
  have Hwf : ∀ rule ∈ rules.drop
      (recursorMinorOffset E.production.indTypes sourceDecl.types.length),
      rule.WF C₀.finalBaseVEnv := by
    intro rule hrule
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hrule
    simp only [List.length_drop] at hi
    simp only [List.getElem_drop]
    have hm : recursorMinorOffset E.production.indTypes sourceDecl.types.length + i <
        rules.length := by omega
    have hmn : recursorMinorOffset E.production.indTypes sourceDecl.types.length + i <
        E.production.production.generationSignature.constructors.size := by omega
    have Hk := Lean4Lean.List.forall₂_getElem Hrules _ (by simpa using hmn) hm
    exact HrestoredWF aux' D' C₀ hC₀ hV _ _ Hk
  obtain ⟨Haux', HauxWF'⟩ := C₀.auxiliaryWF.replaceRules
    (canonicalRestoredBlock sourceDecl C₀.primaryRecursors C₀.auxiliaryRecursors
      (rules.take (recursorMinorOffset E.production.indTypes sourceDecl.types.length))
      (rules.drop (recursorMinorOffset E.production.indTypes sourceDecl.types.length)))
    [] (rules.drop (recursorMinorOffset E.production.indTypes sourceDecl.types.length))
    (rules.drop (recursorMinorOffset E.production.indTypes sourceDecl.types.length))
    (by simp) (by simp only [List.length_nil, List.length_drop, hlenRules] at hauxLen ⊢; omega)
    Hguard Hwf
  refine ⟨C₀.withRules
    (rules.take (recursorMinorOffset E.production.indTypes sourceDecl.types.length))
    (rules.drop (recursorMinorOffset E.production.indTypes sourceDecl.types.length))
    Hprimary Haux' HauxWF', hC₀, ?_⟩
  show List.Forall₂ _ _ (rules.take _ ++ rules.drop _)
  rw [List.take_append_drop]
  exact Hreal'

end VerifyInductive
end Lean4Lean
