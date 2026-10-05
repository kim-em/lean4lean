import Lean4Lean.Theory.Inductive.CaseConstructorOrigin
import Lean4Lean.Theory.Typing.ProjectionRigidity

/-! Declaration-history invariants for native constructor computation. -/

namespace Lean4Lean

/-- The final major argument of an installed equation has this native head. -/
def VDefEq.HasConstructorMajor (equation : VDefEq) (name : Name) : Prop :=
  ∃ fn levels args, equation.lhs.stripLams = .app fn (VExpr.mkApps (.const name levels) args)

theorem VExpr.nativeEquationHead_eq (e : VExpr) :
    e.nativeEquationHead = e.stripLams.getAppFnArgs.1 := by
  induction e with
  | lam _ _ _ ih => exact ih
  | _ => rfl

theorem VEnv.nativeHeadRigid_iff {env : VEnv} {name : Name} :
    env.NativeHeadRigid name ↔ env.Rigid name := by
  simp only [NativeHeadRigid, Rigid, VExpr.nativeEquationHead_eq]

theorem InductiveSignature.CompilationData.equation_major_origin
    {s : InductiveSignature} {g : s.Instance}
    (H : InductiveSignature.CompilationData env source expanded s g auxiliaries block)
    (hprior : CertifiedSpecializations env auxiliaries) (hdf : df ∈ block.rules) :
    ∃ name, df.HasConstructorMajor name ∧
      ((∃ ctor ∈ source.constructorConstants, name = ctor.name) ∨
        ∃ prior, env.defeqs prior ∧ prior.HasConstructorMajor name) := by
  obtain ⟨generated, hgenerated, hrestored⟩ := Lean4Lean.List.Forall₂.forall_exists_r
    (List.mapM_eq_some.mp H.equations) _ hdf
  obtain ⟨index, _, rfl⟩ := List.mem_map.mp hgenerated
  refine ⟨_, InductiveSignature.Instance.restored_equation_major H index hrestored, ?_⟩
  rcases H.constructor_name_origin index with ho | ⟨a, ha, ctor, hc, he⟩
  · exact Or.inl ho
  · right
    rw [he]
    exact hprior.constructor_equation a ha ctor hc

theorem CompiledInductive.equation_major_origin (H : CompiledInductive env source block) :
    ∀ df ∈ block.rules, ∃ name, df.HasConstructorMajor name ∧
      ((∃ ctor ∈ source.constructorConstants, name = ctor.name) ∨
        ∃ prior, env.defeqs prior ∧ prior.HasConstructorMajor name) := by
  exact CompiledInductive.rec
    (motive_1 := fun env source block _ =>
      ∀ df ∈ block.rules, ∃ name, df.HasConstructorMajor name ∧
        ((∃ ctor ∈ source.constructorConstants, name = ctor.name) ∨
          ∃ prior, env.defeqs prior ∧ prior.HasConstructorMajor name))
    (motive_2 := fun _ _ _ => True)
    (fun hdata hprior _ df hdf => hdata.equation_major_origin hprior hdf)
    (fun _ hle _ ih df hdf => by
      obtain ⟨name, hm, ho | ⟨prior, hp, hpm⟩⟩ := ih df hdf
      · exact ⟨name, hm, Or.inl ho⟩
      · exact ⟨name, hm, Or.inr ⟨prior, hle.defeqs hp, hpm⟩⟩)
    trivial (fun _ _ _ _ _ _ _ => trivial) H

private theorem VDefEq.HasConstructorMajor.unique {df : VDefEq}
    (hleft : df.HasConstructorMajor left) (hright : df.HasConstructorMajor right) :
    left = right := by
  obtain ⟨fl, ll, al, hl⟩ := hleft
  obtain ⟨fr, lr, ar, hr⟩ := hright
  have he := (VExpr.app.inj (hl.symm.trans hr)).2
  have hh := congrArg (fun e : VExpr => e.getAppFnArgs.1) he
  simp only [VExpr.getAppFnArgs_mkApps_head] at hh
  exact (VExpr.const.inj hh).1

namespace VEnv

/-- Native equation majors, registered case constructors, and original
families retain declared constants at which no native equation computes. -/
private def ConstructorHistory (env : VEnv) : Prop :=
  (∀ equation, env.defeqs equation → ∀ name, equation.HasConstructorMajor name →
    (∃ ci, env.constants name = some ci) ∧ env.Rigid name) ∧
  (∀ key schema, env.eliminators key schema →
    ∀ (owner : Fin schema.signature.families.size) rule, schema.Generates key owner rule →
    (∃ ci, env.constants rule.application.ctorName = some ci) ∧ env.Rigid rule.application.ctorName) ∧
  (∀ key schema, env.eliminators key schema → ∀ name ∈ schema.originalFamilies,
    (∃ ci, env.constants name = some ci) ∧ env.Rigid name)

private theorem ConstructorHistory.transport {env env' : VEnv}
    (H : ConstructorHistory env) (hle : env ≤ env')
    (hdf : env'.defeqs = env.defeqs) (helim : env'.eliminators = env.eliminators) :
    ConstructorHistory env' := by
  have move {name} : ((∃ ci, env.constants name = some ci) ∧ env.Rigid name) →
      ((∃ ci, env'.constants name = some ci) ∧ env'.Rigid name) := by
    rintro ⟨⟨ci, hci⟩, hr⟩
    exact ⟨⟨ci, hle.1 hci⟩, by simpa only [Rigid, hdf] using hr⟩
  refine ⟨?_, ?_, ?_⟩
  · intro equation he name hn
    rw [hdf] at he
    exact move (H.1 equation he name hn)
  · intro key schema hs owner rule hr
    rw [helim] at hs
    exact move (H.2.1 key schema hs owner rule hr)
  · intro key schema hs name hn
    rw [helim] at hs
    exact move (H.2.2 key schema hs name hn)

private theorem ConstructorHistory.addConst {env env' : VEnv}
    (H : ConstructorHistory env) (hadd : env.addConst name ci = some env') :
    ConstructorHistory env' :=
  H.transport (VEnv.addConst_le hadd) (VEnv.addConst_defeqs hadd)
    (VEnv.addConst_eliminators hadd)

private theorem ConstructorHistory.addConstVals {env env' : VEnv}
    (H : ConstructorHistory env) (hadd : env.addConstVals values = some env') :
    ConstructorHistory env' :=
  H.transport (VEnv.addConstVals_le hadd) (VEnv.addConstVals_defeqs hadd)
    (VEnv.addConstVals_eliminators hadd)

private theorem defeqs_addRules {env : VEnv} {rules : List VDefEq} :
    (env.addDefEqRules rules).defeqs df ↔ df ∈ rules ∨ env.defeqs df := by
  induction rules generalizing env with
  | nil => simp [VEnv.addDefEqRules]
  | cons rule rules ih =>
    rw [VEnv.addDefEqRules, ih]
    change (df ∈ rules ∨ df = rule ∨ env.defeqs df) ↔ _
    simp only [List.mem_cons]
    rw [← or_assoc, or_comm (a := df ∈ rules)]

/-- Fresh recursor heads preserve constructors known before the recursor
constants and equations were added. -/
private theorem ConstructorHistory.addRules {pre env : VEnv} {rules : List VDefEq}
    (H : ConstructorHistory pre) (hle : pre ≤ env)
    (hdf : env.defeqs = pre.defeqs) (helim : env.eliminators = pre.eliminators)
    (hhead : ∀ df ∈ rules, ∀ name levels,
      df.lhs.stripLams.getAppFnArgs.1 = .const name levels → pre.constants name = none)
    (hmajor : ∀ df ∈ rules, ∀ name, df.HasConstructorMajor name →
      (∃ ci, pre.constants name = some ci) ∧ pre.Rigid name) :
    ConstructorHistory (env.addDefEqRules rules) := by
  have hconstants : (env.addDefEqRules rules).constants = env.constants :=
    VEnv.addDefEqRules_constants _ _
  have heliminators : (env.addDefEqRules rules).eliminators = pre.eliminators :=
    (VEnv.addDefEqRules_eliminators _ _).trans helim
  have move {name} : ((∃ ci, pre.constants name = some ci) ∧ pre.Rigid name) →
      ((∃ ci, (env.addDefEqRules rules).constants name = some ci) ∧
        (env.addDefEqRules rules).Rigid name) := by
    rintro ⟨⟨ci, hci⟩, hr⟩
    refine ⟨⟨ci, by rw [hconstants]; exact hle.1 hci⟩, ?_⟩
    intro df hd levels hh
    rcases defeqs_addRules.mp hd with hm | ho
    · have hn := hhead df hm name levels hh
      rw [hci] at hn
      contradiction
    · rw [hdf] at ho
      exact hr df ho levels hh
  refine ⟨?_, ?_, ?_⟩
  · intro df hd name hn
    rcases defeqs_addRules.mp hd with hm | ho
    · exact move (hmajor df hm name hn)
    · rw [hdf] at ho
      exact move (H.1 df ho name hn)
  · intro key schema hs owner rule hr
    rw [heliminators] at hs
    exact move (H.2.1 key schema hs owner rule hr)
  · intro key schema hs name hn
    rw [heliminators] at hs
    exact move (H.2.2 key schema hs name hn)

private theorem ConstructorHistory.compileRules {pre env : VEnv}
    {recursors : List VConstVal} {rules : List VDefEq}
    (H : ConstructorHistory pre) (hrecs : pre.addConstVals recursors = some env)
    (hheads : ∀ df ∈ rules, ∃ recursor ∈ recursors, ∃ levels,
      df.lhs.stripLams.getAppFnArgs.1 = .const recursor.name levels)
    (hmajor : ∀ df ∈ rules, ∀ name, df.HasConstructorMajor name →
      (∃ ci, pre.constants name = some ci) ∧ pre.Rigid name) :
    ConstructorHistory (env.addDefEqRules rules) := by
  apply H.addRules (VEnv.addConstVals_le hrecs) (VEnv.addConstVals_defeqs hrecs)
    (VEnv.addConstVals_eliminators hrecs) _ hmajor
  intro df hdf name levels hhead
  obtain ⟨recursor, hrecursor, ls, hr⟩ := hheads df hdf
  have hn : recursor.name = name := (VExpr.const.inj (hr.symm.trans hhead)).1
  rw [← hn]
  exact VEnv.addConstVals_names_fresh hrecs recursor hrecursor

private theorem ConstructorHistory.addProjections
    (H : ConstructorHistory env) : ConstructorHistory (env.addProjections entries) :=
  H.transport VEnv.addProjections_le (VEnv.addProjections_defeqs _ _)
    (VEnv.addProjections_eliminators _ _)

private theorem addConsts_as_values {env : VEnv} {cis : List VDefVal} :
    env.addConsts cis = env.addConstVals (cis.map (·.toVConstVal)) := by
  induction cis generalizing env with
  | nil => rfl
  | cons ci cis ih =>
    simp only [VEnv.addConsts, List.foldlM_cons, List.map_cons, VEnv.addConstVals]
    cases env.addConst ci.name ci.toVConstant with
    | none => rfl
    | some middle => exact ih (env := middle)

private theorem addDefEqs_as_rules {env : VEnv} {cis : List VDefVal} :
    env.addDefEqs cis = env.addDefEqRules (cis.map (·.toDefEq)) := by
  induction cis generalizing env with
  | nil => rfl
  | cons ci cis ih => exact ih (env := env.addDefEq ci.toDefEq)

private theorem ConstructorHistory.addDefinitions {env env' : VEnv}
    (H : ConstructorHistory env) (hadd : env.addConsts cis = some env') :
    ConstructorHistory (env'.addDefEqs cis) := by
  rw [addDefEqs_as_rules]
  apply H.compileRules (recursors := cis.map (·.toVConstVal))
    (by rwa [← addConsts_as_values])
  · intro df hdf
    obtain ⟨ci, hci, rfl⟩ := List.mem_map.mp hdf
    exact ⟨ci.toVConstVal, List.mem_map.mpr ⟨ci, hci, rfl⟩,
      VLevel.params ci.uvars, rfl⟩
  · intro df hdf name hn
    obtain ⟨ci, _, rfl⟩ := List.mem_map.mp hdf
    obtain ⟨fn, levels, args, hm⟩ := hn
    cases hm

private theorem addConst_fresh {env env' : VEnv}
    (h : env.addConst name ci = some env') : env.constants name = none := by
  unfold VEnv.addConst at h
  split at h
  · cases h
  · rename_i he
    exact he

private theorem absent_of_le {base env : VEnv} (hle : base ≤ env)
    (h : env.constants name = none) : base.constants name = none := by
  cases hb : base.constants name with
  | none => rfl
  | some ci =>
    have he := hle.constants hb
    rw [h] at he
    contradiction

private theorem rigid_of_defeqs_eq {base env : VEnv} (h : env.defeqs = base.defeqs)
    (hr : base.Rigid name) : env.Rigid name := by
  simpa only [Rigid, h] using hr

private theorem ConstructorHistory.addQuot {env env' : VEnv}
    (H : ConstructorHistory env) (hordered : env.Ordered)
    (hadd : env.addQuot = some env') : ConstructorHistory env' := by
  simp [VEnv.addQuot] at hadd
  obtain ⟨e1, h1, e2, h2, e3, h3, pre, h4, rfl⟩ := hadd
  let recursors : List VConstVal := [
    { name := ``Quot.lift, toVConstant := quotLiftConst },
    { name := ``Quot.ind, toVConstant := quotIndConst }]
  have hrecs : e2.addConstVals recursors = some pre := by
    simp [recursors, VEnv.addConstVals, h3, h4]
  apply ((H.addConst h1).addConst h2).compileRules (rules := [quotDefEq]) hrecs
  · intro df hdf
    obtain rfl := List.mem_singleton.mp hdf
    exact ⟨{ name := ``Quot.lift, toVConstant := quotLiftConst }, by simp [recursors],
      [.param 0, .param 1], rfl⟩
  · intro df hdf name hm
    obtain rfl := List.mem_singleton.mp hdf
    have hmk : quotDefEq.HasConstructorMajor ``Quot.mk := ⟨_, [.param 0], [.bvar 5, .bvar 4, .bvar 0], rfl⟩
    have hn := hm.unique hmk
    subst name
    have hrigid := hordered.rigid_of_absent
      (absent_of_le (VEnv.addConst_le h1) (addConst_fresh h2))
    exact ⟨⟨quotMkConst, VEnv.addConst_self h2⟩,
      rigid_of_defeqs_eq ((VEnv.addConst_defeqs h2).trans (VEnv.addConst_defeqs h1)) hrigid⟩

private theorem ConstructorHistory.register {base env : VEnv}
    {schema : InductiveSignature.CaseSchema}
    (Hbase : ConstructorHistory base) (Henv : ConstructorHistory env)
    (hbase : base.Ordered) (hle : base ≤ env)
    (hcert : schema.Certified base source block)
    (hconstants : ∀ value ∈ block.types ++ block.ctors,
      env.constants value.name = some value.toVConstant)
    (hdf : env.defeqs = base.defeqs) :
    ConstructorHistory (env.addEliminator key schema) := by
  refine ⟨?_, ?_, ?_⟩
  · exact Henv.1
  · intro k s hs owner rule hr
    rcases hs with ⟨rfl, rfl⟩ | hs
    · rcases hcert.case_constructor_origin hr with ⟨ctor, hc, hn⟩ | ⟨prior, hp, hpm⟩
      · obtain ⟨expanded, g, auxiliaries, hdata, _⟩ := hcert
        obtain ⟨types, ctors, ht, hct, _⟩ := hdata.sourceWF.2.2.2.2
        have hfresh := absent_of_le (VEnv.addConstVals_le ht)
          (VEnv.addConstVals_names_fresh hct ctor hc)
        rw [hn]
        refine ⟨⟨ctor.toVConstant, ?_⟩, ?_⟩
        · exact hconstants ctor (List.mem_append_right _ (by rwa [hdata.ctors]))
        · exact rigid_of_defeqs_eq hdf (hbase.rigid_of_absent hfresh)
      · obtain ⟨⟨ci, hci⟩, hrigid⟩ := Hbase.1 prior hp _ hpm
        exact ⟨⟨ci, hle.constants hci⟩, rigid_of_defeqs_eq hdf hrigid⟩
    · exact Henv.2.1 k s hs owner rule hr
  · intro k s hs name hn
    rcases hs with ⟨rfl, rfl⟩ | hs
    · obtain ⟨expanded, g, auxiliaries, hdata, _, _, hnames⟩ := hcert
      rw [hnames] at hn
      obtain ⟨family, hfamily, rfl⟩ := List.mem_map.mp hn
      obtain ⟨types, ctors, ht, _⟩ := hdata.sourceWF.2.2.2.2
      have hfresh := VEnv.addConstVals_names_fresh ht family.toVConstVal
        (List.mem_map.mpr ⟨family, hfamily, rfl⟩)
      refine ⟨⟨family.toVConstant, hconstants family.toVConstVal ?_⟩,
        rigid_of_defeqs_eq hdf (hbase.rigid_of_absent hfresh)⟩
      apply List.mem_append_left
      rw [hdata.types]
      exact List.mem_map.mpr ⟨family, hfamily, rfl⟩
    · exact Henv.2.2 k s hs name hn

private theorem ConstructorHistory.addInduct
    (H : ConstructorHistory env) (hordered : env.Ordered)
    (hadd : env.AddInduct decl env') : ConstructorHistory env' := by
  cases hadd with
  | @intro block installed hdecl hcompile hblock hinstall =>
    obtain ⟨envTypes, envCtors, envRecursors, htypes, hctors, hrecs, _⟩ := hblock
    have hcanonical : VInductBlock.install env block =
        some (envRecursors.addDefEqRules block.rules) := by
      simp [VInductBlock.install, htypes, hctors, hrecs]
    have he : env' = envRecursors.addDefEqRules block.rules :=
      Option.some.inj (hinstall.symm.trans hcanonical)
    subst env'
    have hpre := ((H.addConstVals htypes).addConstVals hctors).addProjections
      (entries := block.projections)
    have hle : env ≤ envCtors.addProjections block.projections :=
      (VEnv.addConstVals_le htypes).trans <|
        (VEnv.addConstVals_le hctors).trans VEnv.addProjections_le
    have hdf : (envCtors.addProjections block.projections).defeqs = env.defeqs :=
      (VEnv.addProjections_defeqs _ _).trans <|
        (VEnv.addConstVals_defeqs hctors).trans (VEnv.addConstVals_defeqs htypes)
    apply hpre.compileRules hrecs hcompile.compiled.equation_head_owned
    intro df hdfMem name hmajor
    obtain ⟨originName, horigin, hctor | ⟨prior, hprior, hpriorMajor⟩⟩ :=
      hcompile.compiled.equation_major_origin df hdfMem
    · have heq := hmajor.unique horigin
      obtain ⟨ctor, hctor, hname⟩ := hctor
      have hn : name = ctor.name := heq.trans hname
      rw [hn]
      have hc : ctor ∈ block.ctors := by rw [hcompile.ctors]; exact hctor
      have hfresh := VEnv.addConstVals_names_fresh hctors ctor hc
      have hr := hordered.rigid_of_absent
        (absent_of_le (VEnv.addConstVals_le htypes) hfresh)
      exact ⟨⟨ctor.toVConstant, by
        simpa only [VEnv.addProjections_constants] using VEnv.addConstVals_get hctors hc⟩,
        rigid_of_defeqs_eq hdf hr⟩
    · have heq := hmajor.unique horigin
      rw [← heq] at hpriorMajor
      obtain ⟨⟨ci, hci⟩, hr⟩ := H.1 prior hprior name hpriorMajor
      exact ⟨⟨ci, hle.constants hci⟩, rigid_of_defeqs_eq hdf hr⟩

private theorem WF.constructorHistory {env : VEnv} (H : env.WF) : ConstructorHistory env := by
  suffices h : ∀ {ds env}, VEnv.WF' ds env → ConstructorHistory env from h H.choose_spec
  intro ds env H
  induction H with
  | empty =>
    refine ⟨?_, ?_, ?_⟩
    · intro _ h; cases h
    · intro _ _ h; cases h
    · intro _ _ h; cases h
  | @decl d env' ds env hdecl hbase ih =>
    have hordered := (show env.WF from ⟨ds, hbase⟩).ordered
    cases hdecl with
    | «axiom» _ hadd | «opaque» _ hadd => exact ih.addConst hadd
    | «example» => exact ih
    | @«def» _ _ ci _ hadd =>
      exact ih.addDefinitions (cis := [ci]) (by simpa [VEnv.addConsts] using hadd)
    | mutualDef _ hadd _ => exact ih.addDefinitions hadd
    | quot _ hadd => exact ih.addQuot hordered hadd
    | induct _ hadd => exact ih.addInduct hordered hadd
  | inductEliminators hbase henv hle hcert hkey hconstants hfresh ihBase ihEnv =>
    exact ihBase.register ihEnv (show VEnv.WF _ from ⟨_, hbase⟩).ordered
      hle hcert hconstants.1 hconstants.2
  | inductProjections _ _ _ _ _ _ _ _ _ _ _ _ _ _ ihCtors =>
    exact ihCtors.addProjections

/-- Every generated case constructor is rigid under native computation.
The proof uses finite source provenance and declaration history, independently
of confluence, typing uniqueness, or constructor injectivity. -/
theorem WF.case_constructor_rigid {env : VEnv} (H : env.WF)
    (hregistered : env.eliminators block schema)
    {owner : Fin schema.signature.families.size}
    (hgenerated : schema.Generates block owner rule) :
    env.NativeHeadRigid rule.application.ctorName :=
  nativeHeadRigid_iff.mpr ((H.constructorHistory.2.1 _ _ hregistered _ _ hgenerated).2)

/-- The original family behind a registered projection or case program is
rigid throughout declaration extension. This uses registration provenance,
not a primitive projection entry or a general monotonicity assumption. -/
theorem WF.case_original_family_rigid {env : VEnv} (H : env.WF)
    (hregistered : env.eliminators key schema)
    (hfamily : name ∈ schema.originalFamilies) : env.NativeHeadRigid name :=
  nativeHeadRigid_iff.mpr ((H.constructorHistory.2.2 _ _ hregistered _ hfamily).2)

/-- The major constructor of every installed native iota equation remains
rigid throughout all subsequent declarations. -/
theorem WF.native_constructor_rigid {env : VEnv} (H : env.WF)
    (hinstalled : env.defeqs equation) (hmajor : equation.HasConstructorMajor name) :
    env.NativeHeadRigid name :=
  nativeHeadRigid_iff.mpr ((H.constructorHistory.1 _ hinstalled _ hmajor).2)

end VEnv
end Lean4Lean
