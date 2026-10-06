import Lean4Lean.Verify.Inductive.Nested.AssemblyProviderEvidence
import Lean4Lean.Verify.Inductive.Nested.RestoredEquations
import Lean4Lean.Verify.Inductive.Nested.HitShapeInputs
import Lean4Lean.Verify.Inductive.Nested.FinalShapes

/-! Final assembly certificate of a validated nested run.

`NestedValidatedRunResult.assemblyNative` asks for a
`NestedFinalAssemblyCertificate` whose production is the run's.
`NestedValidatedRunResult.assemblyNative_of_run` assembles one from the
run, given two named hypotheses:

* `Hrules`, the rule junction: a final assembly shape whose rule lists realize
  the executable restored rules (`RestoredRuleRealization`) in its own final
  abstract environment, in which the restorable names are fresh. The shapes
  built by `assemblyShapeNative` use the rule validator's equations, whose
  left-hand side and (inferred) type are not syntactically the restored
  generated ones;
* `Hprovenance`, the recursor provenance of such a shape.

Everything else (the `CompilationData`, the certified specializations and
the realization of every concrete restored recursor entry, including its
specialization, rules and major inductive) is derived here. -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open InductiveSignature


namespace InductiveSignature

@[simp] theorem vars_length' (n k : Nat) : (vars n k).length = n := by
  simp [vars]

theorem vars_map_liftN (n k : Nat) :
    (vars n 0).map (fun arg => arg.liftN k) = vars n k := by
  simp only [vars, List.map_map, Function.comp_def, VExpr.liftN, liftVar]
  apply List.map_congr_left
  intro i _
  simp [Nat.add_comm]

theorem Restoration.find?_of_nodup {heads : List HeadSpecialization}
    (hnodup : (heads.map (·.auxiliary)).Nodup) {x : HeadSpecialization}
    (hx : x ∈ heads) : heads.find? (fun y => y.auxiliary == x.auxiliary) = some x := by
  induction heads with
  | nil => simp at hx
  | cons y ys ih =>
    simp only [List.map_cons, List.nodup_cons] at hnodup
    simp only [List.find?_cons]
    rcases List.mem_cons.mp hx with rfl | hx
    · simp
    · have hne : (y.auxiliary == x.auxiliary) = false := by
        have : y.auxiliary ≠ x.auxiliary := fun h =>
          hnodup.1 (h ▸ List.mem_map_of_mem hx)
        simpa using this
      simp only [hne]
      exact ih hnodup.2 hx

theorem declaration_ctor_mem (s : InductiveSignature) (index : Fin s.constructors.size)
    (howner : s.constructors[index].owner.val < s.declaration.types.length) :
    ({ name := s.constructors[index].name, uvars := s.uvars,
        type := s.constructorType s.constructors[index] } : VConstVal) ∈
      (s.declaration.types[s.constructors[index].owner.val]'howner).ctors := by
  simp only [InductiveSignature.declaration, List.getElem_map, List.getElem_zipIdx,
    List.mem_filterMap]
  refine ⟨s.constructors[index], Array.getElem_mem_toList _, ?_⟩
  simp

theorem Restoration.recursorName_ne_of_mem {r : Restoration}
    (hne : ∀ p ∈ r.recursors, p.2 ≠ p.1) {name : Name}
    (h : name ∈ r.recursors.map Prod.fst) : r.recursorName name ≠ name := by
  unfold Restoration.recursorName
  split
  · next pair hfind =>
    have hmem := List.mem_of_find?_eq_some hfind
    have heq := List.find?_some hfind
    simp only [beq_iff_eq] at heq
    rw [← heq]
    exact hne pair hmem
  · next hfind =>
    obtain ⟨pair, hpair, rfl⟩ := List.mem_map.mp h
    have := List.find?_eq_none.mp hfind pair hpair
    simp at this

/-- **The restored family head of a compiled owner.** For a source family it
is the family itself at the instance's universe levels and the parameter
variables; for an auxiliary family it is the specialized container. Every
constructor of the owner restores to the restored constructor head applied
to the head's arguments and the fields. -/
theorem CompilationData.restoredFamilyHead_spec
    {env : VEnv} {source expanded : VInductDecl} {s : InductiveSignature}
    {g : Instance s} {auxiliaries : List ContainerSpecialization} {block : VInductBlock}
    (Hd : CompilationData env source expanded s g auxiliaries block)
    {envTypes envCtors : VEnv}
    (hadded : env.addConstVals source.typeConstants = some envTypes)
    (hctorsAdded : envTypes.addConstVals source.constructorConstants = some envCtors)
    (hfresh : ∀ n ∈ (compilationRestoration source auxiliaries).restorableNames,
      envTypes.constants n = none)
    (hfreshCtors : ∀ n ∈ (compilationRestoration source auxiliaries).restorableNames,
      envCtors.constants n = none)
    (owner : Fin s.families.size) :
    ∃ head : RestoredFamilyHead,
      g.restoredFamilyHead (compilationRestoration source auxiliaries) owner = some head ∧
      head.name = (compilationRestoration source auxiliaries).restoredHeadName
        s.families[owner].name ∧
      (∀ level ∈ head.levels, level.WF g.uvars) ∧
      (∀ arg ∈ head.arguments, arg.ClosedN s.params.length) ∧
      (compilationRestoration source auxiliaries).expr (g.familyApp owner
        (vars s.params.length
          (s.families.size + s.constructors.size + s.families[owner].indices.length))
        (vars s.families[owner].indices.length 0)) =
        some (VExpr.mkApps (.const head.name head.levels)
          (head.arguments.map (fun arg => arg.liftN
            (s.families.size + s.constructors.size + s.families[owner].indices.length)) ++
            vars s.families[owner].indices.length 0)) ∧
      ∀ index : Fin s.constructors.size, s.constructors[index].owner = owner →
        (((compilationRestoration source auxiliaries).heads.find?
            (fun h => h.auxiliary == s.families[owner].name) = none ∧
          (compilationRestoration source auxiliaries).restoredHeadName
            s.constructors[index].name = s.constructors[index].name) ∨
          ∃ a ∈ auxiliaries, s.families[owner].name = a.auxiliary ∧
            ∃ ctor ∈ a.source.ctors, s.constructors[index].name = a.constructorName ctor) ∧
        (compilationRestoration source auxiliaries).expr
          (g.constructorApp s.constructors[index] (s.families.size + s.constructors.size) 0) =
          some (VExpr.mkApps (.const ((compilationRestoration source auxiliaries).restoredHeadName
              s.constructors[index].name) head.levels)
            (head.arguments.map (fun arg => arg.liftN
              (s.families.size + s.constructors.size + s.constructors[index].fields.length)) ++
              vars s.constructors[index].fields.length 0)) := by
  obtain ⟨envTypes', direct, hadded', hdirect, hwellFormed, Hfam⟩ := Hd.correspondence
  have henv : envTypes = envTypes' := Option.some.inj (hadded.symm.trans hadded')
  subst henv
  obtain ⟨envExpandedTypes, -, Hadm⟩ := Hd.admissible
  have hlevelsLen : g.levels.length = source.uvars :=
    Hadm.levels_length.trans (Hd.model.uvars.trans Hd.uvars)
  have hnp : s.params.length = source.nparams := Hd.model.nparams.trans Hd.nparams
  have hdeclLen : s.declaration.types.length = s.families.size := by
    simp [InductiveSignature.declaration]
  have hlen := Lean4Lean.List.Forall₂.length_eq Hfam
  have howner : owner.val < s.declaration.types.length := by rw [hdeclLen]; exact owner.isLt
  have howner' : owner.val < (source.types ++ direct).length := hlen ▸ howner
  have Hat := Lean4Lean.List.forall₂_getElem Hfam owner.val howner howner'
  have hdeclName : (s.declaration.types[owner.val]'howner).name = s.families[owner].name := by
    simp [InductiveSignature.declaration]
  have hname : s.families[owner].name = ((source.types ++ direct)[owner.val]'howner').name :=
    hdeclName.symm.trans Hat.name
  -- every constructor of the owner names a constructor of the corresponding family
  have hctorName : ∀ index : Fin s.constructors.size, s.constructors[index].owner = owner →
      ∃ sc ∈ ((source.types ++ direct)[owner.val]'howner').ctors,
        s.constructors[index].name = sc.name := by
    intro index hindex
    have hmem := declaration_ctor_mem s index (by rw [hindex]; exact howner)
    simp only [hindex] at hmem
    obtain ⟨sc, hsc, hsc'⟩ :=
      Lean4Lean.List.Forall₂.forall_exists_l Hat.constructors _ hmem
    exact ⟨sc, hsc, hsc'.1⟩
  have hfreshHeads : ∀ n ∈ (compilationRestoration source auxiliaries).heads.map (·.auxiliary),
      envTypes.constants n = none :=
    fun n hn => hfresh n (List.mem_append_left _ hn)
  have hfreshRecs : ∀ p ∈ (compilationRestoration source auxiliaries).recursors,
      envTypes.constants p.1 = none :=
    fun p hp => hfresh p.1 (List.mem_append_right _ (List.mem_map_of_mem hp))
  have hfreshHeadsC : ∀ n ∈ (compilationRestoration source auxiliaries).heads.map (·.auxiliary),
      envCtors.constants n = none :=
    fun n hn => hfreshCtors n (List.mem_append_left _ hn)
  have hfreshRecsC : ∀ p ∈ (compilationRestoration source auxiliaries).recursors,
      envCtors.constants p.1 = none :=
    fun p hp => hfreshCtors p.1 (List.mem_append_right _ (List.mem_map_of_mem hp))
  by_cases hsrc : owner.val < source.types.length
  · -- a source family
    have hname' : s.families[owner].name = (source.types[owner.val]'hsrc).name := by
      rw [hname, List.getElem_append_left hsrc]
    have hconst : envTypes.constants s.families[owner].name =
        some (source.types[owner.val]'hsrc).toVConstVal.toVConstant := by
      rw [hname']
      exact VEnv.addConstVals_get hadded
        (List.mem_map.mpr ⟨_, List.getElem_mem hsrc, rfl⟩)
    have hfind : (compilationRestoration source auxiliaries).heads.find?
        (fun h => h.auxiliary == s.families[owner].name) = none := by
      apply Restoration.heads_find?_eq_none
      intro hmem
      rw [hfreshHeads _ hmem] at hconst
      cases hconst
    have hrecName : (compilationRestoration source auxiliaries).recursorName
        s.families[owner].name = s.families[owner].name :=
      Restoration.recursorName_of_constants hfreshRecs hconst
    refine ⟨⟨s.families[owner].name, g.levels, vars s.params.length 0⟩, ?_, ?_,
      ?_, ?_, ?_, ?_⟩
    · simp only [Instance.restoredFamilyHead, Instance.familyApp,
        InductiveSignature.familyApp, List.append_nil]
      rw [(compilationRestoration source auxiliaries).expr_mkApps,
        (compilationRestoration source auxiliaries).mapM_expr_vars]
      simp only [Option.bind_some, Restoration.expr.go, hfind, hrecName]
      simp only [Option.bind_eq_bind, Option.bind_some,
        VerifyInductive.VExpr.getAppFnArgs_mkApps]
      rfl
    · simp only [Restoration.restoredHeadName, hfind]
    · exact Hadm.levels_wf
    · intro arg harg
      simp only [vars, List.mem_map, List.mem_reverse, List.mem_range] at harg
      obtain ⟨i, hi, rfl⟩ := harg
      simp [VExpr.ClosedN, hi]
    · rw [show g.familyApp owner _ _ = g.recursorMajor owner from rfl,
        (compilationRestoration source auxiliaries).expr_recursorMajor_source g owner hfind
          hrecName]
      simp only [Instance.recursorMajor, Instance.familyApp, InductiveSignature.familyApp,
        vars_map_liftN]
    · intro index hindex
      obtain ⟨sc, hsc, hscName⟩ := hctorName index hindex
      rw [List.getElem_append_left hsrc] at hsc
      have hcconst : envCtors.constants s.constructors[index].name =
          some sc.toVConstant := by
        rw [hscName]
        exact VEnv.addConstVals_get hctorsAdded
          (List.mem_flatMap.mpr ⟨_, List.getElem_mem hsrc, hsc⟩)
      have hcfind : (compilationRestoration source auxiliaries).heads.find?
          (fun h => h.auxiliary == s.constructors[index].name) = none := by
        apply Restoration.heads_find?_eq_none
        intro hmem
        rw [hfreshHeadsC _ hmem] at hcconst
        cases hcconst
      have hcrec : (compilationRestoration source auxiliaries).recursorName
          s.constructors[index].name = s.constructors[index].name :=
        Restoration.recursorName_of_constants hfreshRecsC hcconst
      have hchead : (compilationRestoration source auxiliaries).restoredHeadName
          s.constructors[index].name = s.constructors[index].name := by
        simp only [Restoration.restoredHeadName, hcfind]
      refine ⟨.inl ⟨hfind, hchead⟩, ?_⟩
      rw [hchead]
      simp only [Instance.constructorApp]
      rw [(compilationRestoration source auxiliaries).expr_mkApps, List.mapM_append,
        (compilationRestoration source auxiliaries).mapM_expr_vars,
        (compilationRestoration source auxiliaries).mapM_expr_vars]
      simp only [Restoration.expr.go, hcfind, hcrec, vars_map_liftN, Nat.add_zero]
      rfl
  · -- an auxiliary family
    have hge : source.types.length ≤ owner.val := Nat.le_of_not_lt hsrc
    have hidx : owner.val - source.types.length < direct.length := by
      have := howner'; simp only [List.length_append] at this; omega
    have hFdirect := List.mapM_eq_some.mp hdirect
    have hauxLen : auxiliaries.length = direct.length :=
      Lean4Lean.List.Forall₂.length_eq hFdirect
    have hidx' : owner.val - source.types.length < auxiliaries.length := hauxLen ▸ hidx
    let a := auxiliaries[owner.val - source.types.length]'hidx'
    have ha : a ∈ auxiliaries := List.getElem_mem hidx'
    have hdf : a.directFamily source.uvars s.params =
        some (direct[owner.val - source.types.length]'hidx) :=
      Lean4Lean.List.forall₂_getElem hFdirect _ hidx' hidx
    have hdirectName : (direct[owner.val - source.types.length]'hidx).name = a.auxiliary :=
      ContainerSpecialization.directFamily_name hdf
    have hname' : s.families[owner].name = a.auxiliary := by
      rw [hname, List.getElem_append_right hge]
      exact hdirectName
    let h : HeadSpecialization :=
      ⟨a.auxiliary, source.uvars, source.nparams, a.source.name, a.levels, a.arguments⟩
    have hmem : h ∈ (compilationRestoration source auxiliaries).heads :=
      List.mem_flatMap.mpr ⟨a, ha, List.mem_cons_self⟩
    have hfind : (compilationRestoration source auxiliaries).heads.find?
        (fun h => h.auxiliary == s.families[owner].name) = some h := by
      rw [hname']
      exact Restoration.find?_of_nodup Hd.restorationScoped.1 hmem
    obtain ⟨-, hargsClosed, -, hlevelsWF, -⟩ := hwellFormed a ha
    have hclosed : ∀ arg ∈ h.arguments, arg.ClosedN h.nparams := hargsClosed
    have hclosedL : ∀ arg ∈ a.arguments, (arg.instL g.levels).ClosedN s.params.length := by
      intro arg harg
      rw [hnp]
      exact (hargsClosed arg harg).instL
    have hinst : ∀ k, a.arguments.map (fun arg => instantiateParams (arg.instL g.levels)
        (vars source.nparams k)) =
          a.arguments.map (fun arg => (arg.instL g.levels).liftN k) := by
      intro k
      apply List.map_congr_left
      intro arg harg
      rw [← hnp, instantiateParams_vars (hclosedL arg harg)]
    refine ⟨⟨a.source.name, a.levels.map (·.inst g.levels),
      a.arguments.map (fun arg => arg.instL g.levels)⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [Instance.restoredFamilyHead, Instance.familyApp,
        InductiveSignature.familyApp, List.append_nil]
      rw [(compilationRestoration source auxiliaries).expr_mkApps,
        (compilationRestoration source auxiliaries).mapM_expr_vars]
      simp only [Option.bind_some, Restoration.expr.go, hfind, HeadSpecialization.apply,
        hlevelsLen, h, bne_self_eq_false, Bool.false_or, vars_length', hnp]
      rw [if_neg (by simp), List.take_of_length_le (by simp),
        List.drop_of_length_le (by simp), hinst 0]
      simp only [VExpr.liftN_zero, Option.pure_def, Option.bind_eq_bind, Option.bind_some,
        List.append_nil, VerifyInductive.VExpr.getAppFnArgs_mkApps]
      rfl
    · simp only [Restoration.restoredHeadName, hfind, h]
    · intro level hlevel
      obtain ⟨l, -, rfl⟩ := List.mem_map.mp hlevel
      exact VLevel.WF.inst Hadm.levels_wf
    · intro arg' harg'
      obtain ⟨arg, harg, rfl⟩ := List.mem_map.mp harg'
      exact hclosedL arg harg
    · rw [show g.familyApp owner _ _ = g.recursorMajor owner from rfl,
        (compilationRestoration source auxiliaries).expr_recursorMajor_auxiliary g owner hfind
          hlevelsLen hnp.symm hclosed]
      simp only [List.map_map, Function.comp_def, h]
    · intro index hindex
      obtain ⟨sc, hsc, hscName⟩ := hctorName index hindex
      rw [List.getElem_append_right hge] at hsc
      have hheads := a.directFamily_heads hdf
      simp only [ContainerSpecialization.heads, List.map_cons, List.map_map,
        List.cons.injEq] at hheads
      have hscMem : sc.name ∈ a.source.ctors.map a.constructorName := by
        have : sc.name ∈ (direct[owner.val - source.types.length]'hidx).ctors.map (·.name) :=
          List.mem_map_of_mem hsc
        rw [← hheads.2] at this
        simpa [Function.comp_def] using this
      obtain ⟨ctor, hctor, hctorName'⟩ := List.mem_map.mp hscMem
      have hcName : s.constructors[index].name = a.constructorName ctor :=
        hscName.trans hctorName'.symm
      let hc : HeadSpecialization :=
        ⟨a.constructorName ctor, source.uvars, source.nparams, ctor.name, a.levels,
          a.arguments⟩
      have hcmem : hc ∈ (compilationRestoration source auxiliaries).heads :=
        List.mem_flatMap.mpr ⟨a, ha, List.mem_cons_of_mem _
          (List.mem_map.mpr ⟨ctor, hctor, rfl⟩)⟩
      have hcfind : (compilationRestoration source auxiliaries).heads.find?
          (fun h => h.auxiliary == s.constructors[index].name) = some hc := by
        rw [hcName]
        exact Restoration.find?_of_nodup Hd.restorationScoped.1 hcmem
      have hchead : (compilationRestoration source auxiliaries).restoredHeadName
          s.constructors[index].name = ctor.name := by
        simp only [Restoration.restoredHeadName, hcfind, hc]
      refine ⟨.inr ⟨a, ha, hname', ctor, hctor, hcName⟩, ?_⟩
      rw [hchead]
      simp only [Instance.constructorApp]
      rw [(compilationRestoration source auxiliaries).expr_mkApps, List.mapM_append,
        (compilationRestoration source auxiliaries).mapM_expr_vars,
        (compilationRestoration source auxiliaries).mapM_expr_vars]
      simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def,
        Restoration.expr.go, hcfind, HeadSpecialization.apply,
        hlevelsLen, hc, bne_self_eq_false, Bool.false_or, List.length_append, vars_length',
        hnp, Nat.add_zero]
      rw [if_neg (by simp), List.take_left' (vars_length' _ _),
        List.drop_left' (vars_length' _ _), hinst]
      simp only [List.map_map, Function.comp_def]

end InductiveSignature

namespace VerifyInductive

open private Lean.Kernel.Environment.add from Lean.Environment

private theorem forall₂_imp_mem_right {R S : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ →
      (∀ a b, b ∈ l₂ → R a b → S a b) → List.Forall₂ S l₁ l₂
  | _, _, .nil, _ => .nil
  | _, _, .cons h t, H =>
    .cons (H _ _ List.mem_cons_self h)
      (forall₂_imp_mem_right t fun a b hb h => H a b (List.mem_cons_of_mem _ hb) h)

/-! ### The installed restored recursors -/

/-- The restored recursor of one inductive restoration step is an entry of a
fresh trace of that step. -/
theorem RestoredInductiveDeclResult.freshTraceWithRecInfo
    (H : RestoredInductiveDeclResult result loweredEnv sourceEnv auxRec
      allIndNames indType oldInfo ((), targetEnv))
    (hwf : sourceEnv.constants.WF) :
    ∃ entries, FreshConstantTrace sourceEnv entries targetEnv ∧
      ConstantInfo.recInfo H.recursor.restored.newInfo ∈ entries := by
  let header : ConstantInfo := .inductInfo H.header.newInfo
  have hheaderEnv : H.headerEnv = sourceEnv.add header :=
    congrArg Prod.snd H.header.output
  have hheaderFresh : sourceEnv.find? header.name = none :=
    find?_none_of_contains_false hwf H.header.fresh
  have hwfHeader := constantsWF_add_checked hwf hheaderFresh
  have Hconstructors' : StateForMTrace
      (RestoredConstructorStep result loweredEnv) oldInfo.ctors
      (sourceEnv.add header) H.constructorEnv := by
    rw [← hheaderEnv]
    exact H.constructors
  rcases Hconstructors'.constructorFreshTrace hwfHeader with
    ⟨constructors, Hconstructors⟩
  have hwfConstructors : H.constructorEnv.constants.WF :=
    Hconstructors.targetWF hwfHeader
  let recursor : ConstantInfo := .recInfo H.recursor.restored.newInfo
  have htarget : targetEnv = H.constructorEnv.add recursor :=
    congrArg Prod.snd H.recursor.restored.output
  have hrecFresh : H.constructorEnv.find? recursor.name = none :=
    find?_none_of_contains_false hwfConstructors H.recursor.restored.fresh
  refine ⟨header :: constructors ++ [recursor], ?_, by simp [recursor]⟩
  rw [htarget]
  exact FreshConstantTrace.cons hheaderFresh
    (Hconstructors.append (.cons hrecFresh .nil))

theorem StateForMTrace.inductiveFreshTraceWithRecInfos
    (H : StateForMTrace
      (RestoredInductiveStep result loweredEnv auxRec allIndNames)
      types sourceEnv targetEnv)
    (hwf : sourceEnv.constants.WF) :
    ∃ entries, FreshConstantTrace sourceEnv entries targetEnv ∧
      ∀ t ∈ types, ∃ (s t' : Environment) (Hs : RestoredRecursorStep result loweredEnv
        auxRec allIndNames (Lean.mkRecName t.name) s t'),
        ConstantInfo.recInfo Hs.restored.newInfo ∈ entries := by
  induction H with
  | nil => exact ⟨[], .nil, by simp⟩
  | cons Hstep _Htail ih =>
    rcases Hstep.restored.freshTraceWithRecInfo hwf with ⟨headEntries, Hhead, hmem⟩
    rcases ih (Hhead.targetWF hwf) with ⟨tailEntries, Htail, htail⟩
    refine ⟨headEntries ++ tailEntries, Hhead.append Htail, ?_⟩
    intro t ht
    simp only [List.mem_cons] at ht
    rcases ht with rfl | ht
    · exact ⟨_, _, Hstep.restored.recursor, by simp [hmem]⟩
    · rcases htail t ht with ⟨s, t', Hs, hs⟩
      exact ⟨s, t', Hs, by simp [hs]⟩

theorem StateForMTrace.recursorFreshTraceWithRecInfos
    (H : StateForMTrace
      (RestoredRecursorStep result loweredEnv auxRec allIndNames)
      names sourceEnv targetEnv)
    (hwf : sourceEnv.constants.WF) :
    ∃ entries, FreshConstantTrace sourceEnv entries targetEnv ∧
      ∀ n ∈ names, ∃ (s t : Environment) (Hs : RestoredRecursorStep result loweredEnv
        auxRec allIndNames n s t),
        ConstantInfo.recInfo Hs.restored.newInfo ∈ entries := by
  induction H with
  | nil => exact ⟨[], .nil, by simp⟩
  | cons Hstep Htail ih =>
    let ci : ConstantInfo := .recInfo Hstep.restored.newInfo
    have hfresh :=
      find?_none_of_contains_false hwf Hstep.restored.fresh
    have htarget := congrArg Prod.snd Hstep.restored.output
    simp only at htarget
    rw [htarget] at Htail ih
    rcases ih (constantsWF_add_checked hwf hfresh) with ⟨entries, Hentries, hnames⟩
    refine ⟨ci :: entries, .cons hfresh Hentries, ?_⟩
    intro n hn
    simp only [List.mem_cons] at hn
    rcases hn with rfl | hn
    · exact ⟨_, _, Hstep, by simp [ci]⟩
    · rcases hnames n hn with ⟨s, t, Hs, hs⟩
      exact ⟨s, t, Hs, by simp [hs]⟩

/-- Every restoration step at a restored recursor name of a complete nested
restoration installs its restored recursor in the output environment. -/
theorem RestoredNestedDeclarationsResult.find_restoredRecursor
    (H : RestoredNestedDeclarationsResult result loweredEnv sourceEnv auxRec
      allIndNames types auxRecNames out)
    (hwf : sourceEnv.constants.WF)
    {n : Name} (hn : n ∈ types.map (fun t => Lean.mkRecName t.name) ++ auxRecNames)
    {s t : Environment}
    (Hstep : RestoredRecursorStep result loweredEnv auxRec allIndNames n s t) :
    out.2.find? Hstep.restored.newInfo.name =
      some (.recInfo Hstep.restored.newInfo) := by
  rcases H.inductives.inductiveFreshTraceWithRecInfos hwf with
    ⟨primaryEntries, Hprimary, hprimary⟩
  rcases H.auxiliaries.recursorFreshTraceWithRecInfos (Hprimary.targetWF hwf) with
    ⟨auxiliaryEntries, Hauxiliary, hauxiliary⟩
  have Htrace := Hprimary.append Hauxiliary
  have hmem : ∃ (s' t' : Environment) (Hs : RestoredRecursorStep result loweredEnv
      auxRec allIndNames n s' t'),
      ConstantInfo.recInfo Hs.restored.newInfo ∈ primaryEntries ++ auxiliaryEntries := by
    rcases List.mem_append.mp hn with hn | hn
    · obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hn
      obtain ⟨s', t', Hs, hs⟩ := hprimary t ht
      exact ⟨s', t', Hs, List.mem_append_left _ hs⟩
    · obtain ⟨s', t', Hs, hs⟩ := hauxiliary n hn
      exact ⟨s', t', Hs, List.mem_append_right _ hs⟩
  obtain ⟨s', t', Hs, hs⟩ := hmem
  have hsame := (Hs.info_eq Hstep).2
  rw [← hsame]
  exact Htrace.findEntry hwf hs

/-- Every installed entry of a staged constant list has the name of its
abstract value. -/
theorem AddConstants.name_eq
    (H : AddConstants safety env venv entries outEnv outVEnv) :
    ∀ entry ∈ entries, entry.1.name = entry.2.name := by
  induction H with
  | nil => simp
  | cons _ _ htr _ _ _ _ ih =>
    intro entry hentry
    simp only [List.mem_cons] at hentry
    rcases hentry with rfl | hentry
    · exact htr.2
    · exact ih entry hentry

/-- The recursor entries of a final assembly shape are installed in the
output environment under the names of their abstract values. -/
theorem NestedFinalAssemblyShape.find_recursorEntry
    {result : Lean4Lean.ElimNestedInductive.Result}
    {loweredEnv sourceProdEnv : Environment} {auxRec : NameMap Name}
    {allIndNames : List Name} {sourceTypes : List InductiveType}
    {auxRecNames : List Name} {outEnv : Environment}
    {sourceEnv : VEnv} {decl : VInductDecl} {lparams : List Name}
    {nparams : Nat} {isUnsafe : Bool} {safety : DefinitionSafety}
    {H : RestoredNestedDeclarationsResult result loweredEnv sourceProdEnv
      auxRec allIndNames sourceTypes auxRecNames ((), outEnv)}
    (C : NestedFinalAssemblyShape H sourceEnv decl lparams nparams isUnsafe safety)
    (hwf : sourceProdEnv.constants.WF) :
    ∀ entry ∈ C.recursorEntries,
      outEnv.find? entry.2.name = some entry.1 := by
  intro entry hentry
  rcases H.freshTrace hwf with ⟨actual, Hactual⟩
  have hperm := C.productionOrder actual Hactual
  have hmem : entry.1 ∈ actual := hperm.symm.mem_iff.mp
    (List.mem_map.mpr ⟨entry, List.mem_append_right _ hentry, rfl⟩)
  rw [← C.canonical.recursorsAdded.name_eq entry hentry]
  exact Hactual.findEntry hwf hmem

/-- `compilationData_of_hitShape'` at a given specialization list of
`restorationTablesRestoringAll` (rather than at an existentially chosen one):
the restored recursors and equations of the canonical restored block of a
shape whose rules realize the executable restored rules form a
`CompilationData`, and the specializations are certified. -/
theorem NestedValidatedRunResult.compilationData_of_tables
    {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}
    (E : NestedValidatedRunResult result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (wf : ves.WF sourceProdEnv) (Hsources : SourceSyntaxChecks sourceTypes)
    (C : NestedFinalAssemblyShape E.restoration
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe))
    (hC : C.production = E.production)
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
    (HauxRestoring : List.Forall₂ (VInductDecl.NestedTypeExpansion
          (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl
          ((compilationRestoration sourceDecl auxiliaries).RestoringLeaf
            (VLevel.params sourceDecl.uvars)))
        generated (E.production.loweredDecl.types.drop sourceDecl.types.length))
    (hrealization : E.RestoredRulesRealization (compilationRestoration sourceDecl auxiliaries)
      (C.primaryRules ++ C.auxiliaryRules)) :
    CertifiedSpecializations (ves.venv (if isUnsafe then .unsafe else .safe))
        auxiliaries ∧
      Nonempty (CompilationData (ves.venv (if isUnsafe then .unsafe else .safe))
        sourceDecl E.production.loweredDecl E.production.compilationSignature
        E.production.compilationInstance auxiliaries
        (canonicalRestoredBlock sourceDecl C.primaryRecursors
          C.auxiliaryRecursors C.primaryRules C.auxiliaryRules)) := by
  have hnodup :
      (familyNames E.production.loweredDecl.types ++
        E.production.loweredDecl.types.map (fun t => t.name.str "rec")).Nodup := by
    rcases E.containerSpecializations wf Hsources with
      ⟨_, _, _, _, _, _, _, h, _⟩
    exact h
  let r := compilationRestoration sourceDecl auxiliaries
  have hfreshAll := E.restorableNames_fresh hadded Haux Hexpansion hnodup
  have hfresh : ∀ name ∈ r.heads.map (·.auxiliary), envTypes.constants name = none :=
    fun name hname => hfreshAll name (List.mem_append_left _ hname)
  have hrecFresh : ∀ p ∈ r.recursors, envTypes.constants p.1 = none :=
    fun p hp => hfreshAll p.1 (List.mem_append_right _ (List.mem_map_of_mem hp))
  have hP := E.restorationPrefix_of wf hadded henvTypes Haux Hexpansion hnodup D True.intro
  obtain ⟨-, -, hnames, hheadNames, hcertified, -, hwellFormed, hscoped, hdirect, -⟩ := hP
  have hlevels := E.loweredConstructorLevels_heads wf Hsources hheadNames
  have hrecursors := E.restoredRecursors_of_hitShape C hC wf Hsources hadded Haux Hexpansion
    hnodup hparamsSize D hscoped
  have hheads : r.heads.map (·.auxiliary) = E.auxHeads := by
    rw [compilationRestoration_heads_auxiliary]
    exact auxiliarySpecializations_headNames Haux Hexpansion
  have hequations := E.restoredEquations_of_hitShape C wf Hsources hheads hparamsSize D hscoped
    hrealization
  have htotal := E.normalizedTotal_of wf Hsources hheadNames
  have HsourceCtors := E.sourceConstructors_of_evidence wf hadded henvTypes Haux Hexpansion
    hnodup hfresh hrecFresh
    ⟨E.loweredConstructors_of_evidence hadded henvTypes hfreshAll Hrestoring hlevels,
      fun n hn => htotal n (List.mem_of_mem_take hn)⟩
  have HauxFamilies := E.auxiliaryFamiliesField_of_evidence wf hadded henvTypes Haux
    Hexpansion
    (E.auxiliaryConstructors_of_evidence wf Hsources hadded henvTypes Haux Hexpansion
      HauxRestoring hnodup (fun n hn => htotal n (List.mem_of_mem_drop hn)))
  exact ⟨hcertified, ⟨E.compilationData_of_specializations C hC hadded hnames hwellFormed
    hscoped hdirect
    { sourceConstructors := HsourceCtors
      auxiliaryFamilies := HauxFamilies
      recursors := hrecursors
      equations := hequations }⟩⟩

/-- The recursor entries of a final assembly shape of a validated nested run,
in owner order: each entry's concrete constant is the restored recursor of a
restoration step at the owner's lowered recursor name, and its abstract value
is the abstract restoration of the owner's generated recursor and the
translation of that restored recursor. -/
theorem NestedValidatedRunResult.restoredRecursorEntryInfos
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
    (hC : C.production = E.production)
    (wf : ves.WF sourceProdEnv) (Hsources : SourceSyntaxChecks sourceTypes)
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
    (hwf : sourceProdEnv.constants.WF) :
    List.Forall₂ (fun owner (entry : ConstantInfo × VConstVal) =>
        ∃ (s t : Environment) (Hstep : RestoredRecursorStep result E.loweredEnv
          (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2
          (sourceTypes.map (·.name))
          (E.production.production.completed.canonicalGeneration.recursorName owner) s t),
          entry.1 = .recInfo Hstep.restored.newInfo ∧
          (compilationRestoration sourceDecl auxiliaries).recursor
            (E.production.production.completed.canonicalGeneration.recursor owner) =
              some entry.2 ∧
          RestoredRecursorStepValue
            (C.canonical.venvCtors.addProjections sourceDecl.projectionEntries) Hstep
            entry.2)
      (List.finRange
        E.production.production.completed.generationSignature.families.size)
      C.recursorEntries := by
  have Hentries := E.restoredRecursorEntries_of_hitShape C hC wf Hsources hadded Haux Hexpansion
    hnodup hparamsSize D hscoped
  rw [← C.recursorValues, List.forall₂_map_right_iff] at Hentries
  have hnames := E.recursorNames_order C.sourceNonempty
  have hrecursorEntries : ∀ entry ∈ C.recursorEntries,
      outEnv.find? entry.2.name = some entry.1 := C.find_recursorEntry hwf
  refine forall₂_imp_mem_right Hentries ?_
  rintro owner entry hentry ⟨hrec, s, t, Hstep, Hw⟩
  refine ⟨s, t, Hstep, ?_, hrec, Hw⟩
  have hn : E.production.production.completed.canonicalGeneration.recursorName owner ∈
      sourceTypes.map (fun t => Lean.mkRecName t.name) ++
        (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).1 := by
    rw [← hnames]
    exact List.mem_map_of_mem (List.mem_finRange owner)
  have hfind := E.restoration.find_restoredRecursor hwf hn Hstep
  have hname : entry.2.name = Hstep.restored.newInfo.name :=
    Hw.1.trans Hstep.restored.restoration.name.symm
  have hfind' := hrecursorEntries entry hentry
  rw [hname] at hfind'
  exact Option.some.inj (hfind'.symm.trans hfind)

/-! ### The major inductive of a restored recursor -/

/-- **The major inductive of a restored recursor** is the restored head of its
generated owner family. -/
theorem NestedValidatedRunResult.restoredMajorInduct
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
    (owner : Fin E.production.compilationSignature.families.size)
    {s t : Environment}
    (Hstep : RestoredRecursorStep result E.loweredEnv
      (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2
      (sourceTypes.map (·.name))
      (E.production.compilationInstance.recursorName owner) s t) :
    Hstep.restored.newInfo.getMajorInduct =
      (compilationRestoration sourceDecl auxiliaries).restoredHeadName
        E.production.compilationSignature.families[owner].name := by
  let r := compilationRestoration sourceDecl auxiliaries
  have hheads : r.heads.map (·.auxiliary) = E.auxHeads := by
    rw [compilationRestoration_heads_auxiliary]
    exact auxiliarySpecializations_headNames Haux Hexpansion
  have hfamNodup : (familyNames (E.production.loweredDecl.types.take sourceDecl.types.length) ++
      familyNames (E.production.loweredDecl.types.drop sourceDecl.types.length)).Nodup := by
    have h := (List.nodup_append.mp hnodup).1
    rw [← List.take_append_drop sourceDecl.types.length E.production.loweredDecl.types] at h
    simpa only [familyNames, List.flatMap_append] using h
  have hfamRec : ∀ hi, (E.production.loweredDecl.types[owner.val]'hi).name ∉
      r.recursors.map Prod.fst := by
    intro hi hmem
    rw [compilationRestoration_recursors_fst] at hmem
    obtain ⟨a, ha, heq⟩ := List.mem_map.mp hmem
    have haux : a.auxiliary ∈
        (E.production.loweredDecl.types.drop sourceDecl.types.length).map (·.name) := by
      rw [← auxiliarySpecializations_names Haux Hexpansion]
      exact List.mem_map_of_mem ha
    obtain ⟨t, ht, hta⟩ := List.mem_map.mp haux
    have h1 : (E.production.loweredDecl.types[owner.val]'hi).name ∈
        familyNames E.production.loweredDecl.types :=
      mem_familyNames_of_type (List.getElem_mem hi)
    have h2 : (E.production.loweredDecl.types[owner.val]'hi).name ∈
        E.production.loweredDecl.types.map (fun t => t.name.str "rec") := by
      rw [← heq, ← hta]
      exact List.mem_map_of_mem (f := fun t : VInductiveType => t.name.str "rec")
        (List.mem_of_mem_drop ht)
    exact (List.nodup_append.mp hnodup).2.2 _ h1 _ h2 rfl
  have hfamKey : ∀ hi, (E.production.loweredDecl.types[owner.val]'hi).name ∈
      r.heads.map (·.auxiliary) →
      ∃ nested, result.aux2nested.find?
        (E.production.loweredDecl.types[owner.val]'hi).name = some nested := by
    intro hi hmem
    rw [hheads] at hmem
    by_cases hlt : owner.val < sourceDecl.types.length
    · exfalso
      have htake : E.production.loweredDecl.types[owner.val]'hi ∈
          E.production.loweredDecl.types.take sourceDecl.types.length :=
        List.mem_iff_getElem.mpr ⟨owner.val, by simp; omega, by simp⟩
      exact (List.nodup_append.mp hfamNodup).2.2 _ (mem_familyNames_of_type htake) _ hmem rfl
    · have hdrop : E.production.loweredDecl.types[owner.val]'hi ∈
          E.production.loweredDecl.types.drop sourceDecl.types.length :=
        List.mem_iff_getElem.mpr ⟨owner.val - sourceDecl.types.length, by simp; omega, by
          simp only [List.getElem_drop]; congr 1; omega⟩
      have hname := List.mem_map_of_mem (f := (·.name)) hdrop
      rw [← auxiliarySpecializations_names Haux Hexpansion] at hname
      obtain ⟨a, ha, haeq⟩ := List.mem_map.mp hname
      obtain ⟨nested, hnested⟩ := D.familyLookup a ha
      exact ⟨nested, haeq ▸ hnested⟩
  have hnestedHead : ∀ name nested, result.aux2nested.find? name = some nested →
      ∃ c ls, nested.getAppFn = .const c ls := by
    intro name nested h
    obtain ⟨I, ls, -, h1, -⟩ := E.auxNestedHead wf Hsources h
    exact ⟨I, ls, h1⟩
  obtain ⟨hi', domain, c, ls, Hbinder, hc, hdisj⟩ := E.restoredMajorHead wf Hsources
    (D.agreement VEnv.empty lparams) hheads hparamsSize D.paramsFVars hnestedHead owner Hstep
    hfamRec hfamKey
  have hmi : Hstep.restored.newInfo.getMajorInduct = c := by
    rw [RecursorVal.getMajorInduct_of_binderAt _ Hbinder, hc]
    rfl
  -- the lowered family name is the signature's
  have hfamName : (E.production.loweredDecl.types[owner.val]'hi').name =
      E.production.compilationSignature.families[owner].name := by
    obtain ⟨hi, hinfo⟩ := E.generatedEntryOfStep owner Hstep
    have h1 := E.production.production.completed.generated_getMajorInduct owner.val hi
    rw [hinfo] at h1
    exact h1.symm.trans (E.recursorMetadataOfStep owner Hstep).major
  rw [hmi, ← hfamName]
  rcases hdisj with ⟨hnot, hceq⟩ | ⟨nested, ls', hfind, hfn⟩
  · have hfind : r.heads.find? (fun h => h.auxiliary ==
        (E.production.loweredDecl.types[owner.val]'hi').name) = none :=
      Restoration.heads_find?_eq_none hnot
    simp only [Restoration.restoredHeadName, r] at hfind ⊢
    rw [hfind, hceq]
  · obtain ⟨b, hb, hbaux, envS, domains, lvls, Ys, -, hab, -, -⟩ := D.familyKey _ nested hfind
    have hhead : nested.getAppFn = .const b.source.name lvls := by
      obtain ⟨xs, hxs⟩ := D.paramsFVars
      rw [hxs, Expr.abstractN_eq] at hab
      exact abstractN_getAppFn_const nested 0
        (by rw [hab, Expr.getAppFn_mkAppList_const])
    rw [hfn] at hhead
    have hcb : c = b.source.name := (Expr.const.inj hhead).1
    have hmem : (⟨b.auxiliary, sourceDecl.uvars, sourceDecl.nparams, b.source.name, b.levels,
        b.arguments⟩ : HeadSpecialization) ∈ r.heads :=
      List.mem_flatMap.mpr ⟨b, hb, List.mem_cons_self⟩
    have hfindB := Restoration.find?_of_nodup hscoped.1 hmem
    rw [hbaux] at hfindB
    simp only [Restoration.restoredHeadName] at hfindB ⊢
    rw [hfindB, hcb]

/-- The specialization clause of `RestoredRecursorRealization`. -/
def RestoredRecursorSpecialization {s : InductiveSignature} (g : Instance s)
    (r : Restoration) (venv : VEnv) (owner : Fin s.families.size)
    (rec : Lean.RecursorVal) : Prop :=
  ∃ head,
    g.restoredFamilyHead r owner = some head ∧
    rec.getMajorInduct = head.name ∧
    (∀ level ∈ head.levels, level.WF g.uvars) ∧
    (∀ arg ∈ head.arguments, arg.ClosedN s.params.length) ∧
    r.expr (g.familyApp owner
      (vars s.params.length
        (s.families.size + s.constructors.size + s.families[owner].indices.length))
      (vars s.families[owner].indices.length 0)) =
      some (VExpr.mkApps (.const head.name head.levels)
        (head.arguments.map (fun arg => arg.liftN
          (s.families.size + s.constructors.size + s.families[owner].indices.length)) ++
          vars s.families[owner].indices.length 0)) ∧
    List.Forall₂ (RestoredRuleRealization g r venv rec.levelParams head)
      (s.ownedConstructors owner) rec.rules

/-- **One restored recursor realization**, modulo its specialization clause:
the restored recursor of a restoration step at a generated owner's lowered
recursor name realizes the owner's restored generated recursor. -/
theorem NestedValidatedRunResult.restoredRecursorRealization_of_step
    {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceEnv : VEnv} {sourceDecl : VInductDecl} {lparams : List Name}
    {nparams : Nat} {isUnsafe : Bool} {safety : DefinitionSafety}
    {outEnv : Environment}
    (E : NestedValidatedRunResult result sourceProdEnv sourceTypes sourceEnv
      sourceDecl lparams nparams isUnsafe safety outEnv)
    {auxiliaries : List ContainerSpecialization}
    (D : RestorationTableData sourceDecl auxiliaries result E.loweredEnv
      (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 lparams)
    (hnames : sourceTypes.map (·.name) = sourceDecl.types.map (·.name))
    (owner : Fin E.production.compilationSignature.families.size)
    {s t : Environment}
    (Hstep : RestoredRecursorStep result E.loweredEnv
      (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2
      (sourceTypes.map (·.name))
      (E.production.compilationInstance.recursorName owner) s t)
    {trEnv venv : VEnv} (hle : trEnv ≤ venv) {w : VConstVal}
    (hrec : (compilationRestoration sourceDecl auxiliaries).recursor
      (E.production.compilationInstance.recursor owner) = some w)
    (Hw : RestoredRecursorStepValue trEnv Hstep w)
    (Hspec : RestoredRecursorSpecialization E.production.compilationInstance
      (compilationRestoration sourceDecl auxiliaries) venv owner Hstep.restored.newInfo) :
    RestoredRecursorRealization E.production.compilationInstance
      (compilationRestoration sourceDecl auxiliaries) (sourceDecl.types.map (·.name))
      venv owner Hstep.restored.newInfo := by
  have M := E.recursorMetadataOfStep owner Hstep
  have R := Hstep.restored.restoration
  obtain ⟨hwname, hwuvars, Ht⟩ := Hw
  refine {
    name := ?_
    uvars := ?_
    type := ?_
    numParams := R.numParams.trans M.numParams
    numIndices := R.numIndices.trans M.numIndices
    numMotives := R.numMotives.trans M.numMotives
    numMinors := R.numMinors.trans M.numMinors
    all := ?_
    isUnsafe := R.isUnsafe.trans M.isUnsafe
    specialization := Hspec
    k := fun hk => M.k (R.k ▸ hk) }
  · rw [D.recursorName, R.name, Hstep.restored.mappedName]
    exact nameMap_getD_eq _ _ _
  · rw [R.levelParams]; exact M.uvars
  · simp only [Restoration.recursor, Option.bind_eq_bind, Option.pure_def] at hrec
    cases ht : (compilationRestoration sourceDecl auxiliaries).expr
        (E.production.compilationInstance.recursor owner).type with
    | none => simp [ht] at hrec
    | some type =>
      simp only [ht, Option.bind_some, Option.some.injEq] at hrec
      subst hrec
      exact ⟨type, ht, Ht.mono hle⟩
  · rw [R.all, hnames]

private theorem mem_zipIdx_of_mem' {l : List α} {x : α} (h : x ∈ l) :
    ∃ i, (x, i) ∈ l.zipIdx := by
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp h
  exact ⟨i, List.mk_mem_zipIdx_iff_getElem?.mpr hi⟩

/-- **The restored rules of one restored recursor.** Given the restored
family head of its owner (with the constructor restorations of
`CompilationData.restoredFamilyHead_spec`), every rule of the restored
recursor of a restoration step realizes its generated constructor, against
the canonical restored rule list, in an abstract environment in which the
restored recursor is installed and the restorable names are fresh. -/
theorem NestedValidatedRunResult.restoredRuleRealizations
    {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceEnv : VEnv} {sourceDecl : VInductDecl} {lparams : List Name}
    {nparams : Nat} {isUnsafe : Bool} {safety : DefinitionSafety}
    {outEnv : Environment}
    (E : NestedValidatedRunResult result sourceProdEnv sourceTypes sourceEnv
      sourceDecl lparams nparams isUnsafe safety outEnv)
    {auxiliaries : List ContainerSpecialization} {venv : VEnv} {rules : List VDefEq}
    (D : RestorationTableData sourceDecl auxiliaries result E.loweredEnv
      (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 lparams)
    (hctorNames : ∀ a ∈ auxiliaries, ∀ ctor ∈ a.source.ctors,
      result.restoreCtorName E.loweredEnv (a.constructorName ctor) =
        (compilationRestoration sourceDecl auxiliaries).restoredHeadName
          (a.constructorName ctor))
    (hrecNames : ∀ owner, E.production.compilationInstance.recursorName owner =
      E.production.compilationSignature.families[owner].name.str "rec")
    (hheadsNotRec : ∀ owner, ∀ head ∈ (compilationRestoration sourceDecl auxiliaries).heads,
      head.auxiliary ≠ E.production.compilationInstance.recursorName owner)
    (hfreshFinal : ∀ n ∈ (compilationRestoration sourceDecl auxiliaries).restorableNames,
      venv.constants n = none)
    (hequations : E.production.compilationInstance.restoredEquations
      (compilationRestoration sourceDecl auxiliaries) = some rules)
    (Hrules : List.Forall₂
      (E.RestoredRuleRealization (compilationRestoration sourceDecl auxiliaries) venv)
      (List.finRange E.production.compilationSignature.constructors.size) rules)
    (owner : Fin E.production.compilationSignature.families.size)
    {s t : Environment}
    (Hstep : RestoredRecursorStep result E.loweredEnv
      (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2
      (sourceTypes.map (·.name))
      (E.production.compilationInstance.recursorName owner) s t)
    (hinstalled : venv.constants Hstep.restored.newInfo.name ≠ none)
    (head : RestoredFamilyHead)
    (Hctor : ∀ index : Fin E.production.compilationSignature.constructors.size,
      E.production.compilationSignature.constructors[index].owner = owner →
        (((compilationRestoration sourceDecl auxiliaries).heads.find?
            (fun h => h.auxiliary ==
              E.production.compilationSignature.families[owner].name) = none ∧
          (compilationRestoration sourceDecl auxiliaries).restoredHeadName
            E.production.compilationSignature.constructors[index].name =
              E.production.compilationSignature.constructors[index].name) ∨
          ∃ a ∈ auxiliaries, E.production.compilationSignature.families[owner].name =
              a.auxiliary ∧
            ∃ ctor ∈ a.source.ctors, E.production.compilationSignature.constructors[index].name =
              a.constructorName ctor) ∧
        (compilationRestoration sourceDecl auxiliaries).expr
          (E.production.compilationInstance.constructorApp
            E.production.compilationSignature.constructors[index]
            (E.production.compilationSignature.families.size +
              E.production.compilationSignature.constructors.size) 0) =
          some (VExpr.mkApps (.const ((compilationRestoration sourceDecl auxiliaries).restoredHeadName
              E.production.compilationSignature.constructors[index].name) head.levels)
            (head.arguments.map (fun arg => arg.liftN
              (E.production.compilationSignature.families.size +
                E.production.compilationSignature.constructors.size +
                E.production.compilationSignature.constructors[index].fields.length)) ++
              vars E.production.compilationSignature.constructors[index].fields.length 0))) :
    List.Forall₂ (InductiveSignature.RestoredRuleRealization E.production.compilationInstance
        (compilationRestoration sourceDecl auxiliaries) venv
        Hstep.restored.newInfo.levelParams head)
      (E.production.compilationSignature.ownedConstructors owner)
      Hstep.restored.newInfo.rules := by
  let P := E.production.production.completed
  obtain ⟨hi, hinfo⟩ := E.generatedEntryOfStep owner Hstep
  have RR := P.ruleRealizations P.ruleRhsTranslations owner hi
  rw [hinfo] at RR
  have hmap := P.ownedConstructors_map_val owner hi
  rw [hinfo] at hmap
  have R := Hstep.restored.restoration
  have hlenNew : Hstep.restored.newInfo.rules.length = Hstep.oldInfo.rules.length :=
    R.rules.length
  have hlenOwned : (E.production.compilationSignature.ownedConstructors owner).length =
      Hstep.oldInfo.rules.length := by
    have h2 : (P.generationSignature.ownedConstructors owner).length =
        Hstep.oldInfo.rules.length := by
      simpa using congrArg List.length hmap
    exact h2
  -- the equation list, pointwise
  have Heqs := List.mapM_eq_some.mp hequations
  have hlenRules : rules.length = E.production.compilationSignature.constructors.size := by
    have h1 := Lean4Lean.List.Forall₂.length_eq Hrules
    have h2 : (List.finRange E.production.compilationSignature.constructors.size).length =
        E.production.compilationSignature.constructors.size := List.length_finRange
    exact h1.symm.trans h2
  apply Lean4Lean.List.forall₂_of_getElem (hlenOwned.trans hlenNew.symm)
  intro j hj hjNew
  have hjOld : j < Hstep.oldInfo.rules.length := hlenOwned ▸ hj
  have hval := RuleAssembly.getElem_of_map_val_eq hmap j hj
  let index := (E.production.compilationSignature.ownedConstructors owner)[j]
  have hindexOwner : E.production.compilationSignature.constructors[index].owner = owner := by
    have hmem : index ∈ E.production.compilationSignature.ownedConstructors owner :=
      List.getElem_mem hj
    simp only [InductiveSignature.ownedConstructors, List.mem_filter, beq_iff_eq] at hmem
    exact hmem.2
  have RRj := Lean4Lean.List.forall₂_getElem RR j hj hjOld
  have Rj := R.rules.entry j hjOld hjNew
  obtain ⟨hclass, happ⟩ := Hctor index hindexOwner
  -- the restored constructor name
  have hrecMem : ∀ a ∈ auxiliaries, a.auxiliary.str "rec" ∈
      (compilationRestoration sourceDecl auxiliaries).recursors.map Prod.fst := by
    intro a ha
    obtain ⟨i, hi⟩ := mem_zipIdx_of_mem' ha
    exact List.mem_map.mpr ⟨_, List.mem_map.mpr ⟨(a, i), hi, rfl⟩, rfl⟩
  -- the restored constructor name
  have hctor : (Hstep.restored.newInfo.rules[j]'hjNew).ctor =
      (compilationRestoration sourceDecl auxiliaries).restoredHeadName
        E.production.compilationSignature.constructors[index].name := by
    rw [Rj.ctor, RRj.ctor]
    rcases hclass with ⟨hfind, hheadId⟩ | ⟨a, ha, hfam, ctor, hctor, hcName⟩
    · have hnotRec : E.production.compilationInstance.recursorName owner ∉
          (compilationRestoration sourceDecl auxiliaries).recursors.map Prod.fst := by
        intro hmem
        obtain ⟨pair, hpair, hpairName⟩ := List.mem_map.mp hmem
        obtain ⟨⟨a, i⟩, hai, rfl⟩ := List.mem_map.mp hpair
        have ha : a ∈ auxiliaries := List.fst_mem_of_mem_zipIdx hai
        have hfamName : E.production.compilationSignature.families[owner].name =
            a.auxiliary := by
          have h := hpairName.trans (hrecNames owner)
          exact (Name.str.inj h).1.symm
        have hmemHead : (⟨a.auxiliary, sourceDecl.uvars, sourceDecl.nparams, a.source.name,
            a.levels, a.arguments⟩ : HeadSpecialization) ∈
              (compilationRestoration sourceDecl auxiliaries).heads :=
          List.mem_flatMap.mpr ⟨a, ha, List.mem_cons_self⟩
        have := List.find?_eq_none.mp hfind _ hmemHead
        simp only [beq_iff_eq] at this
        exact this (by simpa using hfamName.symm)
      have hsame : Hstep.restored.newRecName =
          E.production.compilationInstance.recursorName owner := by
        rw [Hstep.restored.mappedName, nameMap_getD_eq, ← D.recursorName]
        exact Restoration.recursorName_of_not_mem hnotRec
      simp only [hsame, beq_self_eq_true, if_true]
      exact hheadId.symm
    · have hold : E.production.compilationInstance.recursorName owner =
          a.auxiliary.str "rec" := by
        rw [hrecNames owner, hfam]
      have hfreshOld : venv.constants (E.production.compilationInstance.recursorName owner) =
          none := by
        rw [hold]
        exact hfreshFinal _ (List.mem_append_right _ (hrecMem a ha))
      have hne : (Hstep.restored.newRecName ==
          E.production.compilationInstance.recursorName owner) = false := by
        have : Hstep.restored.newRecName ≠
            E.production.compilationInstance.recursorName owner := by
          intro h
          apply hinstalled
          rw [R.name, h]
          exact hfreshOld
        simpa using this
      simp only [hne, Bool.false_eq_true, if_false]
      show result.restoreCtorName E.loweredEnv
          E.production.compilationSignature.constructors[index].name = _
      rw [hcName]
      exact hctorNames a ha ctor hctor
  have hindexLt : index.val < rules.length := by rw [hlenRules]; exact index.isLt
  have hindexEq : index.val < E.production.compilationInstance.equations.length := by
    simp [InductiveSignature.Instance.equations]
  have Heq := Lean4Lean.List.forall₂_getElem Heqs index.val hindexEq hindexLt
  have hgetEq : E.production.compilationInstance.equations[index.val]'hindexEq =
      E.production.compilationInstance.equation index := by
    simp [InductiveSignature.Instance.equations]
  rw [hgetEq] at Heq
  refine {
    ctor := hctor
    nfields := Rj.nfields.trans RRj.nfields
    constructorApplication := by rw [hctor]; exact happ
    equation := ⟨rules[index.val]'hindexLt, Heq, ?_, ?_⟩ }
  · have hleft : (compilationRestoration sourceDecl auxiliaries).expr
        (E.production.compilationInstance.equation index).lhs =
          some (rules[index.val]'hindexLt).lhs := by
      simp only [Restoration.equation, Option.bind_eq_bind, Option.pure_def] at Heq
      cases hl : (compilationRestoration sourceDecl auxiliaries).expr
          (E.production.compilationInstance.equation index).lhs with
      | none => simp [hl] at Heq
      | some lhs =>
        simp only [hl, Option.bind_some] at Heq
        cases hr : (compilationRestoration sourceDecl auxiliaries).expr
            (E.production.compilationInstance.equation index).rhs with
        | none => simp [hr] at Heq
        | some rhs =>
          simp only [hr, Option.bind_some] at Heq
          cases hty : (compilationRestoration sourceDecl auxiliaries).expr
              (E.production.compilationInstance.equation index).type with
          | none => simp [hty] at Heq
          | some ty =>
            simp only [hty, Option.bind_some, Option.some.injEq] at Heq
            rw [← Heq]
    exact Restoration.wrapLams_head_const
      (hheadsNotRec E.production.compilationSignature.constructors[index].owner)
      (VExpr.getAppFnArgs_mkApps_head _ _) hleft
  · -- the right-hand side, from the realization at the same flattened index
    have hfinLt : index.val <
        (List.finRange E.production.compilationSignature.constructors.size).length := by
      rw [List.length_finRange]; exact index.isLt
    have HR := Lean4Lean.List.forall₂_getElem Hrules index.val hfinLt hindexLt
    have hfv : ((List.finRange E.production.compilationSignature.constructors.size)[index.val]'
        hfinLt).val = index.val := by simp
    obtain ⟨owner', j', s', t', Hstep', hj', hk0, -, Ht, -, -⟩ := HR
    have hk' : index.val = recursorMinorOffset E.production.indTypes owner'.val + j' :=
      hfv.symm.trans hk0
    obtain ⟨hi', hinfo'⟩ := E.generatedEntryOfStep owner' Hstep'
    have hsrcOf : ∀ (o : Nat) (ho : o < P.entries.length), o < E.production.indTypes.size := by
      intro o ho
      have hrec : o < P.recInfos.size := by rw [← P.generated.length]; exact ho
      rw [← P.recInfos_size_eq_source]; exact hrec
    have hcntOf : ∀ (o : Nat) (ho : o < P.entries.length),
        (P.generated.entry o ho).info.rules.length =
          E.production.indTypes[o]!.ctors.length :=
      fun o ho => (P.generated.entry o ho).rules.length
    have hlocal : j < E.production.indTypes[owner.val]!.ctors.length := by
      rw [← hcntOf owner.val hi, hinfo]; exact hjOld
    have hlocal' : j' < E.production.indTypes[owner'.val]!.ctors.length := by
      rw [← hcntOf owner'.val hi', hinfo', ← Hstep'.restored.restoration.rules.length]
      exact hj'
    obtain ⟨howner, hjj⟩ := recursorMinorOffset_unique E.production.indTypes
      (hsrcOf owner.val hi) (hsrcOf owner'.val hi') hlocal hlocal' (hval.symm.trans hk')
    subst hjj
    have hownerEq : owner' = owner := Fin.ext howner.symm
    subst hownerEq
    have hnew := (Hstep'.info_eq Hstep).2
    have key : ∀ (info : RecursorVal) (h : j < info.rules.length),
        info = Hstep.restored.newInfo →
        TrExprS venv info.levelParams [] (info.rules[j]'h).rhs
          (rules[index.val]'hindexLt).rhs →
        TrExprS venv Hstep.restored.newInfo.levelParams []
          (Hstep.restored.newInfo.rules[j]'hjNew).rhs (rules[index.val]'hindexLt).rhs := by
      intro info h hinfo'' H
      subst hinfo''
      exact H
    exact key _ hj' hnew Ht

private theorem names_of_trTypes {env envTypes : VEnv} {lparams : List Name} :
    ∀ {types : List InductiveType} {decls : List VInductiveType},
      List.Forall₂ (TrInductiveType env envTypes lparams) types decls →
      types.map (·.name) = decls.map (·.name)
  | _, _, .nil => rfl
  | _, _, .cons h t => by
    simp only [List.map_cons, names_of_trTypes t, List.cons.injEq, and_true]
    exact h.header.name.symm

/-- **Final assembly certificate of a validated nested run**, modulo the rule
junction `Hrules` and the recursor provenance `Hprovenance` (see the module
docstring). -/
theorem NestedValidatedRunResult.assemblyNative_of_run
    {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}
    (E : NestedValidatedRunResult result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (wf : ves.WF sourceProdEnv) (Hsources : SourceSyntaxChecks sourceTypes)
    (Hrules : ∀ auxiliaries : List ContainerSpecialization,
      RestorationTableData sourceDecl auxiliaries result E.loweredEnv
        (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 lparams →
      ∃ C : NestedFinalAssemblyShape E.restoration
          (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
          nparams isUnsafe (if isUnsafe then .unsafe else .safe),
        C.production = E.production ∧
        (∀ n ∈ (compilationRestoration sourceDecl auxiliaries).restorableNames,
          C.finalBaseVEnv.constants n = none) ∧
        List.Forall₂
          (E.RestoredRuleRealization (compilationRestoration sourceDecl auxiliaries)
            C.finalBaseVEnv)
          (List.finRange E.production.compilationSignature.constructors.size)
          (C.primaryRules ++ C.auxiliaryRules))
    (Hprovenance : ∀ auxiliaries : List ContainerSpecialization,
      RestorationTableData sourceDecl auxiliaries result E.loweredEnv
        (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 lparams →
      ∀ C : NestedFinalAssemblyShape E.restoration
          (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
          nparams isUnsafe (if isUnsafe then .unsafe else .safe),
        C.production = E.production →
        (∀ n ∈ (compilationRestoration sourceDecl auxiliaries).restorableNames,
          C.finalBaseVEnv.constants n = none) →
        List.Forall₂
          (E.RestoredRuleRealization (compilationRestoration sourceDecl auxiliaries)
            C.finalBaseVEnv)
          (List.finRange E.production.compilationSignature.constructors.size)
          (C.primaryRules ++ C.auxiliaryRules) →
        InductiveRecursorProvenance .unsafe sourceProdEnv.constants
          (ves.venv (if isUnsafe then .unsafe else .safe)) outEnv.constants
          (C.finalBaseVEnv.addDefEqRules (C.primaryRules ++ C.auxiliaryRules))) :
    Nonempty { C : NestedFinalAssemblyCertificate E.restoration
        (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
        nparams isUnsafe (if isUnsafe then .unsafe else .safe) //
      C.production = E.production } := by
  rcases E.restorationTablesRestoringAll wf Hsources with
    ⟨envTypes, generated, auxiliaries, hadded, henvTypes, Haux, Hexpansion,
      hparamsSize, D, Hrestoring, HauxRestoring⟩
  obtain ⟨C, hC, hfreshFinal, HCrules⟩ := Hrules auxiliaries D
  have Hprov := Hprovenance auxiliaries D C hC hfreshFinal HCrules
  have hrealization : E.RestoredRulesRealization (compilationRestoration sourceDecl auxiliaries)
      (C.primaryRules ++ C.auxiliaryRules) := ⟨C.finalBaseVEnv, hfreshFinal, HCrules⟩
  obtain ⟨Hcertified, ⟨Hdata⟩⟩ := E.compilationData_of_tables wf Hsources C hC hadded
    henvTypes Haux Hexpansion hparamsSize D Hrestoring HauxRestoring hrealization
  have hnodup :
      (familyNames E.production.loweredDecl.types ++
        E.production.loweredDecl.types.map (fun t => t.name.str "rec")).Nodup := by
    rcases E.containerSpecializations wf Hsources with
      ⟨_, _, _, _, _, _, _, h, _⟩
    exact h
  obtain ⟨-, -, -, -, -, -, -, hscoped, -, hctorNames, -, -⟩ :=
    E.restorationPrefix_of wf hadded henvTypes Haux Hexpansion hnodup D True.intro
  have hwf : sourceProdEnv.constants.WF := (wf.tr (safety := .safe)).map_wf
  -- the constructor environment of the shape
  have htypesEq : C.canonical.venvTypes = envTypes := by
    have h := C.canonical.typesAdded.abstract
    rw [C.typeValues, hadded] at h
    exact (Option.some.inj h).symm
  have hctorsAdded : envTypes.addConstVals sourceDecl.constructorConstants =
      some C.canonical.venvCtors := by
    have h := C.canonical.ctorsAdded.abstract
    rwa [C.constructorValues, htypesEq] at h
  have hsourceCtorNames := C.sourceConstructorNames
  rw [hC] at hsourceCtorNames
  have hfresh := E.restorableNames_fresh hadded Haux Hexpansion hnodup
  have hfreshCtors := E.restorableNames_fresh_ctors hadded Haux Hexpansion hnodup
    hsourceCtorNames hctorsAdded
  have hrecAdded := C.canonical.recursorsAdded.abstract
  have hle : C.canonical.venvCtors.addProjections sourceDecl.projectionEntries ≤
      C.finalBaseVEnv := VEnv.addConstVals_le hrecAdded
  have hnames : sourceTypes.map (·.name) = sourceDecl.types.map (·.name) := by
    have Hcore := E.nativeSource.core
    rw [E.nativeSourceDecl_eq] at Hcore
    exact names_of_trTypes Hcore.types
  have hinfos := E.restoredRecursorEntryInfos C hC wf Hsources hadded Haux Hexpansion hnodup
    hparamsSize D hscoped hwf
  have Hentries : List.Forall₂
      (RestoredRecursorEntryRealization E.production.compilationInstance
        (compilationRestoration sourceDecl auxiliaries)
        (sourceDecl.types.map (·.name)) C.finalBaseVEnv)
      (List.finRange E.production.compilationSignature.families.size)
      C.recursorEntries := by
    refine forall₂_imp_mem_right hinfos ?_
    rintro owner entry hentry ⟨s, t, Hstep, hentry1, hrec, Hw⟩
    refine ⟨Hstep.restored.newInfo, hentry1, hrec, ?_⟩
    obtain ⟨head, hhead, hheadName, hlevels, hargs, happ, Hctor⟩ :=
      Hdata.restoredFamilyHead_spec hadded hctorsAdded hfresh hfreshCtors owner
    have hinstalled : C.finalBaseVEnv.constants Hstep.restored.newInfo.name ≠ none := by
      have hget := VEnv.addConstVals_get hrecAdded (List.mem_map_of_mem hentry)
      have hname : entry.2.name = Hstep.restored.newInfo.name :=
        Hw.1.trans Hstep.restored.restoration.name.symm
      rw [← hname, hget]
      simp
    have Hrules' := E.restoredRuleRealizations D hctorNames Hdata.recursorNames
      Hdata.heads_not_recursors hfreshFinal Hdata.equations HCrules owner Hstep hinstalled
      head Hctor
    refine E.restoredRecursorRealization_of_step D hnames owner Hstep hle hrec Hw
      ⟨head, hhead, ?_, hlevels, hargs, happ, Hrules'⟩
    rw [E.restoredMajorInduct wf Hsources Haux Hexpansion hnodup hparamsSize D hscoped
      owner Hstep, hheadName]
  exact ⟨⟨{ toNestedFinalAssemblyShape := C
            realization := ⟨⟨_, _, _, _, Hdata, Hcertified, Hentries⟩⟩
            provenance := Hprov }, hC⟩⟩

end VerifyInductive
end Lean4Lean
