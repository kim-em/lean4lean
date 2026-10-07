import Lean4Lean.Theory.Typing.ShapeModel.RuleValidMajorFacts

/-!
# Semantic facts about the family slot of a native recursor

* `container_famSem`: the family of a certified container has a semantic header at its declared
  sort.
* `famProp_false_of_neverZero`: a family whose sort is related to a never-zero level is not a
  proposition at any instance.
* `native_slot_sem`: the constructor of the major of a native equation is recorded in the tables of
  the installation, the family of the major domain is recorded in the final tables, and the sort of
  the owner (at the instance levels) is the sort of the constructor's family at the major's levels.
-/

namespace Lean4Lean.ShapeModel
open Lean4Lean InductiveSignature

set_option linter.unusedSectionVars false

noncomputable section

variable {env : VEnv}

theorem container_famSem (H : env.WF) {E cbase : VEnv} (hgood : Good env E) (hE : E.Ordered)
    (hle : E ≤ env) (hcle : cbase ≤ E) {aux : List ContainerSpecialization}
    (hprior : CertifiedSpecializations cbase aux) {a : ContainerSpecialization} (ha : a ∈ aux) :
    letI := envSig env; ∃ n, FamSem env a.source.name a.source.resultLevel n := by
  obtain ⟨base', block', inst', hcomp', hinst', hle'⟩ := CertifiedSpecializations.member hprior ha
  obtain ⟨b'', exp', s', g', aux', hb'', hdata', -⟩ := hcomp'.compilationOrigin
  obtain ⟨params, _, _, hshape, _, _⟩ := hdata'.sourceParameters
  have hsrc : a.source ∈ a.container.types := List.getElem_mem _
  have hbE : b'' ≤ E := hb''.trans ((install_le hinst').trans (hle'.trans hcle))
  have hc : env.constants a.source.name = some a.source.toVConstant := by
    refine (hle'.trans (hcle.trans hle)).constants (install_type_lookup hinst' (v :=
      a.source.toVConstVal) ?_)
    rw [hcomp'.types_eq]; exact List.mem_map.mpr ⟨_, hsrc, rfl⟩
  exact ⟨_, famSem_of_typeShape H hgood hle hE ((hshape _ hsrc).mono hbE)
    (hdata'.sourceWF.2.2.1 _ hsrc) hc⟩

/-- A family whose sort at the instance levels `lv` is equivalent to a never-zero level is not a
proposition at any further instance. -/
theorem famProp_false_of_neverZero (H : env.WF) {I : Name} {d : FamData}
    (hfamd : famOf env I = some d)
    (hsem : letI := envSig env; FamSem env I d.resultLevel n)
    {L : VLevel} (hL : letI := envSig env; FamSem env I L n')
    {lv ls : List VLevel} (hlen : ∃ ci, env.constants I = some ci ∧ lv.length = ci.uvars)
    {X : VLevel} (hnz : X.IsNeverZero) (hX : X ≈ L.inst lv) (c : Name) (fs : List Nat) :
    letI := envSig env; SemSig.famProp I (RuleMajor.lvls ⟨c, lv, fs⟩ ls) = false := by
  letI := envSig env
  haveI := envSig_coherent_of_wf H
  obtain ⟨ci, hci, hcl⟩ := hlen
  have heval := FamSem.eval_eq hsem hL (lv.map (·.inst ls)) ⟨ci, hci, by simpa using hcl⟩
  have hlev : SemSig.famLevel I = some d.resultLevel := by
    show sigFamLevel env I = _; simp [sigFamLevel, hfamd]
  simp only [SemSig.famProp, hlev, decide_eq_false_iff_not]
  intro hz
  have h0 : d.resultLevel.eval ((RuleMajor.lvls ⟨c, lv, fs⟩ ls).map (· [])) = 0 := hz []
  have e1 : d.resultLevel.eval ((RuleMajor.lvls ⟨c, lv, fs⟩ ls).map (· [])) =
      ((d.resultLevel.inst (lv.map (·.inst ls))).eval []) := by
    rw [VLevel.eval_inst]; simp [RuleMajor.lvls, List.map_map, Function.comp_def]
  rw [e1, congrFun heval [], ← VLevel.inst_inst] at h0
  have e2 := VLevel.equiv_def.1 (VLevel.inst_congr_l (ls := ls) hX) []
  rw [← e2, VLevel.eval_inst] at h0
  exact hnz _ h0

theorem directFamily_resultLevel' {a : ContainerSpecialization} {U : Nat} {params : List VExpr}
    {direct : VInductiveType} (H : a.directFamily U params = some direct) :
    direct.resultLevel = a.source.resultLevel.inst a.levels := by
  unfold ContainerSpecialization.directFamily at H
  simp only [bind, Option.bind_eq_some_iff] at H
  obtain ⟨type, _, ctors, _, he⟩ := H
  cases Option.some.inj he
  rfl

/-- The family table of a native installation records every source family with constructors. -/
theorem addNative_fam {E E' : VEnv} {T : Tables} {decl : VInductDecl} {block : VInductBlock}
    (hT : T.Inv E) (hinstall : block.install E = some E') (htypes : block.types = decl.typeConstants)
    (hnd : decl.sourceNames.Nodup) (entries : List NativeRecursorData) {F : VInductiveType}
    (hF : F ∈ decl.types) (hne : F.ctors ≠ []) :
    (T.addNative decl entries).fam F.name = some (famView decl F) := by
  obtain ⟨envTypes, _, _, ht, -, -, -⟩ := install_parts hinstall
  have hfresh : E.constants F.name = none :=
    VEnv.addConstVals_names_fresh ht F.toVConstVal (by
      rw [htypes]; exact List.mem_map.mpr ⟨F, hF, rfl⟩)
  show addView T.fam (viewFams decl selCtors) F.name = _
  rw [addView_some]
  exact .inr ⟨(hT.freshT hfresh).1, viewFams_mem hnd hF (selCtors_iff.mpr hne)⟩

/-- The semantic facts of the family slot of a native equation. -/
theorem native_slot_sem (H : env.WF) {E E' cbase : VEnv} {T : Tables}
    {decl expanded : VInductDecl} {block : VInductBlock} {s : InductiveSignature} {g : Instance s}
    {aux : List ContainerSpecialization} (hgood : Good env E) (hEW : E.WF) (hle : E' ≤ env)
    (hcomp : decl.CompilesTo E block) (hblock : VInductBlock.WF E block)
    (hinstall : block.install E = some E') (hcle : cbase ≤ E)
    (hdata : CompilationData cbase decl expanded s g aux block)
    (hprior : CertifiedSpecializations cbase aux) (hT : T.Inv E)
    (hext : (T.addNative decl (NativeRecursorData.compilationEntries default decl s aux g)).Extends
      (envTables env))
    (hfam : ∀ I d, (T.addNative decl
      (NativeRecursorData.compilationEntries default decl s aux g)).fam I = some d →
      letI := envSig env; FamSem env I d.resultLevel (d.nparams + d.nindices))
    (own : Fin s.families.size) {c Fn : Name} {lv lvF : List VLevel}
    (hslot : (∃ F ∈ decl.types, decl.types[own.val]? = some F ∧ Fn = F.name ∧
          lvF = g.levels ∧ lv = g.levels ∧ ∃ cv ∈ F.ctors, cv.name = c) ∨
        (∃ a ∈ aux, decl.types.length ≤ own.val ∧
          aux[own.val - decl.types.length]? = some a ∧ Fn = a.source.name ∧
          lvF = a.levels.map (·.inst g.levels) ∧ lv = a.levels.map (·.inst g.levels) ∧
          ∃ cv ∈ a.source.ctors, cv.name = c)) :
    letI := envSig env
    ∃ k, (T.addNative decl (NativeRecursorData.compilationEntries default decl s aux g)).ctor c =
        some k ∧ (∃ ci, env.constants k.family = some ci ∧ lv.length = ci.uvars) ∧
      (∃ dF, famOf env Fn = some dF) ∧
      ∃ L n, FamSem env k.family L n ∧ s.families[own].resultLevel.inst g.levels ≈ L.inst lv := by
  letI := envSig env
  have hinst := hT.install' hEW hcomp hblock hinstall hcle hdata hprior
  have hle₁ := install_le hinstall
  obtain ⟨_, -, hadm⟩ := hdata.admissible
  have hguv : g.levels.length = decl.uvars := by
    rw [hadm.levels_length, hdata.model.uvars, hdata.uvars]
  -- the uvars of the family constant of a recorded constructor
  have hcuv : ∀ {k : CtorData}, (T.addNative decl
      (NativeRecursorData.compilationEntries default decl s aux g)).ctor c = some k →
      ∃ ci, env.constants k.family = some ci ∧ k.uvars = ci.uvars := by
    intro k hk
    obtain ⟨d, hd, hdu, -⟩ := ctorOf_famOf H (hext.ctor hk)
    obtain ⟨ci, hci, hciu, -⟩ := famOf_shape H hd
    exact ⟨ci, hci, by rw [hciu, hdu]⟩
  obtain ⟨envTypes, direct, -, hdirect, hwf, hrel⟩ := hdata.correspondence
  rcases hslot with ⟨F, hF, hFo, rfl, rfl, rfl, cv, hcv, rfl⟩ |
    ⟨a, ha, hlo, hao, rfl, rfl, rfl, cv, hcv, rfl⟩
  · have hne : F.ctors ≠ [] := List.ne_nil_of_mem hcv
    have hTF := addNative_fam hT hinstall hdata.types hdata.sourceWF.2.1
      (NativeRecursorData.compilationEntries default decl s aux g) hF hne
    have hconst : E'.constants cv.name = some cv.toVConstant :=
      VInductBlock.install_ctor_lookup hinstall (by
        rw [hdata.ctors]; exact List.mem_flatMap.mpr ⟨F, hF, hcv⟩)
    obtain ⟨k, hk, hkf, hku, -⟩ := ctor_entry_of_fam hinst.2 hTF hcv hconst
    obtain ⟨ci, hci, hciu⟩ := hcuv hk
    refine ⟨k, hk, ⟨ci, hci, by rw [hguv, ← hku, hciu]⟩, ⟨_, hext.fam hTF⟩, F.resultLevel, _,
      by rw [hkf]; exact hfam _ _ hTF, ?_⟩
    obtain ⟨hlt, hFeq⟩ := List.getElem?_eq_some_iff.mp hFo
    obtain ⟨_, direct', _, hdirect', hlt', hres⟩ := CompilationData.family_slot hdata own
    rw [List.getElem_append_left hlt, hFeq] at hres
    exact VLevel.inst_congr_l hres.resultLevel
  · have hTc := container_ctor hT hprior hcle ha hcv
    have hTc' := hinst.1.ctor hTc
    obtain ⟨d, hd, -⟩ := (hT.views.ctor hTc).2
    obtain ⟨ci, hci, hciu⟩ := hcuv hTc'
    obtain ⟨n, hsemL⟩ := container_famSem H hgood hEW.ordered (hle₁.trans hle) hcle hprior ha
    have hawf := hwf a ha
    refine ⟨_, hTc', ⟨ci, hci, ?_⟩, ⟨_, hext.fam (hinst.1.fam hd)⟩, a.source.resultLevel, n,
      hsemL, ?_⟩
    · rw [← hciu]; simp [ctorView, hawf.2.2.1]
    · obtain ⟨_, direct', _, hdirect', hlt', hres⟩ := CompilationData.family_slot hdata own
      rw [List.getElem_append_right hlo] at hres
      have hrel' := List.mapM_eq_some.mp hdirect'
      have hjb : own.val - decl.types.length < aux.length :=
        (List.getElem?_eq_some_iff.mp hao).1
      obtain ⟨hjb', hdf⟩ := forall₂_getElem_exists hrel' _ hjb
      have haeq : aux[own.val - decl.types.length] = a := (List.getElem?_eq_some_iff.mp hao).2
      rw [haeq] at hdf
      have h1 := hres.resultLevel
      rw [directFamily_resultLevel' hdf] at h1
      refine (VLevel.inst_congr_l h1).trans ?_
      rw [VLevel.inst_inst]

end

end Lean4Lean.ShapeModel
