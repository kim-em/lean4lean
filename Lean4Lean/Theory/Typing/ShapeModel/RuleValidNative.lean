import Lean4Lean.Theory.Typing.ShapeModel.RuleValidNativeSingleton

/-!
# Validity of native iota rules
-/

namespace Lean4Lean.ShapeModel
open Lean4Lean InductiveSignature

set_option linter.unusedSectionVars false

noncomputable section

variable {env : VEnv}

theorem wrapLams_instL' (Ds : List VExpr) (b : VExpr) (ls : List VLevel) :
    (VExpr.wrapLams Ds b).instL ls = VExpr.wrapLams (Ds.map (·.instL ls)) (b.instL ls) := by
  induction Ds with
  | nil => rfl
  | cons D Ds ih => simp [VExpr.wrapLams, VExpr.instL] at ih ⊢; exact ih

theorem wrapForalls_instL' (Ds : List VExpr) (b : VExpr) (ls : List VLevel) :
    (VExpr.wrapForalls Ds b).instL ls = VExpr.wrapForalls (Ds.map (·.instL ls)) (b.instL ls) := by
  induction Ds with
  | nil => rfl
  | cons D Ds ih => simp [VExpr.wrapForalls, VExpr.instL] at ih ⊢; exact ih

theorem vars_instL (n k : Nat) (ls : List VLevel) : (vars n k).map (·.instL ls) = vars n k := by
  simp [vars, VExpr.instL]

theorem closedN_of_wrapLams : ∀ {Ds : List VExpr} {R : VExpr} {k : Nat},
    (VExpr.wrapLams Ds R).ClosedN k → R.ClosedN (k + Ds.length)
  | [], _, _, h => h
  | _ :: Ds, _, k, h => by
    have := closedN_of_wrapLams (Ds := Ds) (k := k + 1) h.2
    simpa [Nat.add_assoc, Nat.add_comm 1] using this

theorem isZero_inst_of_equiv_zero {l : VLevel} (h : l ≈ .zero) (ls : List VLevel) :
    SLvl.IsZero (l.inst ls).eval := fun v => by
  show (l.inst ls).eval v = 0
  rw [VLevel.eval_inst, VLevel.equiv_def.1 h]; rfl

theorem ruleLhs_instL (Ds idx ps : List VExpr) (hd : VExpr) (c : Name) (lv : List VLevel)
    (npre nf : Nat) (ls : List VLevel) :
    (VExpr.wrapLams Ds (VExpr.mkApps hd (vars npre nf ++ idx ++
      [VExpr.mkApps (.const c lv) (ps ++ vars nf 0)]))).instL ls =
    VExpr.wrapLams (Ds.map (·.instL ls)) (VExpr.mkApps (hd.instL ls) (vars npre nf ++
      idx.map (·.instL ls) ++
      [VExpr.mkApps (.const c (lv.map (·.inst ls))) (ps.map (·.instL ls) ++ vars nf 0)])) := by
  rw [wrapLams_instL']
  simp only [VExpr.instL_mkApps, List.map_append, vars_instL, List.map_cons, List.map_nil]
  rfl

theorem ruleType_instL (Ds idx ps : List VExpr) (k : Nat) (c : Name) (lv : List VLevel)
    (nf : Nat) (ls : List VLevel) :
    (VExpr.wrapForalls Ds (VExpr.mkApps (.bvar k) (idx ++
      [VExpr.mkApps (.const c lv) (ps ++ vars nf 0)]))).instL ls =
    VExpr.wrapForalls (Ds.map (·.instL ls)) (VExpr.mkApps (.bvar k) (idx.map (·.instL ls) ++
      [VExpr.mkApps (.const c (lv.map (·.inst ls))) (ps.map (·.instL ls) ++ vars nf 0)])) := by
  rw [wrapForalls_instL']
  simp only [VExpr.instL_mkApps, List.map_append, vars_instL, List.map_cons, List.map_nil]
  rfl

theorem native_extraValid {E E' cbase : VEnv} {T : Tables} {decl expanded : VInductDecl}
    {block : VInductBlock} {s : InductiveSignature} {g : Instance s}
    {aux : List ContainerSpecialization} (H : env.WF) (hgood : Good env E) (hEW : E.WF)
    (hle : E' ≤ env) (hdecl : decl.WF E) (hcomp : decl.CompilesTo E block)
    (hblock : VInductBlock.WF E block) (hinstall : block.install E = some E')
    (hcle : cbase ≤ E) (hdata : CompilationData cbase decl expanded s g aux block)
    (hprior : CertifiedSpecializations cbase aux) (hT : T.Inv E)
    (hext : (T.addNative decl (NativeRecursorData.compilationEntries default decl s aux g)).Extends
      (envTables env))
    (hfam : ∀ I d, (T.addNative decl
      (NativeRecursorData.compilationEntries default decl s aux g)).fam I = some d →
      letI := envSig env; FamSem env I d.resultLevel (d.nparams + d.nindices))
    (hdf : df ∈ block.rules) : letI := envSig env; ExtraValid env df := by
  letI := envSig env
  haveI := envSig_coherent_of_wf H
  have hcl : ConstClosed env := fun h => H.ordered.closedC h
  obtain ⟨data, hmem, index, howner, hgen⟩ := hdata.nativeEntries_equation hdf default
  have hreg : VEnv.NativeRecursorRegistered env data :=
    .compilationEntries hdata hprior hcle hinstall hle hmem
  have hnat : (envTables env).natives data.name = some data :=
    hext.natives (hdata.nativeEntries_lookup hmem)
  have hdfenv : env.defeqs df := hreg.equation_present hgen
  have huvdf : df.uvars = data.uvars := hreg.equation_uvars hgen
  have hclosed := hreg.equation_closed H hgen
  obtain ⟨Th0, hTh0⟩ := hreg.recursorType_exists
  have hcv := hreg.recursorType hTh0
  have hrule : EnvRule env (majorRule (structNp env) (.const data.name) df.uvars df
      data.schema.signature.constructors[index].fields.length) :=
    .inr (.inr (.inl ⟨df, hdfenv, data, hnat, index, howner, hgen, rfl⟩))
  obtain ⟨o, -, rfl⟩ := List.mem_map.mp hmem
  have hinstEq : (NativeRecursorData.ofInstance default (CaseSchema.ofCompilation decl s aux) g
      o).nativeInstance = g := by
    cases g with
    | mk U levels target names =>
      change Instance.mk U levels target (fun owner => s.families[owner].name.str "rec") =
        Instance.mk U levels target names
      congr 1
      exact funext fun owner => (hdata.recursorNames owner).symm
  have hg : (compilationRestoration decl aux).equation (g.equation index) = some df := by
    change (compilationRestoration decl aux).equation
      ((NativeRecursorData.ofInstance default (CaseSchema.ofCompilation decl s aux) g
        o).nativeInstance.equation index) = _ at hgen
    rwa [hinstEq] at hgen
  obtain ⟨j, rfl⟩ : ∃ j : Fin s.constructors.size, j = index := ⟨index, rfl⟩
  have howner' : s.constructors[j].owner = o := howner
  have hrule' : EnvRule env (majorRule (structNp env)
      (.const (NativeRecursorData.ofInstance default (CaseSchema.ofCompilation decl s aux) g o).name)
      df.uvars df s.constructors[j].fields.length) := hrule
  clear hrule hgen howner
  have hTh0' : (compilationRestoration decl aux).expr (g.recursorType s.constructors[j].owner) =
      some Th0 := by
    change (compilationRestoration decl aux).expr
      ((NativeRecursorData.ofInstance default (CaseSchema.ofCompilation decl s aux) g
        _).nativeInstance.recursorType _) = _ at hTh0
    rw [hinstEq] at hTh0
    rw [howner']; exact hTh0
  have hname : (NativeRecursorData.ofInstance default (CaseSchema.ofCompilation decl s aux) g o).name =
      (compilationRestoration decl aux).recursorName (g.recursorName s.constructors[j].owner) := by
    rw [howner']; exact congrArg _ (hdata.recursorNames o).symm
  rw [hname] at hrule' hcv
  change df.uvars = g.uvars at huvdf
  change env.constants _ = some { uvars := g.uvars, type := Th0 } at hcv
  obtain ⟨Ds, idx, R, Es, doms₀, TbH, c, lv, ps, Fn, lvF, pargs, hl, hr, ht, hDs, hidx, hmot, hEs,
    hThs, hdoms, hpl, hslot, hDsR, hidxR⟩ := CompilationData.native_syntax hdata j hg hTh0'
  obtain ⟨k, hk, hkuv, ⟨dF, hdF⟩, L, nL, hsemL, hlevel⟩ :=
    native_slot_sem H hgood hEW hle hcomp hblock hinstall hcle hdata hprior hT hext hfam _ hslot
  have hinst := hT.install' hEW hcomp hblock hinstall hcle hdata hprior
  obtain ⟨ci, d, hci, hcif, hfamd, hsem, hstr⟩ := major_facts H hinst.2 hext hfam hk
  obtain ⟨hncF, hnrF⟩ := fam_facts H hdF
  have heq := majorRule_eq (np := structNp env)
    (h := .const ((compilationRestoration decl aux).recursorName
      (g.recursorName s.constructors[j].owner))) (u := df.uvars) rfl (by intros; simp) hl hr
  have hRcl0 : R.ClosedN Ds.length := by
    have := closedN_of_wrapLams (k := 0) (hr ▸ hclosed.2.1)
    simpa using this
  intro ls u hls hTy hL hR
  rw [hl, ruleLhs_instL, ht, ruleType_instL] at hL
  rw [hr, wrapLams_instL', ht, ruleType_instL] at hR
  rw [hl, ruleLhs_instL, hr, wrapLams_instL']
  have hhd : (VExpr.const ((compilationRestoration decl aux).recursorName
      (g.recursorName s.constructors[j].owner)) (VLevel.params g.uvars)).instL ls =
      Head.toExpr (.const ((compilationRestoration decl aux).recursorName
        (g.recursorName s.constructors[j].owner))) ls := by
    simp only [VExpr.instL, Head.toExpr, VLevel.inst_map_id (hls.trans huvdf)]
  rw [hhd] at hL ⊢
  obtain ⟨hm, hmot'⟩ := hmot
  refine rule_instance_valid H hrule' (by rw [heq]) (by rw [heq]; exact hls)
    (npre := s.params.length + (s.families.size + s.constructors.size))
    (by rw [heq]; exact hDs) (by rw [heq]) (by rw [heq]) (by rw [heq])
    (by rw [heq, hDs, Nat.add_sub_cancel]) (by simp [hDs])
    (by rw [← hDs]; exact hRcl0.instL) hL hR (Th := Th0.instL ls) ⟨_, hcv, rfl⟩
    (TbH := TbH.instL ls) (doms₀ := doms₀.map (·.instL ls)) (F := Fn) (lvF := lvF.map (·.inst ls))
    (pargs := pargs.map (·.instL ls)) ?_ (by simp [hdoms, hidx]) (by simp [hpl]) hncF hnrF
    hci hfamd hsem hstr (fun _ => .rfl) ?_ (iM := s.params.length + s.constructors[j].owner.val)
    (by simp; omega) ?_ (Es := Es.map (·.instL ls)) (tgt := g.targetLevel.inst ls)
    (by simp [hEs, hidx]) ?_
  · rw [hThs, wrapForalls_instL']
    simp only [List.map_append, List.map_cons, List.map_nil, VExpr.instL_mkApps, vars_instL, hidx]
    rfl
  · have := s.constructors[j].owner.isLt
    simp only [List.length_map, hDs]
    congr 2
    omega
  · simp only [List.getElem_map, hmot', wrapForalls_instL']
    rfl
  · intro hfp
    obtain ⟨envX, hX, hadm⟩ := hdata.admissible
    rcases hadm.elimination with hnz | htz | hsing
    · exfalso
      have hown : s.families[s.constructors[j].owner] ∈ s.families.toList :=
        Array.getElem_mem_toList ..
      rw [hcif] at hfamd hsem
      have := famProp_false_of_neverZero H hfamd hsem hsemL hkuv (VLevel.IsNeverZero.inst' (hnz _ hown) ls) hlevel c
        (List.range s.constructors[j].fields.length).reverse (ls := ls)
      rw [hcif] at hfp
      rw [this] at hfp; cases hfp
    · exact .inl (isZero_inst_of_equiv_zero htz ls)
    · by_cases htz : g.targetLevel ≈ .zero
      · exact .inl (isZero_inst_of_equiv_zero htz ls)
      right
      refine ⟨fun r' hr' hh' => ?_, fun σ _ W i hi hn => ?_⟩
      · rcases hr' with ⟨v, -, hv, rfl⟩ | ⟨-, hq, rfl⟩ | ⟨df', -, data', hd', index', -, hg', rfl⟩ |
          ⟨key, schema, -, owner, rules, df', -, -, rfl⟩
        · exfalso
          simp only [defRule, Head.const.injEq] at hh'
          have := (envTables_inv H).defs_natives (n := v.name) (by rw [hv]; simp)
          rw [hh', ← hname, hnat] at this; cases this
        · exfalso
          simp only [majorRule, Head.const.injEq] at hh'
          have := ((envTables_inv H).quot hq).2.2.2.2.1
          rw [hh', ← hname, hnat] at this; cases this
        · simp only [majorRule, Head.const.injEq] at hh'
          rw [hh', ← hname, hnat] at hd'
          cases Option.some.inj hd'
          have hjv : index'.val = j.val := by
            have h1 : index'.val < s.constructors.size := index'.isLt
            have h2 := hsing.2.1
            have h3 := j.isLt
            omega
          have hj' : (⟨index'.val, index'.isLt⟩ : Fin s.constructors.size) = j := Fin.ext hjv
          have hg'' : (compilationRestoration decl aux).equation (g.equation j) = some df' := by
            change (compilationRestoration decl aux).equation
              ((NativeRecursorData.ofInstance default (CaseSchema.ofCompilation decl s aux) g
                o).nativeInstance.equation index') = _ at hg'
            rw [hinstEq] at hg'
            rw [← hj']; exact hg'
          rw [hg] at hg''
          cases Option.some.inj hg''
          have hnf : (NativeRecursorData.ofInstance default (CaseSchema.ofCompilation decl s aux) g
              o).schema.signature.constructors[index'].fields.length =
              s.constructors[j].fields.length :=
            congrArg (fun k : Fin s.constructors.size => s.constructors[k].fields.length) hj'
          rw [hnf, majorRule_eq (np := structNp env) rfl (by intros; simp) hl hr]
          rfl
        · simp [majorRule] at hh'
      · rw [heq, hDs, Nat.add_sub_cancel] at hn
        exact native_singleton_unread H hgood hEW hle hblock hinstall hcle hdata hX hsing
          hadm.levels_wf j hDsR hidxR ls _ _ σ W i hi hn

end

end Lean4Lean.ShapeModel
