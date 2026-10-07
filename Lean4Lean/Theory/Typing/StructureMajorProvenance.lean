import Lean4Lean.Theory.Typing.NativeStructureParams
import Lean4Lean.Theory.Typing.ConcretePatterns
import Lean4Lean.Theory.Typing.Injectivity

/-! The structure-major facts of the concrete pattern table.

A native or quotient iota major of structure type is a saturated application
of the structure's constructor, and native computation at a structure
constructor reads only its fields. Both are consequences of declaration
provenance: the major constructor of every installed equation is the
projection constructor of its registered result family
(`WF.structureCtorCoherent`), a registered structure is never the primitive
quotient type, and a native rule's constructor parameter prefix is the
parameter telescope recorded by that family's projection metadata. -/

namespace Lean4Lean.VEnv
open InductiveSignature VExpr CanonicalDataHead
open private declaration_le from Lean4Lean.Theory.Typing.DefinitionHistory
open private addDefEqs_as_rules addConsts_as_values from Lean4Lean.Theory.Typing.NativeConstructorRigidity
set_option linter.unusedSectionVars false

variable {env : VEnv}

theorem _root_.Lean4Lean.VExpr.forallResult_telescope (e : VExpr) :
    ∃ doms, e = VExpr.wrapForalls doms e.forallResult ∧ doms.length = e.forallArity := by
  induction e with
  | forallE d b _ ih =>
    obtain ⟨doms, he, hl⟩ := ih
    exact ⟨d :: doms, by
      change VExpr.forallE d b = VExpr.forallE d (VExpr.wrapForalls doms b.forallResult)
      rw [← he], by simp [VExpr.forallArity, hl]⟩
  | _ => exact ⟨[], rfl, rfl⟩

private theorem instL_wrapForalls' (ds : List VExpr) (body : VExpr) (packed : List VLevel) :
    (VExpr.wrapForalls ds body).instL packed =
      VExpr.wrapForalls (ds.map (·.instL packed)) (body.instL packed) := by
  induction ds with
  | nil => rfl
  | cons d ds ih => simp only [VExpr.wrapForalls, List.foldr_cons, List.map_cons, VExpr.instL] at ih ⊢; rw [ih]

/-- A saturated application whose head returns a rigid family and whose own
type is an application of a rigid family supplies the whole telescope, and the
two families agree. -/
theorem HasType.mkApps_rigid_family (henv : VEnv.WF env)
    {Γ : List VExpr} (hΓ : OnCtx Γ (env.IsType U)) (hF : env.Rigid F) (hG : env.Rigid G)
    {f : VExpr} {domains args xs ys : List VExpr} {ls levels : List VLevel}
    (hf : env.HasType U Γ f (VExpr.wrapForalls domains (VExpr.mkApps (.const F ls) xs)))
    (ht : env.HasType U Γ (VExpr.mkApps f args) (VExpr.mkApps (.const G levels) ys)) :
    args.length = domains.length ∧ F = G := by
  induction args generalizing f domains xs with
  | nil =>
    cases domains with
    | nil =>
      have ⟨_, hT⟩ := hf.isType henv.ordered hΓ
      exact ⟨rfl, Classical.byContradiction fun hne =>
        IsDefEqU.rigidApp_ne henv hΓ hF hG hne hT (hf.uniqU henv hΓ ht)⟩
    | cons domain domains =>
      have ⟨_, hT⟩ := ht.isType henv.ordered hΓ
      exact (VEnv.IsDefEqU.rigidApp_forallE_inv henv hΓ hG hT
        (hf.uniqU henv hΓ ht).symm).elim
  | cons arg args ih =>
    have hfa : VExpr.WF env U Γ (.app f arg) :=
      VExpr.WF.of_mkApps henv.ordered hΓ (f := .app f arg) ⟨_, ht⟩
    rcases hfa.app_inv henv.ordered hΓ with ⟨A, B, hfun, harg⟩
    cases domains with
    | nil =>
      have ⟨_, hT⟩ := hf.isType henv.ordered hΓ
      exact (VEnv.IsDefEqU.rigidApp_forallE_inv henv hΓ hF hT
        (hf.uniqU henv hΓ hfun)).elim
    | cons domain domains =>
      rcases (hf.uniqU henv hΓ hfun).forallE_inv henv hΓ with ⟨⟨_, hd⟩, _⟩
      have ha := harg.defeqU_r henv hΓ ⟨_, hd.symm⟩
      have hfa' := hf.app ha
      change env.HasType U Γ (.app f arg)
        ((VExpr.wrapForalls domains (VExpr.mkApps (.const F ls) xs)).inst arg) at hfa'
      rw [VExpr.wrapForalls_inst, VExpr.inst_mkApps] at hfa'
      obtain ⟨hlen, heq⟩ := ih hfa' ht
      exact ⟨by simpa [VExpr.instDomains] using hlen, heq⟩

/-- The major constructor of an installed equation, applied at a registered
structure type, is that structure's constructor applied to all its parameters
and fields. -/
theorem WF.installed_major_struct (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U))
    (hdf : env.defeqs equation) (hm : equation.HasConstructorMajor cc)
    (hl : env.projections family info)
    (hs : env.HasType U Γ (VExpr.mkApps (.const cc lsc) fs) (VExpr.mkApps (.const family ls) ps)) :
    cc = info.ctorName ∧ fs.length = info.nparams + info.numFields := by
  obtain ⟨ci, hci, F, lsF, hres, _, hrigidF⟩ := henv.native_constructor_result_rigid hdf hm
  have hhead : VExpr.WF env U Γ (.const cc lsc) := VExpr.WF.of_mkApps henv.ordered hΓ ⟨_, hs⟩
  obtain ⟨ci', hci', hlw, hlen⟩ := hhead.const_inv henv.ordered hΓ
  rw [hci] at hci'
  cases hci'
  have hc := HasType.const (Γ := Γ) hci hlw hlen
  obtain ⟨doms, hdoms, hdomsLen⟩ := VExpr.forallResult_telescope ci.type
  have hresEq : ci.type.forallResult =
      VExpr.mkApps (.const F lsF) ci.type.forallResult.getAppFnArgs.2 := by
    have h := VExpr.mkApps_getAppFnArgs_eq ci.type.forallResult
    change VExpr.mkApps ci.type.forallResult.getAppFnArgs.1 ci.type.forallResult.getAppFnArgs.2 = _ at h
    rw [hres] at h
    exact h.symm
  rw [hdoms, hresEq, instL_wrapForalls', VExpr.instL_mkApps] at hc
  obtain ⟨hfs, hFfam⟩ := HasType.mkApps_rigid_family henv hΓ hrigidF (henv.projectionRigid hl) hc hs
  subst hFfam
  have hcc := henv.structureCtorCoherent F info hl equation cc hdf hm ⟨ci, lsF, hci, hres⟩
  subst hcc
  refine ⟨rfl, ?_⟩
  have hctor := henv.ordered.projectionConstructor hl
  rw [hci] at hctor
  cases hctor
  obtain ⟨decl, type, ctor, _, _, _, _, _, hnparams, _, _, _, hctorType, _, _, _, hraw, _⟩ :=
    henv.ordered.projectionShape hl
  obtain ⟨doms', result, _, hle, _, _, harity⟩ := hraw.forallArity
  rw [hctorType] at harity
  simp only [List.length_map] at hfs
  change fs.length = info.nparams + (info.ctorType.forallArity - info.nparams)
  change doms.length = info.ctorType.forallArity at hdomsLen
  omega

/-- After the primitive quotient declaration, no structure is registered for
`Quot`. -/
theorem WF'.quot_no_projection (H : VEnv.WF' ds env) :
    VDecl.quot ∈ ds → QuotRegistered env ∧ ∀ info, ¬env.projections ``Quot info := by
  induction H with
  | empty => intro h; cases h
  | @decl d env' ds env hdecl hbase ih =>
    have henv := (show env.WF from ⟨ds, hbase⟩).ordered
    intro hmem
    have hle := declaration_le hdecl
    have hproj : ∀ F info, env'.projections F info → env.projections F info ∨
        env.constants F = none := by
      intro F info hp
      cases hdecl with
      | «axiom» _ hadd | «opaque» _ hadd => rw [VEnv.addConst_projections hadd] at hp; exact .inl hp
      | «example» => exact .inl hp
      | «def» _ hadd =>
        have h := VEnv.addConst_projections hadd
        exact .inl (h ▸ hp)
      | mutualDef _ hadd _ =>
        rw [addDefEqs_as_rules, VEnv.addDefEqRules_projections,
          VEnv.addConstVals_projections (addConsts_as_values ▸ hadd)] at hp
        exact .inl hp
      | quot _ hadd =>
        simp only [VEnv.addQuot, Option.bind_eq_bind, Option.bind_eq_some_iff,
          Option.some.injEq] at hadd
        obtain ⟨a, ha, b, hb, c, hc, d, hd, rfl⟩ := hadd
        have h : (d.addDefEq quotDefEq).projections = env.projections :=
          (VEnv.addConst_projections hd).trans <| (VEnv.addConst_projections hc).trans <|
            (VEnv.addConst_projections hb).trans (VEnv.addConst_projections ha)
        exact .inl (h ▸ hp)
      | induct _ hadd =>
        cases hadd with
        | intro _ hcompile _ _ hinstall =>
          simp only [VInductBlock.install, Option.bind_eq_bind, Option.bind_eq_some_iff,
            Option.pure_def, Option.some.injEq] at hinstall
          obtain ⟨envTypes, htypes, envCtors, hctors, envRecs, hrecs, rfl⟩ := hinstall
          rw [VEnv.addDefEqRules_projections, VEnv.addConstVals_projections hrecs,
            VEnv.addProjections_iff, VEnv.addEliminators_projections,
            VEnv.addConstVals_projections hctors,
            VEnv.addConstVals_projections htypes] at hp
          rcases hp with ⟨entry, hentry, rfl, rfl⟩ | hp
          · rw [hcompile.projections] at hentry
            obtain ⟨type, htype, ctor, _, rfl⟩ := VInductDecl.projectionEntries_origin hentry
            exact .inr (VEnv.addConstVals_names_fresh htypes type.toVConstVal (by
              rw [hcompile.types]; exact List.mem_map.mpr ⟨type, htype, rfl⟩))
          · exact .inl hp
    rcases List.mem_cons.mp hmem with rfl | hold
    · cases hdecl with
      | quot _ hadd =>
        refine ⟨.of_addQuot hadd, fun info hp => ?_⟩
        simp only [VEnv.addQuot, Option.bind_eq_bind, Option.bind_eq_some_iff,
          Option.some.injEq] at hadd
        obtain ⟨a, ha, b, hb, c, hc, d, hd, rfl⟩ := hadd
        have h : (d.addDefEq quotDefEq).projections = env.projections :=
          (VEnv.addConst_projections hd).trans <| (VEnv.addConst_projections hc).trans <|
            (VEnv.addConst_projections hb).trans (VEnv.addConst_projections ha)
        obtain ⟨_, hq⟩ := henv.projectionConstant (h ▸ hp)
        unfold VEnv.addConst at ha
        split at ha
        · cases ha
        · rename_i hnone; rw [hnone] at hq; cases hq
    · obtain ⟨hq, hno⟩ := ih hold
      refine ⟨hq.mono hle, fun info hp => ?_⟩
      rcases hproj _ info hp with hp | hfresh
      · exact hno info hp
      · rw [hq.quotient] at hfresh; cases hfresh
  | inductEliminators _ _ _ _ _ _ _ _ ih =>
    intro hmem
    obtain ⟨hq, hno⟩ := ih hmem
    exact ⟨hq.mono VEnv.addEliminator_le, fun info hp => hno info hp⟩
  | @inductProjections baseDecls ds base envTypes envCtors decl block
      hbase _ _ _ _ _ _ _ _ htypesSource _ hprojections htypes hctors _ ihCtors =>
    intro hmem
    obtain ⟨hq, hno⟩ := ihCtors hmem
    have hbaseOrdered := (show base.WF from ⟨baseDecls, hbase⟩).ordered
    have hleCtors : base ≤ envCtors.addEliminators block.eliminators :=
      (VEnv.addConstVals_le htypes).trans ((VEnv.addConstVals_le hctors).trans
        VEnv.addEliminators_le)
    refine ⟨hq.mono VEnv.addProjections_le, fun info hp => ?_⟩
    rw [VEnv.addProjections_iff] at hp
    rcases hp with ⟨entry, hentry, hname, rfl⟩ | hp
    · have hdf : (envCtors.addEliminators block.eliminators).defeqs = base.defeqs :=
        VEnv.addEliminators_defeqs.trans <|
        (VEnv.addConstVals_defeqs hctors).trans (VEnv.addConstVals_defeqs htypes)
      have hqd : base.defeqs quotDefEq := hdf ▸ hq.equation
      have hmk : quotDefEq.HasConstructorMajor ``Quot.mk :=
        ⟨_, [.param 0], [.bvar 5, .bvar 4, .bvar 0], rfl⟩
      obtain ⟨ci, hci⟩ := hbaseOrdered.constructorMajor_declared hqd hmk
      have hci' := hleCtors.constants hci
      rw [hq.constructor] at hci'
      cases hci'
      have hrf : base.ResultFamily ``Quot.mk ``Quot := ⟨_, [.param 0], hci, by rfl⟩
      obtain ⟨cF, hcF⟩ := hbaseOrdered.resultFamily_declared hrf
      rw [hprojections] at hentry
      obtain ⟨type, htype, ctor, _, rfl⟩ := VInductDecl.projectionEntries_origin hentry
      have hfresh := VEnv.addConstVals_names_fresh htypes type.toVConstVal (by
        rw [htypesSource]; exact List.mem_map.mpr ⟨type, htype, rfl⟩)
      change base.constants type.name = none at hfresh
      have hname' : type.name = ``Quot := hname.symm
      rw [hname', hcF] at hfresh
      cases hfresh
    · exact hno info hp

theorem _root_.List.drop_append_ge {l1 l2 : List α} (h : l1.length ≤ n) :
    (l1 ++ l2).drop n = l2.drop (n - l1.length) := by
  rw [List.drop_append, List.drop_eq_nil_of_le h, List.nil_append]

theorem Pattern.argumentRHS_var (p : Pattern) (n : Nat) :
    ∀ x ∈ p.argumentRHS n, ∃ path, x = .var path := by
  induction n with
  | zero => intro x hx; cases hx
  | succ n ih =>
    intro x hx
    simp only [Pattern.argumentRHS, List.mem_append, List.mem_map, List.mem_singleton] at hx
    rcases hx with ⟨y, hy, rfl⟩ | rfl
    · obtain ⟨path, rfl⟩ := ih y hy
      exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩

theorem Pattern.Matches.const_arguments_eq
    (H : ((Pattern.const name).varN n).Matches (VExpr.mkApps (.const name levels) args) levels values)
    (levels' : List VLevel) :
    ((Pattern.const name).argumentRHS n).map (fun rhs => rhs.apply levels' values) = args := by
  have h := congrArg VExpr.getAppFnArgs H.const_arguments
  rw [spine_mkApps_exact _ _ rfl, spine_mkApps_exact _ _ rfl] at h
  have h2 := (Prod.mk.inj h).2
  rw [h2]
  apply List.map_congr_left
  intro x hx
  obtain ⟨path, rfl⟩ := Pattern.argumentRHS_var _ _ x hx
  rfl

section
variable {registry : Registry} {declarations : List VDecl}

/-- A native or quotient iota major of structure type is a saturated
application of the structure's constructor. -/
theorem ConcretePattern.struct_major (henv : env.WF)
    (contract : registry.EnvironmentContract env declarations)
    (H : ConcretePattern registry env (.app ((Pattern.const rc).varN mr) ((Pattern.const cc).varN kc)) r)
    (hΓ : OnCtx Γ (env.IsType U)) (hl : env.projections family info)
    (hs : env.HasType U Γ (VExpr.mkApps (.const cc lsc) fs) (VExpr.mkApps (.const family ls) ps))
    (hlen : fs.length = kc) : cc = info.ctorName ∧ kc = info.nparams + info.numFields := by
  have hmajor : ∃ equation, env.defeqs equation ∧ equation.HasConstructorMajor cc := by
    rcases H with H | ⟨_, H⟩ | H
    · exact (DefinitionPattern.not_iota (recursor := rc) (major := mr) (ctor := cc) (fields := kc) H).elim
    · obtain ⟨hq, -, -, hccq, -⟩ := QuotPattern.registered (recursor := rc) (major := mr)
        (ctor := cc) (fields := kc) H
      subst hccq
      exact ⟨quotDefEq, hq.equation, ⟨_, [.param 0], [.bvar 5, .bvar 4, .bvar 0], rfl⟩⟩
    · obtain ⟨data, index, equation, _, hr, _, _, hg, he, _⟩ := H.generated
      obtain ⟨-, -, hccd, -⟩ := SimplePattern.iota_toPattern_inj (a := rc) (b := mr) (c := cc)
        (d := kc) he
      subst hccd
      exact ⟨equation, hr.equation_present hg, hr.equation_major hg⟩
  obtain ⟨equation, hdf, hm⟩ := hmajor
  obtain ⟨hcc, hfs⟩ := henv.installed_major_struct hΓ hdf hm hl hs
  exact ⟨hcc, hlen ▸ hfs⟩

/-- Native iota computation at a structure constructor reads only its
fields, not its parameters. -/
theorem ConcretePattern.iota_params (henv : env.WF)
    (contract : registry.EnvironmentContract env declarations)
    {r : (Pattern.app ((Pattern.const rc).varN mr) ((Pattern.const cc).varN kc)).RHS ×
      (Pattern.app ((Pattern.const rc).varN mr) ((Pattern.const cc).varN kc)).Check}
    (H : ConcretePattern registry env (.app ((Pattern.const rc).varN mr) ((Pattern.const cc).varN kc)) r)
    (hl : env.projections family info) (hcc : cc = info.ctorName)
    (hm : ((Pattern.const cc).varN kc).Matches (VExpr.mkApps (.const cc lsc) (ps ++ fields)) lsc g)
    (hm' : ((Pattern.const cc).varN kc).Matches (VExpr.mkApps (.const cc lsc') (ps' ++ fields)) lsc' g')
    (hps : ps.length = info.nparams) (hps' : ps'.length = info.nparams) :
    (∀ (m1 : List VLevel) (g1 : ((Pattern.const rc).varN mr).Path → VExpr),
      Pattern.RHS.apply (p := .app ((Pattern.const rc).varN mr) ((Pattern.const cc).varN kc))
          m1 (Sum.elim g1 g) r.1 =
        Pattern.RHS.apply (p := .app ((Pattern.const rc).varN mr) ((Pattern.const cc).varN kc))
          m1 (Sum.elim g1 g') r.1) ∧
    (∀ (m1 : List VLevel) (g1 : ((Pattern.const rc).varN mr).Path → VExpr)
      (df : VExpr → VExpr → Prop),
      Pattern.Check.OK (p := .app ((Pattern.const rc).varN mr) ((Pattern.const cc).varN kc))
          df m1 (Sum.elim g1 g) r.2 →
        Pattern.Check.OK (p := .app ((Pattern.const rc).varN mr) ((Pattern.const cc).varN kc))
          df m1 (Sum.elim g1 g') r.2) := by
  rcases H with H | ⟨hen, H⟩ | H
  · exact (DefinitionPattern.not_iota (recursor := rc) (major := mr) (ctor := cc) (fields := kc) H).elim
  · obtain ⟨hq, -, -, hccq, -⟩ := QuotPattern.registered (recursor := rc) (major := mr)
      (ctor := cc) (fields := kc) H
    exfalso
    have hrf := henv.ordered.projection_resultFamily hl
    rw [← hcc, hccq] at hrf
    have hF := hrf.unique (⟨_, [.param 0], hq.constructor, by rfl⟩ : env.ResultFamily ``Quot.mk ``Quot)
    subst hF
    exact (WF'.quot_no_projection contract.history (contract.quotient.mp hen)).2 info hl
  · obtain ⟨data, index, equation, hclosed, hr, _, _, hg, he, hrhs⟩ := H.generated
    obtain ⟨hrc, hmr, hccd, hkc⟩ := SimplePattern.iota_toPattern_inj (a := rc) (b := mr) (c := cc)
      (d := kc) he
    subst hrc hmr hccd hkc
    obtain rfl := eq_of_heq hrhs
    have hcount := hr.rule_param_count henv hg hl hcc
    have hargs := Pattern.Matches.const_arguments_eq hm
    have hargs' := Pattern.Matches.const_arguments_eq hm'
    refine ⟨fun m1 g1 => ?_, fun m1 g1 df h => ?_⟩
    · dsimp only
      rw [NativeRecursorData.ruleRHS]
      refine (Pattern.RHS.applyArgs_apply (p := data.rulePattern index equation) _ _).trans
        (Eq.trans ?_ (Pattern.RHS.applyArgs_apply (p := data.rulePattern index equation) _ _).symm)
      rw [NativeRecursorData.ruleCaptures]
      simp only [List.map_append, List.map_map]
      have hpre : ∀ (L : List ((Pattern.const data.name).varN data.majorOffset).RHS),
          List.map ((fun rhs => Pattern.RHS.apply (p := data.rulePattern index equation) m1 (Sum.elim g1 g) rhs) ∘
            Pattern.RHS.mapPaths (q := data.rulePattern index equation) Sum.inl) L =
          List.map ((fun rhs => Pattern.RHS.apply (p := data.rulePattern index equation) m1 (Sum.elim g1 g') rhs) ∘
            Pattern.RHS.mapPaths (q := data.rulePattern index equation) Sum.inl) L := by
        intro L
        apply List.map_congr_left
        intro x _
        exact (Pattern.RHS.mapPaths_apply (q := data.rulePattern index equation) (levels := m1)
          (values := Sum.elim g1 g) Sum.inl x).trans
          (Pattern.RHS.mapPaths_apply (q := data.rulePattern index equation) (levels := m1)
            (values := Sum.elim g1 g') Sum.inl x).symm
      have hpost : ∀ (L : List ((Pattern.const (data.ruleConstructor index)).varN
          (NativeRecursorData.ruleMajorArguments equation).length).RHS),
          List.map ((fun rhs => Pattern.RHS.apply (p := data.rulePattern index equation) m1 (Sum.elim g1 g) rhs) ∘
            Pattern.RHS.mapPaths (q := data.rulePattern index equation) Sum.inr) L =
          List.map (fun rhs => rhs.apply m1 g) L := by
        intro L
        apply List.map_congr_left
        intro x _
        exact Pattern.RHS.mapPaths_apply (q := data.rulePattern index equation) Sum.inr x
      have hpost' : ∀ (L : List ((Pattern.const (data.ruleConstructor index)).varN
          (NativeRecursorData.ruleMajorArguments equation).length).RHS),
          List.map ((fun rhs => Pattern.RHS.apply (p := data.rulePattern index equation) m1 (Sum.elim g1 g') rhs) ∘
            Pattern.RHS.mapPaths (q := data.rulePattern index equation) Sum.inr) L =
          List.map (fun rhs => rhs.apply m1 g') L := by
        intro L
        apply List.map_congr_left
        intro x _
        exact Pattern.RHS.mapPaths_apply (q := data.rulePattern index equation) Sum.inr x
      rw [hpre, hpost, hpost', List.map_drop, List.map_drop, hargs m1, hargs' m1]
      have hd : ps.length ≤ (NativeRecursorData.ruleMajorArguments equation).length -
          data.schema.signature.constructors[index].fields.length := by omega
      have hd' : ps'.length ≤ (NativeRecursorData.ruleMajorArguments equation).length -
          data.schema.signature.constructors[index].fields.length := by omega
      rw [List.drop_append_ge hd, List.drop_append_ge hd', hps, hps']
      rfl
    · revert h
      unfold NativeRecursorData.ruleCheck
      split <;> simp [Pattern.Check.OK]

end

end Lean4Lean.VEnv
