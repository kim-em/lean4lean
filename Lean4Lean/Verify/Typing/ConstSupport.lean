import Lean4Lean.Theory.Inductive
import Lean4Lean.Theory.Typing.HeadInjectivity.Rules.NestedStub

/-! # Typed terms avoid fresh constants

A typing derivation of an ordered environment cannot introduce a constant absent from the
environment (`VEnv.IsDefEq.noConsts`), provided the registered reduction rules do not
(`VEnv.PatsAvoidConsts`). For a well-formed environment the rules do not
(`VEnv.WF.patsAvoidFreshConsts`): every registered pattern is the ι entry of a recursor rule of
an installed block (`VEnv.WF'.pats_origin`), whose reduct template is read off a generated
equation (`VInductDecl.RecsCompiled`); for an ordinary block the template mentions only
constants of the recursor's type, typed at the projection stage (`VInductDecl.WF.recs_wf`), and
the block's recursor names (`Instance.equation_rhs_containsAnyConst`); for a nested block the
restored template is typed in the recursor stage (`VInductDecl.WF.nestedRules_wf`, wave 3). -/

namespace Lean4Lean

namespace VExpr

theorem containsAnyConst_inst_eq_false
    (body arg : VExpr) (k : Nat)
    (hbody : body.containsAnyConst names = false)
    (harg : arg.containsAnyConst names = false) :
    (body.inst arg k).containsAnyConst names = false := by
  induction body generalizing k <;>
    simp_all [VExpr.inst, VExpr.containsAnyConst]
  case bvar i =>
    simp only [VExpr.instVar]
    split
    · rfl
    · split
      · simpa using harg
      · rfl

end VExpr

/-- Every type stored in a local typing context avoids `names`. -/
def CtxAvoidsConsts (names : List Lean.Name) (Gamma : List VExpr) : Prop :=
  ∀ type ∈ Gamma, type.containsAnyConst names = false

theorem CtxAvoidsConsts.nil : CtxAvoidsConsts names [] := fun _ h => by simp at h

theorem CtxAvoidsConsts.cons
    (H : CtxAvoidsConsts names Gamma)
    (hA : A.containsAnyConst names = false) :
    CtxAvoidsConsts names (A :: Gamma) := by
  intro type htype
  simp only [List.mem_cons] at htype
  rcases htype with rfl | htype
  · exact hA
  · exact H type htype

theorem Lookup.noConsts
    (Hctx : CtxAvoidsConsts names Gamma)
    (H : Lookup Gamma index type) :
    type.containsAnyConst names = false := by
  induction H with
  | zero =>
      simp only [VExpr.containsAnyConst_liftN]
      exact Hctx _ (by simp)
  | @succ Gamma index type domain H ih =>
      have htail : CtxAvoidsConsts names Gamma := by
        intro current hcurrent
        exact Hctx current (by simp [hcurrent])
      simpa using VExpr.containsAnyConst_liftN
        (e := type) (names := names) 1 0 |>.trans (ih htail)

/-- Every registered reduction rule produces a reduct avoiding `names` from a redex avoiding
`names`: the fixed parts of its right-hand side avoid them. -/
def VEnv.PatsAvoidConsts (env : VEnv) (names : List Lean.Name) : Prop :=
  ∀ {p : Pattern} {r : p.RHS × p.Check} {e m1 m2}, env.pats p r → p.Matches e m1 m2 →
    e.containsAnyConst names = false → (r.1.apply m1 m2).containsAnyConst names = false

theorem VEnv.PatsAvoidConsts.mono {env env' : VEnv} (hle : env ≤ env')
    (H : env'.PatsAvoidConsts names) : env.PatsAvoidConsts names :=
  fun hp => H (hle.pats hp)

theorem VEnv.PatsAvoidConsts.of_pats_eq {env env' : VEnv} (h : env'.pats = env.pats)
    (H : env.PatsAvoidConsts names) : env'.PatsAvoidConsts names :=
  fun hp => H (h ▸ hp)

/-- A typing derivation cannot introduce a selected constant when the
environment declarations used by `constDF`/`extra`, the local context, and
all directly looked-up constants avoid it.  The result is simultaneous for
both endpoints and the inferred type because eta/beta expose type syntax. -/
theorem VEnv.IsDefEq.noConsts
    (Htypes : OnTypes env fun _ e A =>
      e.containsAnyConst names = false ∧
      A.containsAnyConst names = false)
    (Hfresh : ∀ {name ci}, env.constants name = some ci → name ∉ names)
    (Hpats : env.PatsAvoidConsts names)
    (Hctx : CtxAvoidsConsts names Gamma)
    (H : env.IsDefEq U Gamma lhs rhs type) :
    lhs.containsAnyConst names = false ∧
    rhs.containsAnyConst names = false ∧
    type.containsAnyConst names = false := by
  induction H with
  | bvar Hlookup =>
      exact ⟨rfl, rfl, Hlookup.noConsts Hctx⟩
  | symm _ ih =>
      specialize ih Hctx
      exact ⟨ih.2.1, ih.1, ih.2.2⟩
  | trans _ _ ihLeft ihRight =>
      specialize ihLeft Hctx
      specialize ihRight Hctx
      exact ⟨ihLeft.1, ihRight.2.1, ihLeft.2.2⟩
  | sortDF => exact ⟨rfl, rfl, rfl⟩
  | @constDF c ci levels levels' Gamma Hlookup _ _ _ _ =>
      have hname : names.contains c = false := by
        exact Bool.eq_false_iff.mpr fun hcontains =>
          Hfresh Hlookup (by simpa using hcontains)
      have htype := (Htypes.1 Hlookup).choose_spec.1
      exact ⟨hname, hname, by simpa using htype⟩
  | pat hp hm _ _ _ ih =>
      have ih := ih Hctx
      exact ⟨ih.1, Hpats hp hm ih.1, ih.2.2⟩
  | appDF _ _ ihFn ihArg =>
      specialize ihFn Hctx
      specialize ihArg Hctx
      rcases ihFn with ⟨hfn, hfn', hforall⟩
      rcases ihArg with ⟨harg, harg', hA⟩
      simp only [VExpr.containsAnyConst,
        Bool.or_eq_false_iff] at hforall
      exact ⟨Bool.or_eq_false_iff.mpr ⟨hfn, harg⟩,
        Bool.or_eq_false_iff.mpr ⟨hfn', harg'⟩,
        VExpr.containsAnyConst_inst_eq_false _ _ _ hforall.2 harg⟩
  | @projDF typeName info levels params index sourceMajor fieldType Gamma
      fieldLevel major indexArgs major'
      hinfo hlevels huvars hparams hindices hfield hfieldTyping
      hmajor hmajor' _ _ ihField ihMajor ihMajor' =>
      specialize ihField Hctx
      specialize ihMajor Hctx
      specialize ihMajor' Hctx
      have howner :=
        (VExpr.containsAnyConst_mkApps_eq_false_iff
          (.const typeName levels) (params ++ indexArgs)).mp ihMajor.2.2
      have hname : names.contains typeName = false := by
        simpa [VExpr.containsAnyConst] using howner.1
      simp only [VExpr.containsAnyConst, Bool.or_eq_false_iff]
      exact ⟨⟨hname, ihMajor.2.1⟩,
        ⟨hname, ihMajor'.2.1⟩, ihField.1⟩
  | lamDF _ _ ihType ihBody =>
      specialize ihType Hctx
      rcases ihType with ⟨hA, hA', _⟩
      rcases ihBody (Hctx.cons hA) with ⟨hbody, hbody', hB⟩
      exact ⟨Bool.or_eq_false_iff.mpr ⟨hA, hbody⟩,
        Bool.or_eq_false_iff.mpr ⟨hA', hbody'⟩,
        Bool.or_eq_false_iff.mpr ⟨hA, hB⟩⟩
  | forallEDF _ _ ihType ihBody =>
      specialize ihType Hctx
      rcases ihType with ⟨hA, hA', _⟩
      rcases ihBody (Hctx.cons hA) with ⟨hbody, hbody', _⟩
      exact ⟨Bool.or_eq_false_iff.mpr ⟨hA, hbody⟩,
        Bool.or_eq_false_iff.mpr ⟨hA', hbody'⟩, rfl⟩
  | defeqDF _ _ ihType ihTerm =>
      specialize ihType Hctx
      specialize ihTerm Hctx
      exact ⟨ihTerm.1, ihTerm.2.1, ihType.2.1⟩
  | beta _ _ ihBody ihArg =>
      specialize ihArg Hctx
      rcases ihArg with ⟨harg, harg', hA⟩
      rcases ihBody (Hctx.cons hA) with ⟨hbody, _, hB⟩
      exact ⟨Bool.or_eq_false_iff.mpr
          ⟨Bool.or_eq_false_iff.mpr ⟨hA, hbody⟩, harg⟩,
        VExpr.containsAnyConst_inst_eq_false _ _ _ hbody harg',
        VExpr.containsAnyConst_inst_eq_false _ _ _ hB harg'⟩
  | eta _ ih =>
      specialize ih Hctx
      rcases ih with ⟨he, he', hforall⟩
      simp only [VExpr.containsAnyConst,
        Bool.or_eq_false_iff] at hforall
      refine ⟨Bool.or_eq_false_iff.mpr ⟨hforall.1,
          Bool.or_eq_false_iff.mpr ⟨?_, rfl⟩⟩,
        he', Bool.or_eq_false_iff.mpr hforall⟩
      simpa using he
  | proofIrrel _ _ _ ihProof ihLeft ihRight =>
      specialize ihProof Hctx
      specialize ihLeft Hctx
      specialize ihRight Hctx
      exact ⟨ihLeft.1, ihRight.1, ihProof.1⟩
  | extra Hdf _ _ =>
      have hstored := Htypes.2 Hdf
      exact ⟨by simpa using hstored.1.1,
        by simpa using hstored.2.1,
        by simpa using hstored.1.2⟩
  | projIota _ _ _ _ ihProj ihField =>
      specialize ihProj Hctx
      specialize ihField Hctx
      exact ⟨ihProj.1, ihField.1, ihProj.2.2⟩
  | structEta _ _ _ _ _ ihE ihCtor =>
      specialize ihE Hctx
      specialize ihCtor Hctx
      exact ⟨ihCtor.1, ihE.1, ihE.2.2⟩
  | unitLike _ _ _ _ _ _ ihE ihE' =>
      specialize ihE Hctx
      specialize ihE' Hctx
      exact ⟨ihE.1, ihE'.1, ihE.2.2⟩

/-! ## Ordered environments whose rules avoid the names -/

/-- All declarations stored in an ordered environment avoid names which are absent from that
environment, given that its registered rules avoid them. The proof follows the same
well-founded environment induction as `VEnv.Ordered.closed`. -/
theorem VEnv.Ordered.onTypes_noFreshConsts
    (Henv : VEnv.Ordered env)
    (Hfresh : ∀ name ∈ names, env.constants name = none)
    (Hpats : env.PatsAvoidConsts names) :
    OnTypes env fun _ e A =>
      e.containsAnyConst names = false ∧
      A.containsAnyConst names = false := by
  let motive := fun (current : VEnv) (_ : Nat) (e A : VExpr) =>
    ∀ selected : List Lean.Name,
      (∀ name ∈ selected, current.constants name = none) →
      current.PatsAvoidConsts selected →
      e.containsAnyConst selected = false ∧
      A.containsAnyConst selected = false
  have Hall : OnTypes env (motive env) := Henv.induction motive
    (fun Hle Hsupport selected hfresh hpats => by
      apply Hsupport selected
      · intro name hname
        exact Hle.constants_eq_none_left (hfresh name hname)
      · exact VEnv.PatsAvoidConsts.mono Hle hpats)
    (fun _Hordered Hstored Htyping selected hfresh hpats => by
      have Hstored' :=
        Hstored.mono VEnv.LE.rfl (fun H => H selected hfresh hpats)
      have Hresult := Htyping.noConsts Hstored' (fun hlookup hname => by
        rw [hfresh _ hname] at hlookup
        contradiction) hpats CtxAvoidsConsts.nil
      exact ⟨Hresult.1, Hresult.2.2⟩)
  exact Hall.mono VEnv.LE.rfl (fun H => H names Hfresh Hpats)

/-- Derivation-level form of `Ordered.onTypes_noFreshConsts`. -/
theorem VEnv.IsDefEq.noFreshConsts'
    (Henv : VEnv.Ordered env)
    (Hfresh : ∀ name ∈ names, env.constants name = none)
    (Hpats : env.PatsAvoidConsts names)
    (Hctx : CtxAvoidsConsts names Gamma)
    (H : env.IsDefEq U Gamma lhs rhs type) :
    lhs.containsAnyConst names = false ∧
    rhs.containsAnyConst names = false ∧
    type.containsAnyConst names = false := by
  apply H.noConsts (Henv.onTypes_noFreshConsts Hfresh Hpats)
  · intro name ci hlookup hname
    rw [Hfresh name hname] at hlookup
    contradiction
  · exact Hpats
  · exact Hctx

/-! ## The rules of a well-formed environment avoid its fresh names -/

/-- The reduct of a freshly registered ι rule of a well-formed declaration avoids the names
absent from the resulting environment, given that the rules of the environment before it
do. -/
theorem VEnv.addInduct_rule_reductAvoids {env env' : VEnv} (hW : env.WF) {decl : VInductDecl}
    (hdecl : decl.WF env) (hadd : env.addInduct decl = some env') {names : List Lean.Name}
    (Hfresh : ∀ name ∈ names, env'.constants name = none) (hpats : env.PatsAvoidConsts names)
    {rec : VRecursor} (hrec : rec ∈ decl.recs) {ru : VRecRule} (hru : ru ∈ rec.rules)
    (hc : ru.rhs.Closed) {e : VExpr} {m1 : List VLevel}
    {m2 : (SimplePattern.iota rec.name rec.getMajorIdx ru.ctor
      (ru.ctorParams + ru.nfields)).toPattern.Path → VExpr}
    (hm : (SimplePattern.iota rec.name rec.getMajorIdx ru.ctor
      (ru.ctorParams + ru.nfields)).toPattern.Matches e m1 m2)
    (he : e.containsAnyConst names = false) :
    ((SimplePattern.iotaRHS rec.name ru.ctor rec.numParams rec.numMotives rec.numMinors
      rec.numIndices ru.ctorParams ru.nfields ru.rhs hc).apply m1 m2).containsAnyConst names =
      false := by
  obtain ⟨recArgs, ctorArgs, lsC, h1, h2, rfl, happ⟩ :=
    SimplePattern.iotaRHS_apply_of_matches (k := rec.numParams + rec.numMotives + rec.numMinors)
      (nind := rec.numIndices) (cnp := ru.ctorParams) (nf := ru.nfields) (rhs := ru.rhs) (hc := hc)
      hm
  unfold SimplePattern.iotaRHS
  erw [happ]
  rw [VExpr.containsAnyConst_mkApps_eq_false_iff, VExpr.containsAnyConst_instL]
  rw [VExpr.containsAnyConst_mkApps_eq_false_iff] at he
  refine ⟨?_, fun arg harg => ?_⟩
  · -- the template avoids the names
    obtain ⟨block, base, expanded, s, g, aux, hcomp, hrecsOf, hbase, C, hcont, df, hdf, hOf⟩ :=
      hdecl.rule_block hrec hru
    obtain ⟨envT, envC, envR, hT, hC, hR, hP⟩ := VEnv.addInduct_stages hadd
    have hPstage : decl.addTypesCtorsProjs env = some (decl.addProjs envC) :=
      VEnv.addTypesCtorsProjs_eq_some (Option.bind_eq_some_iff.2 ⟨envT, hT, hC⟩)
    have hRstage : decl.addTypesCtorsProjsRecs env = some envR := by
      unfold VInductDecl.addTypesCtorsProjsRecs; rw [hPstage]; exact hR
    have hordP : VEnv.Ordered (decl.addProjs envC) :=
      VEnv.addTypesCtorsProjs_ordered hW.ordered hdecl hPstage
    have hordR : VEnv.Ordered envR := VEnv.addRecs_ordered hdecl hPstage hordP hR
    have hRle : envR ≤ env' := VEnv.addRules_le hP
    have hPle : decl.addProjs envC ≤ env' := (VEnv.addRecs_le hR).trans hRle
    have hfreshR : ∀ n ∈ names, envR.constants n = none :=
      fun n hn => hRle.constants_eq_none_left (Hfresh n hn)
    have hfreshP : ∀ n ∈ names, (decl.addProjs envC).constants n = none :=
      fun n hn => hPle.constants_eq_none_left (Hfresh n hn)
    have hpatsP : (decl.addProjs envC).PatsAvoidConsts names :=
      VEnv.PatsAvoidConsts.of_pats_eq
        (by rw [VEnv.addProjs_pats, VEnv.addCtors_pats hC, VEnv.addTypes_pats hT]) hpats
    have hpatsR : envR.PatsAvoidConsts names :=
      VEnv.PatsAvoidConsts.of_pats_eq (H := hpats) (by
        rw [VEnv.addRecs_pats hR, VEnv.addProjs_pats, VEnv.addCtors_pats hC, VEnv.addTypes_pats hT])
    cases aux with
    | nil =>
      obtain ⟨index, rfl, -, -, -, -, hrhs⟩ := C.ordinary_rule hdf hOf
      rw [hrhs]
      apply g.equation_rhs_containsAnyConst names index s.constructors[index].owner
      · obtain ⟨r', hr', hr'eq⟩ := C.ordinary_rec_of hrecsOf s.constructors[index].owner
        have hty := hdecl.recs_wf _ hPstage r' hr'
        have hrt : r'.type = g.recursorType s.constructors[index].owner :=
          congrArg (fun v : VConstVal => v.type) hr'eq
        obtain ⟨u, hu⟩ := hty
        have := (VEnv.IsDefEq.noFreshConsts' hordP hfreshP hpatsP CtxAvoidsConsts.nil hu).1
        rwa [hrt] at this
      · intro o
        obtain ⟨r'', hr'', e⟩ := C.ordinary_rec_of hrecsOf o
        have hfind := VEnv.addInduct_rec_find hadd hr''
        have hn : r''.name = g.recursorName o := congrArg (fun v : VConstVal => v.name) e
        rw [← hn]
        exact Bool.eq_false_iff.mpr fun hcontains => by
          have := Hfresh _ (by simpa using hcontains)
          rw [this] at hfind
          cases hfind
    | cons a rest =>
      have hwf := hdecl.nestedRules_wf hcomp hrecsOf hbase C hcont (by simp) hRstage df hdf
      have := (VEnv.IsDefEq.noFreshConsts' hordR hfreshR hpatsR CtxAvoidsConsts.nil hwf.2).1
      rwa [hOf.1] at this
  · rcases List.mem_append.1 harg with harg | harg
    · exact he.2 _ (List.mem_append_left _ (List.mem_of_mem_take harg))
    · have hmaj := he.2 _ (List.mem_append_right _ (List.mem_singleton_self _))
      rw [VExpr.containsAnyConst_mkApps_eq_false_iff] at hmaj
      exact hmaj.2 _ (List.mem_of_mem_drop harg)

/-- **The rules of a well-formed environment avoid the names absent from it.** By induction on
the declaration history: a freshly registered rule's reduct template is read off its block's
compilation (`VEnv.addInduct_rule_reductAvoids`). -/
theorem VEnv.WF'.patsAvoidFreshConsts {ds : List VDecl} {env : VEnv} (H : env.WF' ds)
    {names : List Lean.Name} (Hfresh : ∀ name ∈ names, env.constants name = none) :
    env.PatsAvoidConsts names := by
  induction H with
  | empty => intro p r e m1 m2 hp; exact (hp : False).elim
  | @decl d env' ds env hd H ih =>
    have hfresh0 : ∀ name ∈ names, env.constants name = none :=
      fun n hn => hd.le.constants_eq_none_left (Hfresh n hn)
    have ih0 : env.PatsAvoidConsts names := ih hfresh0
    rcases hd.pats_eq_or_induct with heq | ⟨decl, hdecl, hadd⟩
    · intro p rr e m1 m2 hp hm he
      exact ih0 (heq ▸ hp) hm he
    · intro p rr e m1 m2 hp hm he
      rcases VEnv.addInduct_pats_origin' hadd hp with hold | ⟨rec, hrec, ru, hru, hc, ea, hrr⟩
      · exact ih0 hold hm he
      · subst ea; subst hrr
        exact VEnv.addInduct_rule_reductAvoids ⟨ds, H⟩ hdecl hadd Hfresh ih0 hrec hru hc hm he
  | inductProjections _ _ _ _ _ _ _ _ _ _ _ _ _ _ ihCtors =>
    intro p rr e m1 m2 hp hm he
    exact ihCtors (fun n hn => by simpa using Hfresh n hn) (by simpa using hp) hm he

theorem VEnv.WF.patsAvoidFreshConsts {env : VEnv} (H : env.WF) {names : List Lean.Name}
    (Hfresh : ∀ name ∈ names, env.constants name = none) : env.PatsAvoidConsts names :=
  let ⟨_, H⟩ := H; H.patsAvoidFreshConsts Hfresh

/-! ## Well-formed environments -/

/-- All declarations stored in a well-formed environment avoid names which are absent from
that environment. -/
theorem VEnv.WF.onTypes_noFreshConsts
    (Henv : VEnv.WF env)
    (Hfresh : ∀ name ∈ names, env.constants name = none) :
    OnTypes env fun _ e A =>
      e.containsAnyConst names = false ∧
      A.containsAnyConst names = false :=
  Henv.ordered.onTypes_noFreshConsts Hfresh (Henv.patsAvoidFreshConsts Hfresh)

/-- Usable derivation-level form of `onTypes_noFreshConsts`. -/
theorem VEnv.IsDefEq.noFreshConsts
    (Henv : VEnv.WF env)
    (Hfresh : ∀ name ∈ names, env.constants name = none)
    (Hctx : CtxAvoidsConsts names Gamma)
    (H : env.IsDefEq U Gamma lhs rhs type) :
    lhs.containsAnyConst names = false ∧
    rhs.containsAnyConst names = false ∧
    type.containsAnyConst names = false :=
  H.noFreshConsts' Henv.ordered Hfresh (Henv.patsAvoidFreshConsts Hfresh) Hctx

theorem VEnv.WF.ctxNoFreshConsts
    (Henv : VEnv.WF env)
    (Hfresh : ∀ name ∈ names, env.constants name = none) :
    ∀ {Gamma}, OnCtx Gamma (env.IsType U) → CtxAvoidsConsts names Gamma
  | [], _ => CtxAvoidsConsts.nil
  | A :: Gamma, ⟨Htail, _level, Htype⟩ => by
      have HtailFree := Henv.ctxNoFreshConsts Hfresh Htail
      have HA := Htype.noFreshConsts Henv Hfresh HtailFree
      exact HtailFree.cons HA.1

/-- A well-formed expression in a well-formed context cannot mention a name
which is absent from its well-formed environment. -/
theorem VExpr.WF.noFreshConsts
    (Henv : VEnv.WF env)
    (Hfresh : ∀ name ∈ names, env.constants name = none)
    (Hctx : OnCtx Gamma (env.IsType U))
    (H : VExpr.WF env U Gamma e) :
    e.containsAnyConst names = false := by
  rcases H with ⟨type, Htyping⟩
  exact (Htyping.noFreshConsts Henv Hfresh
    (Henv.ctxNoFreshConsts Hfresh Hctx)).1

end Lean4Lean
