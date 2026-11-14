import Lean4Lean.Theory.Typing.Lemmas
import Lean4Lean.Theory.Typing.Env
import Lean4Lean.Theory.Typing.QuotLemmas
import Lean4Lean.Theory.Typing.InductiveLemmas

namespace Lean4Lean

theorem VEnv.addConsts_le {env env' : VEnv} : ∀ {cis}, env.addConsts cis = some env' → env ≤ env'
  | [], h => by cases h; exact .rfl
  | _ :: _, h => by
    simp [VEnv.addConsts, Option.bind_eq_some_iff] at h
    obtain ⟨_, h1, h2⟩ := h
    exact (addConst_le h1).trans (addConsts_le h2)

theorem VEnv.addConst_eq_none {env : VEnv} {name ci}
    (h : env.constants name = none) : ∃ env', env.addConst name ci = some env' := by
  unfold VEnv.addConst; rw [h]; exact ⟨_, rfl⟩

theorem VEnv.addConst_constants_eq {env env' : VEnv} {name ci}
    (h : env.addConst name ci = some env') :
    env'.constants = fun n => if name = n then some ci else env.constants n := by
  unfold VEnv.addConst at h; split at h <;> cases h; rfl

/-- A block of constants can be added as long as each name is fresh and the block has no
duplicates; the latter is what `addMutual`'s `found` set checks. -/
theorem VEnv.exists_addConsts {env : VEnv} : ∀ {cis : List VDefVal},
    (∀ ci ∈ cis, env.constants ci.name = none) → (cis.map (·.name)).Nodup →
    ∃ env', env.addConsts cis = some env'
  | [], _, _ => ⟨_, rfl⟩
  | ci :: cis, hfresh, hnd => by
    obtain ⟨env₁, h₁⟩ := VEnv.addConst_eq_none (ci := ci.toVConstant) (hfresh _ (.head _))
    rw [List.map_cons, List.nodup_cons] at hnd
    have ⟨env₂, h₂⟩ := VEnv.exists_addConsts (env := env₁) (cis := cis) (fun c hc => ?_) hnd.2
    · exact ⟨env₂, by simp [VEnv.addConsts, h₁]; exact h₂⟩
    · rw [VEnv.addConst_constants_eq h₁]
      have : ci.name ≠ c.name := fun h => hnd.1 (List.mem_map.2 ⟨c, hc, h.symm⟩)
      simp [this, hfresh c (.tail _ hc)]

theorem VEnv.addConsts_congr {env : VEnv} : ∀ {cis cis' : List VDefVal},
    List.Forall₂ (fun a b => a.toVConstVal = b.toVConstVal) cis cis' →
    env.addConsts cis = env.addConsts cis'
  | [], [], _ => rfl
  | a :: _, b :: _, .cons h t => by
    have h1 : a.name = b.name := congrArg VConstVal.name h
    have h2 : a.toVConstant = b.toVConstant := congrArg VConstVal.toVConstant h
    show (env.addConst a.name a.toVConstant).bind _ = (env.addConst b.name b.toVConstant).bind _
    rw [h1, h2]
    cases env.addConst b.name b.toVConstant
    · rfl
    · exact VEnv.addConsts_congr t

theorem VEnv.addConsts_ordered {env env' : VEnv} : ∀ {cis}, Ordered env →
    (∀ ci ∈ cis, ci.toVConstant.WF env) → env.addConsts cis = some env' → Ordered env'
  | [], h, _, e => by cases e; exact h
  | _ :: _, h, hw, e => by
    simp [VEnv.addConsts, Option.bind_eq_some_iff] at e
    obtain ⟨_, h1, h2⟩ := e
    refine VEnv.addConsts_ordered (.const h (hw _ (.head _)) h1) (fun c hc => ?_) h2
    exact (hw c (.tail _ hc)).mono (VEnv.addConst_le h1)

theorem VEnv.addConsts_constants {env env' : VEnv} : ∀ {cis}, env.addConsts cis = some env' →
    ∀ ci ∈ cis, env'.constants ci.name = some ci.toVConstant
  | [], _, _, hc => nomatch hc
  | _ :: _, e, c, hc => by
    simp [VEnv.addConsts, Option.bind_eq_some_iff] at e
    obtain ⟨_, h1, h2⟩ := e
    cases hc with
    | head => exact (VEnv.addConsts_le h2).constants (VEnv.addConst_self h1)
    | tail _ hc => exact VEnv.addConsts_constants h2 c hc

theorem VEnv.addDefEqs_ordered : ∀ {env : VEnv} {cis}, Ordered env →
    (∀ ci ∈ cis, env.constants ci.name = some ci.toVConstant) →
    (∀ ci ∈ cis, ci.WF env) → Ordered (env.addDefEqs cis)
  | _, [], h, _, _ => h
  | env, ci :: cis, h, hmem, hw => by
    have hci : ci.WF env := hw _ (.head _)
    have hord : Ordered (env.addDefEq ci.toDefEq) := by
      refine .defeq h ⟨?_, hci⟩
      simp [VDefVal.toDefEq]
      rw [← (hci.levelWF ⟨⟩).2.2.instL_id]
      exact .const (hmem _ (.head _)) VLevel.id_WF (by simp)
    show Ordered ((env.addDefEq ci.toDefEq).addDefEqs cis)
    refine VEnv.addDefEqs_ordered hord (fun c hc => ?_) (fun c hc => ?_)
    · exact (VEnv.addDefEq_le (df := ci.toDefEq)).constants (hmem c (.tail _ hc))
    · exact (hw c (.tail _ hc)).mono VEnv.addDefEq_le

/-- A dependency-ordered list of well-formed constants may be viewed as a
sequence of abstract axioms extending a well-formed environment.  Stating
the input typing in the starting environment is sufficient because each
constant can be weakened through the preceding fresh additions. -/
theorem VEnv.WF.addConstVals
    {env env' : VEnv} {cis : List VConstVal}
    (Henv : env.WF)
    (Hwf : ∀ ci ∈ cis, ci.toVConstant.WF env)
    (Hadd : env.addConstVals cis = some env') : env'.WF := by
  induction cis generalizing env env' with
  | nil =>
    simp [VEnv.addConstVals] at Hadd
    subst env'
    exact Henv
  | cons ci cis ih =>
    cases hci : env.addConst ci.name ci.toVConstant with
    | none => simp [VEnv.addConstVals, hci] at Hadd
    | some next =>
      simp [VEnv.addConstVals, hci] at Hadd
      have hhead : ci.toVConstant.WF env := Hwf ci (by simp)
      have Hnext : next.WF := by
        rcases Henv with ⟨ds, Hds⟩
        exact ⟨.axiom ci :: ds, .decl (.axiom hhead hci) Hds⟩
      apply ih Hnext (env' := env')
      · intro ci' hmem
        exact (Hwf ci' (by simp [hmem])).mono (VEnv.addConst_le hci)
      · exact Hadd

/-- The stages of a constructor-and-projection prefix: the type formers, then the constructors,
then the projection entries. -/
theorem VInductDecl.ProjectionStage.stages {env env' : VEnv} {decl : VInductDecl}
    (h : decl.ProjectionStage env env') :
    ∃ envTypes envCtors, env.addConstVals decl.typeConstants = some envTypes ∧
      envTypes.addConstVals decl.constructorConstants = some envCtors ∧
      env' = envCtors.addProjections decl.projectionEntries := by
  have h := h.install
  unfold VInductDecl.addTypesCtorsProjs at h
  obtain ⟨envC, hC, rfl⟩ := Option.map_eq_some_iff.1 h
  obtain ⟨envT, hT, hC⟩ := Option.bind_eq_some_iff.1 hC
  rw [VInductDecl.addTypes_eq_addConstVals] at hT
  rw [VInductDecl.addCtors_eq_addConstVals] at hC
  exact ⟨envT, envC, hT, hC, rfl⟩

/-- A constructor-and-projection prefix from its stages. -/
theorem VInductDecl.ProjectionStage.of_stages {env envTypes envCtors : VEnv} {decl : VInductDecl}
    (hsource : decl.SourceWF env) (hformation : decl.FormationWF env)
    (htypes : env.addConstVals decl.typeConstants = some envTypes)
    (hctors : envTypes.addConstVals decl.constructorConstants = some envCtors) :
    decl.ProjectionStage env (envCtors.addProjections decl.projectionEntries) where
  source := hsource
  formation := hformation
  install := by
    rw [← VInductDecl.addTypes_eq_addConstVals] at htypes
    rw [← VInductDecl.addCtors_eq_addConstVals] at hctors
    simp [VInductDecl.addTypesCtorsProjs, VInductDecl.addTypesCtors, htypes, hctors,
      VInductDecl.addProjs]

/-- A constructor-and-projection prefix only grows the environment. -/
theorem VInductDecl.ProjectionStage.le {env env' : VEnv} {decl : VInductDecl}
    (h : decl.ProjectionStage env env') : env ≤ env' := by
  obtain ⟨_, _, htypes, hctors, rfl⟩ := h.stages
  exact (VEnv.addConstVals_le htypes).trans <|
    (VEnv.addConstVals_le hctors).trans VEnv.addProjections_le

/-- A constructor-and-projection prefix registers no ι rule. -/
theorem VInductDecl.ProjectionStage.pats_eq {env env' : VEnv} {decl : VInductDecl}
    (h : decl.ProjectionStage env env') : env'.pats = env.pats := by
  obtain ⟨_, _, htypes, hctors, rfl⟩ := h.stages
  rw [VEnv.addProjections_pats, VEnv.addConstVals_pats hctors, VEnv.addConstVals_pats htypes]

/-- A constructor-and-projection prefix adds no definitional axiom. -/
theorem VInductDecl.ProjectionStage.defeqs_eq {env env' : VEnv} {decl : VInductDecl}
    (h : decl.ProjectionStage env env') : env'.defeqs = env.defeqs := by
  obtain ⟨_, _, htypes, hctors, rfl⟩ := h.stages
  rw [VEnv.addProjections_defeqs, VEnv.addConstVals_defeqs hctors,
    VEnv.addConstVals_defeqs htypes]

/-- Induction along a well-formed history that presents a constructor-and-projection prefix
(`VEnv.WF'.inductProjections`) by its three parts. The type formers and constructors of the
prefix are typed constants, so the environment `envCtors` that has them and not yet the
projection entries is well formed, by a history `dsC` that lists them as axioms; the case for
the prefix receives the induction hypothesis for `envCtors` as well as for `base`, and has to
account for the projection entries only. -/
theorem VEnv.WF'.stageInduction {motive : ∀ ds env, VEnv.WF' ds env → Prop}
    (empty : motive [] .empty .empty)
    (decl : ∀ {d env' ds env} (hd : VDecl.WF env d env') (H : env.WF' ds),
      motive ds env H → motive (d :: ds) env' (.decl hd H))
    (inductProjections : ∀ {base envTypes envCtors : VEnv} {decl : VInductDecl} {ds dsC}
      (hbase : base.WF' ds) (hctorsWF : envCtors.WF' dsC)
      (hstage : decl.ProjectionStage base (envCtors.addProjections decl.projectionEntries))
      (_ : base.addConstVals decl.typeConstants = some envTypes)
      (_ : envTypes.addConstVals decl.constructorConstants = some envCtors),
      motive ds base hbase → motive dsC envCtors hctorsWF →
      motive (.induct decl :: ds) _ (.inductProjections hstage hbase))
    {ds env} (H : VEnv.WF' ds env) : motive ds env H := by
  have step : ∀ {vs : List VConstVal} {env env' : VEnv} {ds} (H : env.WF' ds),
      motive ds env H → (∀ v ∈ vs, v.toVConstant.WF env) → env.addConstVals vs = some env' →
      ∃ ds' H', motive ds' env' H' := by
    intro vs
    induction vs with
    | nil => intro env env' ds H ih _ hadd; cases hadd; exact ⟨_, H, ih⟩
    | cons v vs ihvs =>
      intro env env' ds H ih hv hadd
      simp only [VEnv.addConstVals] at hadd
      obtain ⟨mid, hmid, hadd⟩ := Option.bind_eq_some_iff.1 hadd
      exact ihvs _ (decl (.axiom (ci := v) (hv v (.head _)) hmid) H ih)
        (fun w hw => (hv w (.tail _ hw)).mono (VEnv.addConst_le hmid)) hadd
  induction H with
  | empty => exact empty
  | decl hd H ih => exact decl hd H ih
  | inductProjections hstage H ih =>
    obtain ⟨envTypes, envCtors, htypes, hctors, rfl⟩ := hstage.stages
    obtain ⟨_, HT, ihT⟩ := step H ih (fun v hv => by
      obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hv
      exact hstage.source.sourceTypes t ht) htypes
    obtain ⟨_, HC, ihC⟩ := step HT ihT (hstage.source.constructorsWF_at htypes) hctors
    exact inductProjections H HC hstage htypes hctors ih ihC

theorem VEnv.WF.ordered : WF env → Ordered env
  | ⟨ds, H⟩ => by
    induction H using VEnv.WF'.stageInduction with
    | empty => exact .empty
    | decl h _ ih =>
      cases h with
      | «axiom» h1 h2 => exact .const ih h1 h2
      | @«def» env env' ci h1 h2 =>
        refine .defeq (.const ih (h1.isType ih ⟨⟩) h2) ⟨?_, ?_⟩
        · simp [VDefVal.toDefEq]
          rw [← (h1.levelWF ⟨⟩).2.2.instL_id]
          exact .const (addConst_self h2) VLevel.id_WF (by simp)
        · exact h1.mono (addConst_le h2)
      | mutualDef h0 h1 h2 =>
        exact VEnv.addDefEqs_ordered (VEnv.addConsts_ordered ih h0 h1)
          (VEnv.addConsts_constants h1) h2
      | «opaque» h1 h2 => exact .const ih (h1.isType ih ⟨⟩) h2
      | «example» _ => exact ih
      | quot h1 h2 => exact addQuot_WF ih h1 h2
      | induct h1 h2 => exact addInduct_WF ih h1 h2
    | inductProjections _ _ hstage htypes hctors ihBase ihCtors =>
      exact .inductProjections ihBase ihCtors hstage.source
        (hstage.formation.sourceParameterWF htypes) htypes hctors

instance : CoeOut (VEnv.WF env) env.Ordered := ⟨(·.ordered)⟩

/-- Every `VDecl.WF` step only grows the environment. -/
theorem VDecl.WF.le {env d env'} (h : VDecl.WF env d env') : env ≤ env' := by
  cases h with
  | «axiom» _ h2 => exact VEnv.addConst_le h2
  | «def» _ h2 => exact (VEnv.addConst_le h2).trans VEnv.addDefEq_le
  | mutualDef _ h2 _ => exact (VEnv.addConsts_le h2).trans VEnv.addDefEqs_le
  | «opaque» _ h2 => exact VEnv.addConst_le h2
  | «example» _ => exact .rfl
  | quot _ h2 => exact VEnv.addQuot_le h2
  | induct _ h2 => exact VEnv.addInduct_le h2

/-- A well-formed prefix is a sub-environment. -/
theorem VEnv.WFPrefix.le {env env₀ : VEnv} (h : env.WFPrefix env₀) : env₀ ≤ env := by
  induction h with
  | rfl => exact .rfl
  | decl hd _ ih => exact ih.trans hd.le
  | inductProjections hs _ ih => exact ih.trans hs.le

/-- `OnTypes (EnvStrong ·)` is carried along a fold over `addConst`, given the typing of every
added constant in the environment the fold starts from. -/
theorem VEnv.foldlM_addConst_strong {α} {nm : α → Name} {ci : α → VConstant} :
    ∀ {l : List α} {init final : VEnv},
      Ordered init → OnTypes init (EnvStrong init) → (∀ a ∈ l, (ci a).WF init) →
      l.foldlM (fun e a => e.addConst (nm a) (ci a)) init = some final →
      OnTypes final (EnvStrong final)
  | [], _, _, _, IH, _, h => by simp [List.foldlM] at h; subst h; exact IH
  | a :: _, _, _, hord, IH, hwf, h => by
    simp only [List.foldlM] at h
    obtain ⟨env₁, h₁, h₂⟩ := Option.bind_eq_some_iff.1 h
    have hle₁ := addConst_le h₁
    exact foldlM_addConst_strong
      (.const hord (hwf a (.head _)) h₁)
      (OnTypes.addConst hord IH (hwf a (.head _)) h₁)
      (fun b hb => (hwf b (.tail _ hb)).mono hle₁) h₂

/-- Adding a block of definitional axioms whose two sides are strongly typed in the
environment the block starts from leaves every constant and definitional axiom strongly
typed. -/
theorem VEnv.addDefEqs_strong : ∀ {env : VEnv} {cis : List VDefVal},
    OnTypes env (EnvStrong env) →
    (∀ ci ∈ cis, EnvStrong env ci.toDefEq.uvars ci.toDefEq.lhs ci.toDefEq.type ∧
      EnvStrong env ci.toDefEq.uvars ci.toDefEq.rhs ci.toDefEq.type) →
    OnTypes (env.addDefEqs cis) (EnvStrong (env.addDefEqs cis))
  | _, [], IH, _ => IH
  | env, ci :: _, IH, h => by
    show OnTypes ((env.addDefEq ci.toDefEq).addDefEqs _) _
    refine addDefEqs_strong (OnTypes.addDefEq IH (h _ (.head _)).1 (h _ (.head _)).2)
      fun c hc => ⟨(h c (.tail _ hc)).1.mono addDefEq_le, (h c (.tail _ hc)).2.mono addDefEq_le⟩

/-- Registering the ι rules of a block adds neither a constant nor a definitional axiom, so
strong typing of both survives stage 3 of `addInduct`. -/
theorem VEnv.addRules_strong {decl : VInductDecl} {envR env' : VEnv}
    (IH : OnTypes envR (EnvStrong envR)) (h : decl.addRules envR = some env') :
    OnTypes env' (EnvStrong env') := by
  unfold VInductDecl.addRules at h
  refine foldlM_inv (P := fun e => OnTypes e (EnvStrong e)) (fun _ _ _ _ hIH hf => ?_) IH h
  refine foldlM_inv (P := fun e => OnTypes e (EnvStrong e)) (fun _ _ _ _ hIH hf => ?_) hIH hf
  unfold addRecRule at hf
  split at hf
  · cases hf; exact OnTypes.addPat hIH
  · cases hf

/-- Adding the quotient constants and the quotient rule to a strong environment leaves every
constant and definitional axiom strongly typed. -/
theorem VEnv.addQuot_strong {env env' : VEnv} (hord : Ordered env)
    (IH : OnTypes env (EnvStrong env)) (hq : QuotReady env)
    (h : env.addQuot = some env') : OnTypes env' (EnvStrong env') := by
  obtain ⟨q1, q2, q3, q4, w1, a1, w2, a2, w3, a3, w4, a4, wdf, rfl⟩ := addQuot_chain hq h
  have O1 : Ordered q1 := .const hord w1 a1
  have I1 := OnTypes.addConst hord IH w1 a1
  have O2 : Ordered q2 := .const O1 w2 a2
  have I2 := OnTypes.addConst O1 I1 w2 a2
  have O3 : Ordered q3 := .const O2 w3 a3
  have I3 := OnTypes.addConst O2 I2 w3 a3
  have O4 : Ordered q4 := .const O3 w4 a4
  have I4 := OnTypes.addConst O3 I3 w4 a4
  exact OnTypes.addDefEq I4 (EnvStrong.of_hasType O4 I4 wdf.1)
    (EnvStrong.of_hasType O4 I4 wdf.2)

/-- Adding a well-formed inductive declaration to a strong environment leaves every constant
and definitional axiom strongly typed: the three constant stages by
`foldlM_addConst_strong`, each in the environment `VInductDecl.WF` types its constants in,
and the ι-rule stage by `addRules_strong`. -/
theorem VEnv.addInduct_strong {env env' : VEnv} {decl : VInductDecl}
    (hord : Ordered env) (IH : OnTypes env (EnvStrong env)) (hdecl : decl.WF env)
    (h : env.addInduct decl = some env') : OnTypes env' (EnvStrong env') := by
  obtain ⟨envT, envC, envR, hT, hC, hR, hP⟩ := addInduct_stages h
  have hTC : decl.addTypesCtors env = some envC := by
    unfold VInductDecl.addTypesCtors; rw [hT]; exact hC
  have hTCP : decl.addTypesCtorsProjs env = some (decl.addProjs envC) :=
    addTypesCtorsProjs_eq_some hTC
  have hordT := addTypes_ordered hord hdecl hT
  have hordC := addCtors_ordered hdecl hT hordT hC
  have hordP := addProjs_ordered hord hdecl hTC hordC
  have IHT : OnTypes envT (EnvStrong envT) := by
    unfold VInductDecl.addTypes at hT
    exact foldlM_addConst_strong hord IH hdecl.types_wf hT
  have IHC : OnTypes envC (EnvStrong envC) := by
    have hcw : ∀ c ∈ decl.types.flatMap (·.ctors), c.toVConstant.WF envT := fun c hc => by
      obtain ⟨t, ht, hc⟩ := List.mem_flatMap.1 hc
      exact hdecl.ctors_wf envT hT t ht c hc
    unfold VInductDecl.addCtors at hC
    exact foldlM_addConst_strong hordT IHT hcw hC
  have IHP : OnTypes (decl.addProjs envC) (EnvStrong (decl.addProjs envC)) :=
    OnTypes.addProjections IHC
  have IHR : OnTypes envR (EnvStrong envR) := by
    have hrw := hdecl.recs_wf _ hTCP
    unfold VInductDecl.addRecs at hR
    exact foldlM_addConst_strong hordP IHP hrw hR
  exact addRules_strong IHR hP

/-- Every constant and definitional axiom of a well-formed environment is strongly typed:
each is strengthened by `IsDefEq.strong'` in the environment it is typed in, then lifted by
monotonicity. -/
theorem VEnv.WF.strong {env : VEnv} (H : env.WF) : OnTypes env (EnvStrong env) := by
  have key : ∀ {ds e}, WF' ds e → OnTypes e (EnvStrong e) := by
    intro ds e H
    induction H using VEnv.WF'.stageInduction with
    | empty => exact ⟨nofun, nofun⟩
    | inductProjections _ _ _ _ _ _ ihCtors =>
      exact OnTypes.addProjections ihCtors
    | decl hd hwf IH =>
      have hord := WF.ordered ⟨_, hwf⟩
      clear hwf
      cases hd with
      | «axiom» h1 h2 => exact OnTypes.addConst hord IH h1 h2
      | «opaque» h1 h2 => exact OnTypes.addConst hord IH (h1.isType (Γ := []) hord ⟨⟩) h2
      | «example» _ => exact IH
      | «def» h1 h2 =>
        have hisT := h1.isType (Γ := []) hord ⟨⟩
        have hle₁ := addConst_le h2
        have hord₁ : Ordered _ := .const hord hisT h2
        have IH₁ := OnTypes.addConst hord IH hisT h2
        refine OnTypes.addDefEq IH₁ (EnvStrong.of_hasType hord₁ IH₁ ?_)
          (EnvStrong.of_hasType hord₁ IH₁ (h1.mono hle₁))
        simp [VDefVal.toDefEq]
        rw [← (h1.levelWF ⟨⟩).2.2.instL_id]
        exact .const (addConst_self h2) VLevel.id_WF (by simp)
      | mutualDef h0 h1 h2 =>
        have hord₁ := addConsts_ordered hord h0 h1
        have IH₁ := foldlM_addConst_strong
          (nm := fun c : VDefVal => c.name) (ci := fun c : VDefVal => c.toVConstant)
          hord IH h0 h1
        refine addDefEqs_strong IH₁ fun c hc => ⟨EnvStrong.of_hasType hord₁ IH₁ ?_,
          EnvStrong.of_hasType hord₁ IH₁ (h2 c hc)⟩
        simp [VDefVal.toDefEq]
        rw [← ((h2 c hc).levelWF ⟨⟩).2.2.instL_id]
        exact .const (addConsts_constants h1 c hc) VLevel.id_WF (by simp)
      | quot h1 h2 => exact addQuot_strong hord IH h1 h2
      | induct h1 h2 => exact addInduct_strong hord IH h1 h2
  obtain ⟨_, H⟩ := H
  exact key H

/-- A well-formed environment satisfies the hypotheses of the strong system: `Ordered` and
strong typing of its constants and definitional axioms. -/
theorem VEnv.WF.orderedStrong (H : WF env) : OrderedStrong env :=
  ⟨H.ordered, H.strong⟩

instance : CoeOut (VEnv.WF env) env.OrderedStrong := ⟨(·.orderedStrong)⟩

/-! ### Origin of a well-formed environment's contents -/

namespace VEnv.WF'

/-- Every definitional axiom headed by a constant `c` has `c` declared, and is the only
definitional axiom headed by `c`. -/
private def DefEqsConst (env : VEnv) : Prop :=
  ∀ df c us, env.defeqs df → df.lhs = .const c us →
    env.constants c ≠ none ∧ ∀ df' us', env.defeqs df' → df'.lhs = .const c us' → df = df'

private theorem DefEqsConst.mono {env env' : VEnv} (H : DefEqsConst env) (hle : env ≤ env')
    (hd : env'.defeqs = env.defeqs) : DefEqsConst env' := by
  intro df c us h hl
  rw [hd] at h
  obtain ⟨hc, hu⟩ := H _ _ _ h hl
  obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.1 hc
  exact ⟨by rw [hle.constants ha]; nofun, fun _ _ h' hl' => hu _ _ (hd ▸ h') hl'⟩

private theorem DefEqsConst.addDefEq {env : VEnv} {df₀ : VDefEq} {c₀ us₀}
    (H : DefEqsConst env) (hc : env.constants c₀ ≠ none)
    (hfresh : ∀ df us, env.defeqs df → df.lhs ≠ .const c₀ us)
    (hl : df₀.lhs = .const c₀ us₀) : DefEqsConst (env.addDefEq df₀) := by
  intro df c us h hl'
  rcases h with rfl | h
  · obtain rfl : c = c₀ := by rw [hl] at hl'; cases hl'; rfl
    refine ⟨hc, fun _ _ h' hl'' => ?_⟩
    rcases h' with rfl | h'
    · rfl
    · exact (hfresh _ _ h' hl'').elim
  · obtain ⟨hc', hu⟩ := H _ _ _ h hl'
    refine ⟨hc', fun _ _ h' hl'' => ?_⟩
    rcases h' with rfl | h'
    · obtain rfl : c = c₀ := by rw [hl] at hl''; cases hl''; rfl
      exact (hfresh _ _ h hl').elim
    · exact hu _ _ h' hl''

private theorem DefEqsConst.addDefEq_app {env : VEnv} {df₀ : VDefEq}
    (H : DefEqsConst env) (hl : ∀ c us, df₀.lhs ≠ .const c us) :
    DefEqsConst (env.addDefEq df₀) := by
  intro df c us h hl'
  rcases h with rfl | h
  · exact (hl _ _ hl').elim
  · obtain ⟨hc', hu⟩ := H _ _ _ h hl'
    refine ⟨hc', fun _ _ h' hl'' => ?_⟩
    rcases h' with rfl | h'
    · exact (hl _ _ hl'').elim
    · exact hu _ _ h' hl''

private theorem DefEqsConst.addDefEqs : ∀ {env : VEnv} {cis : List VDefVal},
    DefEqsConst env → (∀ ci ∈ cis, env.constants ci.name ≠ none) →
    (∀ ci ∈ cis, ∀ df us, env.defeqs df → df.lhs ≠ .const ci.name us) →
    (cis.map (·.name)).Nodup → DefEqsConst (env.addDefEqs cis)
  | _, [], H, _, _, _ => H
  | env, ci :: cis, H, hc, hfresh, hnd => by
    rw [List.map_cons, List.nodup_cons] at hnd
    show DefEqsConst ((env.addDefEq ci.toDefEq).addDefEqs cis)
    refine DefEqsConst.addDefEqs
      (H.addDefEq (hc _ (.head _)) (hfresh _ (.head _)) rfl)
      (fun c hm => hc c (.tail _ hm)) (fun c hm df us h hl => ?_) hnd.2
    rcases h with rfl | h
    · obtain ⟨h₁, -⟩ := VExpr.const.inj hl
      exact hnd.1 (h₁ ▸ List.mem_map_of_mem (f := (·.name)) hm)
    · exact hfresh c (.tail _ hm) _ _ h hl

private theorem defEqsConst {ds : List VDecl} {env : VEnv} (H : env.WF' ds) :
    DefEqsConst env := by
  induction H using VEnv.WF'.stageInduction with
  | empty => intro _ _ _ h; cases h
  | inductProjections _ _ _ _ _ _ ihCtors =>
    exact ihCtors.mono addProjections_le (addProjections_defeqs _ _)
  | decl hwf _ ih =>
    cases hwf with
    | «axiom» _ h2 => exact ih.mono (addConst_le h2) (addConst_defeqs h2)
    | «opaque» _ h2 => exact ih.mono (addConst_le h2) (addConst_defeqs h2)
    | «example» _ => exact ih
    | induct _ h2 => exact ih.mono (addInduct_le h2) (addInduct_defeqs h2)
    | «def» _ h2 =>
      obtain ⟨hnone, hsome, -⟩ := addConst_eq h2
      refine (ih.mono (addConst_le h2) (addConst_defeqs h2)).addDefEq
        (by rw [hsome]; nofun) (fun _ _ h hl => ?_) rfl
      rw [addConst_defeqs h2] at h
      exact (ih _ _ _ h hl).1 hnone
    | mutualDef _ h2 _ =>
      have hd := addConsts_defeqs h2
      refine (ih.mono (addConsts_le h2) hd).addDefEqs
        (fun ci hm => by rw [addConsts_constants h2 ci hm]; nofun)
        (fun ci hm _ _ h hl => ?_) (addConst_foldlM_nodup h2)
      rw [hd] at h
      exact (ih _ _ _ h hl).1 (addConst_foldlM_fresh h2 ci hm)
    | quot _ h2 =>
      rw [VEnv.addQuot] at h2
      obtain ⟨e1, s1, h2⟩ := Option.bind_eq_some_iff.1 h2
      obtain ⟨e2, s2, h2⟩ := Option.bind_eq_some_iff.1 h2
      obtain ⟨e3, s3, h2⟩ := Option.bind_eq_some_iff.1 h2
      obtain ⟨e4, s4, h2⟩ := Option.bind_eq_some_iff.1 h2
      cases h2
      refine ((((ih.mono (addConst_le s1) (addConst_defeqs s1)).mono (addConst_le s2)
        (addConst_defeqs s2)).mono (addConst_le s3) (addConst_defeqs s3)).mono
        (addConst_le s4) (addConst_defeqs s4)).addDefEq_app fun _ _ h => ?_
      cases h

/-- A well-formed environment has at most one definitional axiom per constant head: its δ
rules are functional. -/
theorem defeqs_const_uniq {ds : List VDecl} {env : VEnv} (H : env.WF' ds)
    {df df' : VDefEq} (h : env.defeqs df) (h' : env.defeqs df') {c : Name}
    {us us' : List VLevel} (hlhs : df.lhs = .const c us) (hlhs' : df'.lhs = .const c us') :
    df = df' :=
  (defEqsConst H _ _ _ h hlhs).2 _ _ h' hlhs'

end VEnv.WF'

/-! ### Projection and installation bookkeeping -/

theorem VEnv.addConsts_projections {env env' : VEnv} :
    ∀ {cis}, env.addConsts cis = some env' → env'.projections = env.projections
  | [], h => by cases h; rfl
  | _ :: _, h => by
    simp only [VEnv.addConsts, List.foldlM_cons, Option.bind_eq_bind,
      Option.bind_eq_some_iff] at h
    obtain ⟨middle, hfirst, hrest⟩ := h
    exact (VEnv.addConsts_projections hrest).trans (VEnv.addConst_projections hfirst)

@[simp] theorem VEnv.addDefEqs_projections (env : VEnv) (cis : List VDefVal) :
    (env.addDefEqs cis).projections = env.projections := by
  induction cis generalizing env with
  | nil => rfl
  | cons ci cis ih => exact ih (env := env.addDefEq ci.toDefEq)

theorem VEnv.addQuot_projections {env env' : VEnv}
    (H : env.addQuot = some env') : env'.projections = env.projections := by
  simp only [VEnv.addQuot, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.some.injEq] at H
  obtain ⟨a, ha, b, hb, c, hc, d, hd, rfl⟩ := H
  exact (VEnv.addConst_projections hd).trans <|
    (VEnv.addConst_projections hc).trans <|
      (VEnv.addConst_projections hb).trans (VEnv.addConst_projections ha)

namespace VEnv

/-- No lookup can appear except from the old environment or a literal
member of the installed block. -/
theorem addConstVals_lookup_cases {base extended : VEnv}
    (installed : base.addConstVals values = some extended)
    (lookup : extended.constants name = some value) :
    base.constants name = some value ∨
      ∃ entry ∈ values, entry.name = name ∧ entry.toVConstant = value := by
  induction values generalizing base with
  | nil => cases installed; exact Or.inl lookup
  | cons entry entries ih =>
    simp only [VEnv.addConstVals, Option.bind_eq_bind, Option.bind_eq_some_iff] at installed
    obtain ⟨middle, first, rest⟩ := installed
    rcases ih rest with old | added
    · rw [VEnv.addConst_constants_eq first] at old
      dsimp only at old
      by_cases same : entry.name = name
      · simp only [same, ite_true, Option.some.injEq] at old
        exact Or.inr ⟨entry, List.mem_cons_self, same, old⟩
      · exact Or.inl (by simpa only [same, ite_false] using old)
    · obtain ⟨selected, member, sameName, sameValue⟩ := added
      exact Or.inr ⟨selected, List.mem_cons_of_mem _ member, sameName, sameValue⟩

end VEnv

namespace VerifyInductive

theorem VEnv.addConstVals_projections_eq
    {base out : VEnv} {constants : List VConstVal}
    (H : base.addConstVals constants = some out) :
    out.projections = base.projections :=
  VEnv.addConstVals_projections H

end VerifyInductive
