import Lean4Lean.Theory.Typing.Confluence.HeadSeparation
import Lean4Lean.Theory.Typing.RecursorRegistryInstallation
import Lean4Lean.Theory.Typing.RecursorMajorFamily
import Lean4Lean.Theory.Typing.DefinitionPatterns
import Lean4Lean.Theory.Typing.PatsIota

/-! # The head registries of a well-formed environment

The data the confluence engine (`Params`, `Theory/Typing/ChurchRosser.lean`) reads off an
environment: for each name, the metadata of a registered recursor of that name with a
constructor of its owner (`recursorRegistry`), and the stored definition of that name
(`definitionRegistry`). Both are chosen classically among the actual installations; the facts
below make every choice agree with the registered rules:

* every registered ι pattern has a registry entry for its recursor (`WF.pat_recursorEntry`),
  and the entry's major offset is the pattern's (`WF.recursorEntry_majorOffset`): the
  recursor's constant determines it;
* every stored equation is the quotient rule or the δ rule of a registered definition
  (`WF.defeqs_origin`), which is the registry's (`WF.definitionRegistry_of_defeq`).

On the verified-inductives branch these tables were built along the declaration history
(`Confluence/RegistryOfWF.lean` there); with the ι rules registered as patterns
(`VEnv.pats`, provenance `WF'.pats_origin`) they are read off the environment directly. -/

namespace Lean4Lean

theorem VExpr.stripLams_eq_lamBody : ∀ e : VExpr, e.stripLams = e.lamBody
  | .lam _ b => stripLams_eq_lamBody b
  | .bvar _ | .sort _ | .const .. | .app .. | .forallE .. | .proj .. => rfl

theorem VExpr.piArity_wrapForalls (ds : List VExpr) (b : VExpr) :
    (VExpr.wrapForalls ds b).piArity = ds.length + b.piArity := by
  induction ds with
  | nil => simp [VExpr.wrapForalls]
  | cons d ds ih =>
    show (VExpr.forallE d (VExpr.wrapForalls ds b)).piArity = _
    simp only [VExpr.piArity, ih, List.length_cons]; omega

theorem VExpr.piArity_mkApps_bvar (k : Nat) (args : List VExpr) :
    (VExpr.mkApps (.bvar k) args).piArity = 0 := by
  rcases List.eq_nil_or_concat args with rfl | ⟨as, a, rfl⟩
  · rfl
  · rw [List.concat_eq_append, VExpr.mkApps_append]; rfl

end Lean4Lean

namespace Lean4Lean.VEnv
open InductiveSignature

variable {env : VEnv}

/-! ## Recursors -/

/-- A registry entry for the name `name`: the metadata of a registered recursor of that name
whose owner has a constructor (so that it registers ι rules). -/
def RecursorEntry (env : VEnv) (name : Name) (data : RecursorData) : Prop :=
  RecursorRegistered env data ∧ data.name = name ∧
    ∃ index : Fin data.schema.signature.constructors.size,
      data.schema.signature.constructors[index].owner = data.owner

open Classical in
/-- The recursor registry of an environment: some registry entry of each name. -/
noncomputable def recursorRegistry (env : VEnv) (name : Name) : Option RecursorData :=
  if h : ∃ data, RecursorEntry env name data then some (Classical.choose h) else none

theorem recursorRegistry_entry {name : Name} {data : RecursorData}
    (h : env.recursorRegistry name = some data) : RecursorEntry env name data := by
  unfold recursorRegistry at h
  split at h
  · cases h; exact Classical.choose_spec ‹∃ data, RecursorEntry env name data›
  · cases h

theorem recursorRegistry_of_entry {name : Name} {data : RecursorData}
    (h : RecursorEntry env name data) : ∃ data', env.recursorRegistry name = some data' := by
  unfold recursorRegistry
  rw [dif_pos ⟨data, h⟩]
  exact ⟨_, rfl⟩

theorem recursorRegistry_none {name : Name}
    (h : ∀ data, ¬RecursorEntry env name data) : env.recursorRegistry name = none := by
  unfold recursorRegistry
  rw [dif_neg fun ⟨d, hd⟩ => h d hd]

/-- A registered recursor of the environment is a constant whose type has `majorOffset + 1`
binders. -/
theorem RecursorRegistered.constant_piArity {data : RecursorData}
    (H : RecursorRegistered env data) :
    ∃ c, env.constants data.name = some c ∧ c.type.piArity = data.majorOffset + 1 := by
  obtain ⟨type, htype⟩ := H.recursorType_exists
  obtain ⟨domains, _, rfl, hlen, -⟩ := RecursorData.recursorType_shape htype
  refine ⟨_, H.recursorType htype, ?_⟩
  simp [VExpr.piArity_wrapForalls, VExpr.piArity_mkApps_bvar, hlen]

/-- The registered recursor of a compiled declaration whose rule `ru` is installed. -/
theorem WF'.rule_recursorEntry {ds : List VDecl} (_H : env.WF' ds)
    {decl : VInductDecl} {env₀ env₁ : VEnv} (hdecl : decl.WF env₀)
    (hadd : env₀.addInduct decl = some env₁) (hle : env₁ ≤ env)
    {rec : VRecursor} (hrec : rec ∈ decl.recs) {ru : VRecRule} (hru : ru ∈ rec.rules) :
    ∃ data, RecursorEntry env rec.name data := by
  obtain ⟨block, hcomp, hrecs, -⟩ := hdecl.recsCompiled
  obtain ⟨df, hdf, hof⟩ := hrecs.rules rec hrec ru hru
  obtain ⟨base, expanded, s, g, auxiliaries, hbase, hdata, hprior⟩ := hcomp.exists_compilation
  obtain ⟨data, hmem, index, howner, hgen⟩ := hdata.recursorEntries_equation hdf .anonymous
  obtain ⟨owner, -, rfl⟩ := List.mem_map.mp hmem
  have hreg : RecursorRegistered env
      (RecursorData.ofInstance .anonymous (RecursorSchema.ofCompilation decl s auxiliaries) g
        owner) :=
    ⟨base, env₀, decl, expanded, g, auxiliaries, block, env₁, hdata, hprior, hbase, rfl, rfl,
      rfl, rfl, rfl, hdecl, hadd, hrecs, hle⟩
  refine ⟨_, hreg, ?_, index, howner⟩
  have hhead := hreg.equation_head howner hgen
  rw [VExpr.stripLams_eq_lamBody, ← VExpr.getAppFn_eq_fst] at hhead
  have hname := hof.2.1
  rw [VExpr.headConst?_eq_some, hhead] at hname
  obtain ⟨_, h⟩ := hname
  exact (VExpr.const.inj h).1

/-- **Every registered ι pattern has a recursor registry entry.** -/
theorem WF.pat_recursorEntry (henv : env.WF) {recN ctor : Name} {major fields : Nat}
    {r : (SimplePattern.iota recN major ctor fields).toPattern.RHS ×
      (SimplePattern.iota recN major ctor fields).toPattern.Check}
    (hp : env.pats (SimplePattern.iota recN major ctor fields).toPattern r) :
    ∃ data, RecursorEntry env recN data := by
  obtain ⟨ds, H⟩ := henv
  obtain ⟨decl, ds₀, env₀, env₁, -, -, hdecl, hadd, hle, rec, hrec, ru, hru, -, hpe, -⟩ :=
    H.pats_origin hp
  obtain ⟨rfl, -, -, -⟩ := SimplePattern.iota_toPattern_inj hpe
  exact H.rule_recursorEntry hdecl hadd hle hrec hru

/-- **The registry's major offset is the pattern's**: both are read off the recursor's
constant. -/
theorem WF.recursorEntry_majorOffset (henv : env.WF) {recN ctor : Name} {major fields : Nat}
    {r : (SimplePattern.iota recN major ctor fields).toPattern.RHS ×
      (SimplePattern.iota recN major ctor fields).toPattern.Check}
    (hp : env.pats (SimplePattern.iota recN major ctor fields).toPattern r)
    {data : RecursorData} (hentry : RecursorEntry env recN data) :
    data.majorOffset = major := by
  obtain ⟨ds, H⟩ := henv
  obtain ⟨decl, ds₀, env₀, env₁, -, -, hdecl, hadd, hle, rec, hrec, ru, hru, -, hpe, -⟩ :=
    H.pats_origin hp
  obtain ⟨rfl, rfl, -, -⟩ := SimplePattern.iota_toPattern_inj hpe
  obtain ⟨hreg, hname, -⟩ := hentry
  obtain ⟨c, hc, harity⟩ := hreg.constant_piArity
  have hrc := hle.constants (addInduct_rec_find hadd hrec)
  rw [hname, hrc] at hc
  cases Option.some.inj hc
  have hshape := (hdecl.rec_shape rec hrec).1
  change rec.type.piArity = _ at harity
  simp only [VRecursor.getMajorIdx]
  omega

/-- The registry entry of the recursor of a registered ι pattern. -/
theorem WF.pat_recursorRegistry (henv : env.WF) {recN ctor : Name} {major fields : Nat}
    {r : (SimplePattern.iota recN major ctor fields).toPattern.RHS ×
      (SimplePattern.iota recN major ctor fields).toPattern.Check}
    (hp : env.pats (SimplePattern.iota recN major ctor fields).toPattern r) :
    ∃ data, env.recursorRegistry recN = some data ∧ RecursorEntry env recN data ∧
      data.majorOffset = major := by
  obtain ⟨data, hentry⟩ := henv.pat_recursorEntry hp
  obtain ⟨data', hlookup⟩ := recursorRegistry_of_entry hentry
  have hentry' := recursorRegistry_entry hlookup
  exact ⟨data', hlookup, hentry', henv.recursorEntry_majorOffset hp hentry'⟩

/-- Every constructor of a registered recursor's signature has a restored equation. -/
theorem RecursorRegistered.equation_exists' {data : RecursorData}
    (H : RecursorRegistered env data) (index : Fin data.schema.signature.constructors.size) :
    ∃ equation, data.equation index = some equation := by
  obtain ⟨base, installBase, source, expanded, g, auxiliaries, block, installed,
    hdata, _, _, hr, _, hu, hl, ht, -⟩ := H
  have hinstance := RecursorRegistered.recursorInstance_eq hdata hu hl ht
  have hm : g.equation index ∈ g.equations := List.mem_map.mpr ⟨index, List.mem_finRange _, rfl⟩
  obtain ⟨equation, _, he⟩ := Lean4Lean.List.Forall₂.forall_exists_l
    (List.mapM_eq_some.mp hdata.equations) _ hm
  exact ⟨equation, by simpa only [RecursorData.equation, hinstance, hr] using he⟩

/-- A registry entry's recursor heads a registered ι pattern: the generated equation of its
constructor is the rule of one of the recursor's rules (`RecursorRegistered.restoredEquation_pat`). -/
theorem RecursorEntry.pat {name : Name} {data : RecursorData} (H : RecursorEntry env name data) :
    ∃ (p : Pattern) (r : p.RHS × p.Check), env.pats p r ∧ p.headConst = name := by
  obtain ⟨hreg, hname, index, howner⟩ := H
  obtain ⟨equation, hgen⟩ := hreg.equation_exists' index
  obtain ⟨rec, ru, hc, hof, hp⟩ := hreg.restoredEquation_pat index hgen
  refine ⟨_, _, hp, ?_⟩
  rw [SimplePattern.iota_headConst, ← hname]
  have hhead := hreg.equation_head howner hgen
  rw [VExpr.stripLams_eq_lamBody, ← VExpr.getAppFn_eq_fst] at hhead
  have h := hof.2.1
  rw [VExpr.headConst?_eq_some, hhead] at h
  obtain ⟨_, h⟩ := h
  exact (VExpr.const.inj h).1.symm

/-- The head of a registry entry is not rigid. -/
theorem RecursorEntry.not_rigid {name : Name} {data : RecursorData}
    (H : RecursorEntry env name data) : ¬env.Rigid name := fun hr =>
  let ⟨_, _, hp, hh⟩ := H.pat; hr.pats _ _ hp hh

/-! ## Definitions -/

open Classical in
/-- The definition registry of an environment: some registered definition of each name. -/
noncomputable def definitionRegistry (env : VEnv) (name : Name) : Option VDefVal :=
  if h : ∃ value : VDefVal, DefinitionRegistered env value ∧ value.name = name then
    some (Classical.choose h) else none

theorem definitionRegistry_registered {name : Name} {value : VDefVal}
    (h : env.definitionRegistry name = some value) :
    DefinitionRegistered env value ∧ value.name = name := by
  unfold definitionRegistry at h
  split at h
  · cases h
    exact Classical.choose_spec ‹∃ value : VDefVal, DefinitionRegistered env value ∧ value.name = name›
  · cases h

/-- A registered definition's value is closed. -/
theorem DefinitionRegistered.closed (henv : env.WF) {value : VDefVal}
    (H : DefinitionRegistered env value) : value.value.Closed := by
  have hw := (henv.ordered.defEqWF H.2).2
  exact VExpr.WF.closedN henv.ordered ⟨_, hw⟩ (by trivial)

theorem DefinitionRegistered.mono {env' : VEnv} {value : VDefVal}
    (H : DefinitionRegistered env value) (hle : env ≤ env') : DefinitionRegistered env' value :=
  ⟨hle.constants H.1, hle.defeqs H.2⟩

theorem addDefEqs_constants' : ∀ {cis : List VDefVal} {e : VEnv},
    (e.addDefEqs cis).constants = e.constants
  | [], _ => rfl
  | ci :: cis, e => (addDefEqs_constants' (cis := cis) (e := e.addDefEq ci.toDefEq) :)

/-- **Every stored equation is the quotient rule or the δ rule of a registered definition.** -/
theorem WF'.defeqs_origin {ds : List VDecl} (H : env.WF' ds) {df : VDefEq}
    (hdf : env.defeqs df) :
    df = quotDefEq ∨ ∃ value, DefinitionRegistered env value ∧ df = value.toDefEq := by
  induction H generalizing df with
  | empty => cases hdf
  | inductProjections _ _ _ _ _ _ _ _ _ _ _ _ _ _ ihCtors =>
    rcases ihCtors (by simpa using hdf) with h | ⟨value, hv, h⟩
    · exact .inl h
    · exact .inr ⟨value, hv.mono addProjections_le, h⟩
  | @decl d env' ds env hd H ih =>
    have old : env.defeqs df → env ≤ env' →
        df = quotDefEq ∨ ∃ value, DefinitionRegistered env' value ∧ df = value.toDefEq :=
      fun h hle => (ih h).imp id fun ⟨value, hv, h⟩ => ⟨value, hv.mono hle, h⟩
    cases hd with
    | «axiom» _ h2 | «opaque» _ h2 =>
      rw [addConst_defeqs h2] at hdf; exact old hdf (addConst_le h2)
    | «example» _ => exact ih hdf
    | @«def» _ _ ci _ h2 =>
      rcases hdf with rfl | hdf
      · exact .inr ⟨ci, ⟨(addConst_self h2 : _), .inl rfl⟩, rfl⟩
      · rw [addConst_defeqs h2] at hdf
        exact old hdf ((addConst_le h2).trans addDefEq_le)
    | mutualDef _ h2 _ =>
      have hdf' := hdf
      rw [addDefEqs_eq_addDefEqRules, addDefEqRules_defeqs_iff_mem_or] at hdf'
      rcases hdf' with hm | hdf'
      · obtain ⟨ci, hci, rfl⟩ := List.mem_map.1 hm
        refine .inr ⟨ci, ⟨?_, hdf⟩, rfl⟩
        rw [addDefEqs_constants']
        exact addConsts_constants h2 ci hci
      · rw [addConsts_defeqs h2] at hdf'; exact old hdf' ((addConsts_le h2).trans addDefEqs_le)
    | quot h1 h2 =>
      obtain ⟨e1, e2, e3, e4, -, a1, -, a2, -, a3, -, a4, -, rfl⟩ := addQuot_chain h1 h2
      rcases hdf with rfl | hdf
      · exact .inl rfl
      · rw [addConst_defeqs a4, addConst_defeqs a3, addConst_defeqs a2,
          addConst_defeqs a1] at hdf
        exact old hdf ((addConst_le a1).trans ((addConst_le a2).trans ((addConst_le a3).trans
          ((addConst_le a4).trans addDefEq_le))))
    | induct _ h2 => rw [addInduct_defeqs h2] at hdf; exact old hdf (addInduct_le h2)

/-- The registry's definition of the head of a stored δ rule is that rule's definition. -/
theorem WF.definitionRegistry_of_defeq (henv : env.WF) {value : VDefVal}
    (hv : DefinitionRegistered env value) :
    env.definitionRegistry value.name = some value := by
  have hex : ∃ v : VDefVal, DefinitionRegistered env v ∧ v.name = value.name := ⟨value, hv, rfl⟩
  unfold definitionRegistry
  rw [dif_pos hex]
  congr 1
  obtain ⟨hv', hn⟩ := Classical.choose_spec hex
  generalize Classical.choose hex = v at hv' hn ⊢
  obtain ⟨ds, H⟩ := henv
  have heq := H.defeqs_const_uniq hv'.2 hv.2 (c := value.name)
    (us := VLevel.params v.uvars) (us' := VLevel.params value.uvars)
    (by simp [VDefVal.toDefEq, hn]) (by simp [VDefVal.toDefEq])
  rcases v with ⟨⟨⟨u1, t1⟩, n1⟩, v1⟩
  rcases value with ⟨⟨⟨u2, t2⟩, n2⟩, v2⟩
  simp only [VDefVal.toDefEq, VDefEq.mk.injEq] at heq hn
  obtain ⟨rfl, -, rfl, rfl⟩ := heq
  subst hn
  rfl

end Lean4Lean.VEnv
