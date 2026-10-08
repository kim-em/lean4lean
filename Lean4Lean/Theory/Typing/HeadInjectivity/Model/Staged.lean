import Lean4Lean.Theory.Typing.HeadInjectivity.Model.Extract
import Lean4Lean.Theory.Typing.HeadInjectivity.Model.ElimRule

/-! # Staged soundness (decision D11) and stages B and D

`VEnv.WF'.ruleValid`: in a well-formed environment `envF` without projections or eliminators,
every rule of every environment in the declaration history of `envF` is
valid in the model of `envF`. The proof is by induction on the history; the semantic fact
needed by a native rule of a data family (`FamSort`: the family's type observations end in its
recorded result sort) comes from the soundness, in the model of `envF`, of the definitional
equality between the family's declared type and a telescope ending in that sort, a derivation
of the environment before the rules of the family were installed, whose rules are valid by
the induction hypothesis.

`VEnv.WF.headInjectivityCore_of_projElimFree`: chain-level head injectivity under that scope.

The proof-field fact needed by singleton eliminators (mode C) comes the same way from the
soundness of the field typings recorded by `SingletonElimination`, placed in the equation's
telescope (`Model/Singleton.lean`). Uniqueness of a native rule per head comes from
`HeadsClosed`: along the history, no later declaration adds a rule headed by an existing
constant, so the rules headed by a recursor are exactly its block's equations. Restored
equations of nested compilations take `FamSort` of an original family from the block's own
correspondence and of a container family from the container's compilation
(`Model/NestedRule.lean`). -/

namespace Lean4Lean
namespace VEnv
open InductiveSignature
open private addDefEqs_as_rules addConsts_as_values defeqs_addRules
  from Lean4Lean.Theory.Typing.NativeConstructorRigidity

/-- **The semantic sort of an original family** (D11): its type observations end in its
recorded result sort, in the model of any later environment `envF` in which the rules of the
environment `env0` before the family are valid. -/
theorem Model.famSort_source {envF env0 installed base envTypes : VEnv} {source : VInductDecl}
    {block : VInductBlock} {r : Restoration} {u0 : Nat} {nf family : VInductiveType}
    (henvF : envF.Ordered) (h0 : env0.Ordered)
    (hnp : ∀ n p, ¬ envF.projections n p) (hEV : Model.ElimsValid envF env0)
    (hvalid : ∀ df, env0.defeqs df → Model.RuleValid envF df)
    (hwf : ∀ t ∈ source.types, t.toVConstant.WF base) (hb : base ≤ env0)
    (htypes : base.addConstVals source.typeConstants = some envTypes)
    (hbt : block.types = source.typeConstants)
    (hinst : block.install env0 = some installed) (hle : installed ≤ envF)
    (hfamily : family ∈ source.types) (hrel : RestoresFamily r envTypes u0 nf family) :
    Model.FamSort envF family.name nf.resultLevel := by
  obtain ⟨domains, body, level, exprType, hlev, h1, h2⟩ := hrel.type
  obtain ⟨types', ht, hti⟩ := install_parts hinst
  rw [hbt] at ht
  have hE : types'.Ordered := h0.addConstVals (fun ci hci => by
    obtain ⟨t, htm, rfl⟩ := List.mem_map.1 hci
    exact (hwf t htm).mono hb) ht
  have hTE : envTypes ≤ types' := addConstVals_mono hb htypes ht
  have hEF : types' ≤ envF := hti.trans hle
  have hfc : envF.constants family.name = some family.toVConstant :=
    hEF.constants (addConstVals_get ht (List.mem_map_of_mem hfamily))
  refine Model.famSort_of henvF hE hEF ?_ hnp
    (hEV.of_elims fun b s h => by rwa [VEnv.addConstVals_eliminators ht] at h) hfc
    (h1.mono hTE) (h2.mono hTE) hlev
  rw [VEnv.addConstVals_defeqs ht]; exact hvalid

/-- `FamSort` for every family of an ordinary compilation. -/
theorem Model.famSort {envF env0 installed base : VEnv} {source expanded : VInductDecl}
    {s : InductiveSignature} {g : Instance s} {block : VInductBlock}
    (henvF : envF.Ordered) (h0 : env0.Ordered)
    (hnp : ∀ n p, ¬ envF.projections n p) (hEV : Model.ElimsValid envF env0)
    (hvalid : ∀ df, env0.defeqs df → Model.RuleValid envF df)
    (C : CompilationData base source expanded s g [] block) (hb : base ≤ env0)
    (hinst : block.install env0 = some installed) (hle : installed ≤ envF)
    (o : Fin s.families.size) : Model.FamSort envF s.families[o].name s.families[o].resultLevel := by
  obtain ⟨envTypes, direct, htypes, hdirect, -, hfamilies⟩ := C.correspondence
  have hd : direct = [] := by simpa using hdirect.symm
  subst hd
  obtain ⟨family, hfamily, hrel⟩ := Lean4Lean.List.Forall₂.forall_exists_l
    hfamilies _ (s.declarationFamily_mem o)
  rw [List.append_nil] at hfamily
  obtain ⟨-, -, -, -, _, _, _, _, hwf, _⟩ := C.sourceWF
  have hn : s.families[o].name = family.name := hrel.name
  rw [hn]
  exact Model.famSort_source henvF h0 hnp hEV hvalid hwf hb htypes C.types hinst hle hfamily hrel

/-- The rules of `envF` whose head constant is a constant of `env` are rules of `env`: no later
declaration adds a rule headed by an existing constant. -/
def HeadsClosed (envF env : VEnv) : Prop :=
  ∀ df, envF.defeqs df → ∀ n ls, df.lhs.stripLams.getAppFnArgs.1 = .const n ls →
    (∃ ci, env.constants n = some ci) → env.defeqs df

theorem HeadsClosed.down {envF env0 env' : VEnv} {new : List VDefEq} (H : HeadsClosed envF env')
    (hle : env0 ≤ env') (hdefeqs : ∀ df, env'.defeqs df → df ∈ new ∨ env0.defeqs df)
    (hfresh : ∀ df ∈ new, ∀ n ls, df.lhs.stripLams.getAppFnArgs.1 = .const n ls →
      env0.constants n = none) : HeadsClosed envF env0 := by
  intro df hdf n ls h ⟨ci, hci⟩
  rcases hdefeqs df (H df hdf n ls h ⟨ci, hle.constants hci⟩) with hm | ho
  · rw [hfresh df hm n ls h] at hci; cases hci
  · exact ho

theorem HeadsClosed.excl {envF env0 env' : VEnv} {new : List VDefEq} {n : Name}
    (H : HeadsClosed envF env') (hord0 : env0.Ordered)
    (hdefeqs : ∀ df, env'.defeqs df → df ∈ new ∨ env0.defeqs df)
    (hn : ∃ ci, env'.constants n = some ci) (hfresh : env0.constants n = none) :
    Model.HeadExcl envF n new := fun df' hdf' ls' h' => by
  rcases hdefeqs df' (H df' hdf' n ls' h' hn) with hm | ho
  · exact hm
  · obtain ⟨_, hc⟩ := (hord0.defEqWF ho).1.head_const_lookup hord0 (Γ := []) ⟨⟩ h'
    rw [hfresh] at hc; cases hc

private theorem definitions_le' (env : VEnv) (cis : List VDefVal) :
    env ≤ env.addDefEqs cis := by
  induction cis generalizing env with
  | nil => exact .rfl
  | cons ci cis ih => exact VEnv.addDefEq_le.trans (ih _)

private theorem declaration_le' (H : VDecl.WF env decl env') : env ≤ env' := by
  cases H with
  | «axiom» _ h | «opaque» _ h => exact VEnv.addConst_le h
  | «def» _ h => exact (VEnv.addConst_le h).trans VEnv.addDefEq_le
  | «example» => exact .rfl
  | mutualDef _ h _ => exact (VEnv.addConsts_le h).trans (definitions_le' ..)
  | quot _ h =>
    simp only [VEnv.addQuot, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.some.injEq] at h
    obtain ⟨a, ha, b, hb, c, hc, d, hd, rfl⟩ := h
    exact (VEnv.addConst_le ha).trans <| (VEnv.addConst_le hb).trans <|
      (VEnv.addConst_le hc).trans <| (VEnv.addConst_le hd).trans VEnv.addDefEq_le
  | induct _ h =>
    cases h with
    | intro _ _ _ h =>
      simp only [VInductBlock.install, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at h
      obtain ⟨types, ht, ctors, hc, recs, hr, rfl⟩ := h
      exact (VEnv.addConstVals_le ht).trans <| (VEnv.addConstVals_le hc).trans <|
        VEnv.addProjections_le.trans <| (VEnv.addConstVals_le hr).trans VEnv.addDefEqRules_le

theorem HeadsClosed.of_decl {envF env0 env' : VEnv} (hdecl : VDecl.WF env0 d env')
    (hcl : HeadsClosed envF env') : HeadsClosed envF env0 := by
  have h0le := declaration_le' hdecl
  cases hdecl with
  | «axiom» _ hadd | «opaque» _ hadd =>
    exact hcl.down (new := []) h0le
      (fun df h => .inr (by rwa [VEnv.addConst_defeqs hadd] at h)) nofun
  | «example» => exact hcl
  | @«def» env₁ _ ci _ hadd =>
    have hnone : env0.constants ci.name = none := by
      unfold VEnv.addConst at hadd; split at hadd <;> cases hadd; assumption
    exact hcl.down (new := [ci.toDefEq]) h0le
      (fun df h => by rwa [defeqs_addDefEq, VEnv.addConst_defeqs hadd] at h)
      (fun df hm n ls h => by
        simp only [List.mem_singleton] at hm; subst hm; cases h; exact hnone)
  | mutualDef _ hadd _ =>
    rw [addConsts_as_values] at hadd
    exact hcl.down (new := _) h0le
      (fun df h => by
        rw [addDefEqs_as_rules, defeqs_addRules, VEnv.addConstVals_defeqs hadd] at h; exact h)
      (fun df hm n ls h => by
        obtain ⟨ci, hci, rfl⟩ := List.mem_map.mp hm
        cases h
        exact addConstVals_names_fresh hadd ci.toVConstVal (List.mem_map_of_mem hci))
  | quot _ installed =>
    simp only [VEnv.addQuot, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.some.injEq] at installed
    obtain ⟨a, ha, b, hb, c, hc, e, he, rfl⟩ := installed
    have hnone : env0.constants ``Quot.lift = none := by
      have hb' : b.constants ``Quot.lift = none := by
        unfold VEnv.addConst at hc; split at hc <;> cases hc; assumption
      cases h' : env0.constants ``Quot.lift with
      | none => rfl
      | some ci =>
        have := (VEnv.addConst_le hb).constants <| (VEnv.addConst_le ha).constants h'
        rw [this] at hb'; cases hb'
    exact hcl.down h0le (new := [quotDefEq]) (fun df h => by
        rwa [defeqs_addDefEq, VEnv.addConst_defeqs he, VEnv.addConst_defeqs hc,
          VEnv.addConst_defeqs hb, VEnv.addConst_defeqs ha] at h) (fun df hm n ls h => by
      simp only [List.mem_singleton] at hm; subst hm
      have hn : n = ``Quot.lift := by cases h; rfl
      subst hn; exact hnone)
  | induct _ installed =>
    cases installed with
    | @intro block _ _ compiled _ hinst =>
      have howned := compiled.compiled.equation_head_owned
      simp only [VInductBlock.install, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at hinst
      obtain ⟨types, ht, ctors, hc, recursors, hr, rfl⟩ := hinst
      refine hcl.down h0le (new := block.rules) (fun df h => by
        rwa [defeqs_addRules, VEnv.addConstVals_defeqs hr, VEnv.addProjections_defeqs,
          VEnv.addConstVals_defeqs hc, VEnv.addConstVals_defeqs ht] at h) fun df hm n ls h => ?_
      obtain ⟨recursor, hrec, ls', hhead⟩ := howned df hm
      have hn : recursor.name = n := (VExpr.const.inj (hhead.symm.trans h)).1
      subst hn
      have hfresh := addConstVals_names_fresh hr recursor hrec
      cases h' : env0.constants recursor.name with
      | none => rfl
      | some ci =>
        have := (addConstVals_le hc).constants ((addConstVals_le ht).constants h')
        simp only [VEnv.addProjections_constants] at hfresh
        rw [this] at hfresh; cases hfresh

/-- A family's derivations in the environment of its headers, placed in a later environment that
contains the headers. -/
theorem addConstVals_le_of : ∀ {cis : List VConstVal} {base E1 env : VEnv},
    base.addConstVals cis = some E1 → base ≤ env →
    (∀ ci ∈ cis, env.constants ci.name = some ci.toVConstant) → E1 ≤ env
  | [], base, E1, env, h, hle, _ => by
    simp [VEnv.addConstVals] at h; subst h; exact hle
  | ci :: cis, base, E1, env, h, hle, hc => by
    cases hadd : base.addConst ci.name ci.toVConstant with
    | none => simp [VEnv.addConstVals, hadd] at h
    | some b1 =>
      simp [VEnv.addConstVals, hadd] at h
      refine addConstVals_le_of h ?_ fun c hc' => hc c (List.mem_cons_of_mem _ hc')
      unfold VEnv.addConst at hadd; split at hadd <;> cases hadd
      refine ⟨fun {n a} hn => ?_, hle.defeqs, hle.projections, hle.eliminators⟩
      simp only at hn
      split at hn
      · rename_i e; subst e; cases hn; exact hc ci List.mem_cons_self
      · exact hle.constants hn

/-- **Staged validity** (D11): every rule of every environment in the declaration history of a
well-formed `envF` in scope is valid in the model of `envF`. -/
theorem WF'.ruleValid {envF : VEnv} (hF : envF.WF) (hnp : ∀ n p, ¬ envF.projections n p) :
    ∀ {ds env}, env.WF' ds → env ≤ envF → HeadsClosed envF env →
      (∀ df, env.defeqs df → Model.RuleValid envF df) ∧
      ∀ b (schema : CaseSchema) owner rules df, env.eliminators b schema →
        schema.genericEquations b owner = some rules → df ∈ rules → Model.ElimValid envF owner df := by
  have henvF := hF.ordered
  have hEu : ∀ b s s', envF.eliminators b s → envF.eliminators b s' → s = s' :=
    fun _ _ _ h1 h2 => hF.eliminators_unique h1 h2
  have hdr := hF.defRules
  have hctor : ∀ c, Model.IsCtor envF c → envF.Rigid c := by
    rintro _ (⟨_, hdf, hm⟩ | ⟨_, _, _, _, hb, hgen, rfl⟩)
    · exact VEnv.nativeHeadRigid_iff.1 (hF.native_constructor_rigid hdf hm)
    · exact VEnv.nativeHeadRigid_iff.1 (hF.case_constructor_rigid hb hgen)
  have hcres : ∀ c, Model.IsNativeCtor envF c → envF.CtorResultRigid c :=
    fun _ ⟨_, hdf, hm⟩ => hF.native_constructor_result_rigid hdf hm
  have hpctor : ∀ c, Model.IsProjCtor envF c → envF.Rigid c :=
    fun _ ⟨_, _, h, _⟩ => absurd h (hnp _ _)
  intro ds env H
  induction H with
  | empty => intro _ _; exact ⟨fun df h => (by cases h), fun _ _ _ _ _ h => (by cases h)⟩
  | @decl d env' ds env0 hdecl hbase ih =>
    intro hle hcl
    have h0le := declaration_le' hdecl
    have IH := ih (h0le.trans hle) (HeadsClosed.of_decl hdecl hcl)
    have helim := VDecl.WF.eliminators hdecl
    refine ⟨fun df hdf => ?_, fun b schema owner rules df hb hr hm =>
      IH.2 b schema owner rules df (by rw [helim] at hb; exact hb) hr hm⟩
    have h0 : env0.Ordered := (show env0.WF from ⟨ds, hbase⟩).ordered
    have hEV0 : Model.ElimsValid envF env0 := ⟨hEu, IH.2⟩
    have ih' : HeadsClosed envF env0 → ∀ df, env0.defeqs df → Model.RuleValid envF df :=
      fun _ => IH.1
    have hdfF := hle.defeqs hdf
    cases hdecl with
    | «axiom» _ hadd | «opaque» _ hadd =>
      have hcl0 := hcl.down (new := []) h0le
        (fun df h => .inr (by rwa [VEnv.addConst_defeqs hadd] at h)) nofun
      exact @ih' hcl0 df (by rwa [VEnv.addConst_defeqs hadd] at hdf)
    | «example» => exact @ih' hcl df hdf
    | @«def» env₁ _ ci _ hadd =>
      have hnone : env0.constants ci.name = none := by
        unfold VEnv.addConst at hadd; split at hadd <;> cases hadd; assumption
      have hcl0 := hcl.down (new := [ci.toDefEq]) h0le
        (fun df h => by rwa [defeqs_addDefEq, VEnv.addConst_defeqs hadd] at h)
        (fun df hm n ls h => by
          simp only [List.mem_singleton] at hm; subst hm; cases h; exact hnone)
      rcases hdf with rfl | hdf
      · exact Model.RuleValid.delta henvF hdr hctor hpctor hdfF rfl
      · exact @ih' hcl0 df (by rwa [VEnv.addConst_defeqs hadd] at hdf)
    | mutualDef _ hadd _ =>
      rw [addConsts_as_values] at hadd
      have hcl0 := hcl.down (new := _) h0le
        (fun df h => by
          rw [addDefEqs_as_rules, defeqs_addRules, VEnv.addConstVals_defeqs hadd] at h; exact h)
        (fun df hm n ls h => by
          obtain ⟨ci, hci, rfl⟩ := List.mem_map.mp hm
          cases h
          exact addConstVals_names_fresh hadd ci.toVConstVal (List.mem_map_of_mem hci))
      rw [addDefEqs_as_rules, defeqs_addRules] at hdf
      rcases hdf with member | hdf
      · obtain ⟨ci, _, rfl⟩ := List.mem_map.mp member
        exact Model.RuleValid.delta henvF hdr hctor hpctor hdfF rfl
      · exact @ih' hcl0 df (by rwa [VEnv.addConstVals_defeqs hadd] at hdf)
    | quot _ installed =>
      simp only [VEnv.addQuot, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.some.injEq] at installed
      obtain ⟨a, ha, b, hb, c, hc, e, he, rfl⟩ := installed
      have hnone : env0.constants ``Quot.lift = none := by
        have hb' : b.constants ``Quot.lift = none := by
          unfold VEnv.addConst at hc; split at hc <;> cases hc; assumption
        cases h' : env0.constants ``Quot.lift with
        | none => rfl
        | some ci =>
          have := (VEnv.addConst_le hb).constants <| (VEnv.addConst_le ha).constants h'
          rw [this] at hb'; cases hb'
      have hdefeqs : ∀ df, (e.addDefEq quotDefEq).defeqs df → df ∈ [quotDefEq] ∨ env0.defeqs df :=
        fun df h => by
          rwa [defeqs_addDefEq, VEnv.addConst_defeqs he, VEnv.addConst_defeqs hc,
            VEnv.addConst_defeqs hb, VEnv.addConst_defeqs ha] at h
      have hcl0 := hcl.down h0le hdefeqs (fun df hm n ls h => by
        simp only [List.mem_singleton] at hm; subst hm
        have hn : n = ``Quot.lift := by cases h; rfl
        subst hn; exact hnone)
      have hle' : e.addDefEq quotDefEq ≤ envF := hle
      have hlift : (e.addDefEq quotDefEq).constants ``Quot.lift = some quotLiftConst :=
        VEnv.addDefEq_le.constants ((VEnv.addConst_le he).constants (VEnv.addConst_self hc))
      rcases (hdefeqs df hdf) with hm | hdf
      · simp only [List.mem_singleton] at hm; subst hm
        have hq : Model.QuotConsts envF := by
          refine ⟨?_, ?_, hle'.constants hlift⟩
          · exact hle'.constants (VEnv.addDefEq_le.constants ((VEnv.addConst_le he).constants
              ((VEnv.addConst_le hc).constants ((VEnv.addConst_le hb).constants
                (VEnv.addConst_self ha)))))
          · exact hle'.constants (VEnv.addDefEq_le.constants ((VEnv.addConst_le he).constants
              ((VEnv.addConst_le hc).constants (VEnv.addConst_self hb))))
        have hex := hcl.excl h0 hdefeqs ⟨_, hlift⟩ hnone
        exact Model.RuleValid.quot henvF hq (fun df' ls' hdf' h' => List.mem_singleton.1
          (hex df' hdf' ls' h')) hdr hctor hcres hpctor (hnp _)
          (fun ⟨_, _, h, _⟩ => hnp _ _ h) hdfF
      · exact @ih' hcl0 df hdf
    | induct _ installed =>
      cases installed with
      | @intro block _ _ compiled hbwf hinst =>
        obtain ⟨base, expanded, s, g, aux, hbase', C, hprior⟩ :=
          compiled.compiled.compilationOrigin
        have howned := compiled.compiled.equation_head_owned
        have hinst' := hinst
        simp only [VInductBlock.install, Option.bind_eq_bind, Option.bind_eq_some_iff,
          Option.pure_def, Option.some.injEq] at hinst'
        obtain ⟨types, ht, ctors, hc, recursors, hr, rfl⟩ := hinst'
        have hdefeqs : ∀ df, (recursors.addDefEqRules block.rules).defeqs df →
            df ∈ block.rules ∨ env0.defeqs df := fun df h => by
          rwa [defeqs_addRules, VEnv.addConstVals_defeqs hr, VEnv.addProjections_defeqs,
            VEnv.addConstVals_defeqs hc, VEnv.addConstVals_defeqs ht] at h
        have hrecFresh : ∀ recursor ∈ block.recursors, env0.constants recursor.name = none :=
          fun recursor hrec => by
            have hfresh := addConstVals_names_fresh hr recursor hrec
            cases h' : env0.constants recursor.name with
            | none => rfl
            | some ci =>
              have := (addConstVals_le hc).constants ((addConstVals_le ht).constants h')
              simp only [VEnv.addProjections_constants] at hfresh
              rw [this] at hfresh; cases hfresh
        have hcl0 := hcl.down h0le hdefeqs (fun df hm n ls h => by
          obtain ⟨recursor, hrec, ls', hhead⟩ := howned df hm
          have hn : recursor.name = n := (VExpr.const.inj (hhead.symm.trans h)).1
          subst hn; exact hrecFresh recursor hrec)
        rcases hdefeqs df hdf with member | hdf
        rcases (Classical.em (aux = [])).symm with haux | haux
        · -- nested compilations
          obtain ⟨src, hsrc, hres⟩ := Lean4Lean.List.Forall₂.forall_exists_r
            (List.mapM_eq_some.mp C.equations) _ member
          obtain ⟨index, -, rfl⟩ := List.mem_map.1 hsrc
          obtain ⟨rec', hrec', hn, -⟩ := C.restored_recursor s.constructors[index].owner
          have hc1 := VInductBlock.install_recursor_lookup hinst hrec'
          have hc2 := hrecFresh _ hrec'
          rw [hn] at hc1 hc2
          have hex := hcl.excl h0 hdefeqs ⟨_, hc1⟩ hc2
          have hbF : base ≤ envF := hbase'.trans (h0le.trans hle)
          have hmemF : s.families[s.constructors[index].owner] ∈ s.families.toList :=
            Array.mem_toList_iff.2 (Array.getElem_mem s.constructors[index].owner.isLt)
          rcases C.family_origin s.constructors[index].owner with
            ⟨envTypes, family, htypes, hfamily, hrel, hhn, hhl⟩ | ⟨a, ha, hhn, hhl, hlev⟩
          · obtain ⟨-, -, -, -, _, _, _, _, hwf, _⟩ := C.sourceWF
            have hfs := Model.famSort_source henvF h0 hnp hEV0 (@ih' hcl0) hwf hbase' htypes C.types
              hinst hle hfamily hrel
            exact Model.RuleValid.nested henvF hdr hctor hcres hpctor C hprior haux hbF hinst hle index hres
              hdfF (hnp _) (fun ⟨_, _, h, _⟩ => hnp _ _ h) hex (L := s.families[s.constructors[index].owner].resultLevel)
              (by rw [hhn]; exact hfs) (fun hnz => by rw [hhl]; exact hnz _ hmemF)
          · have hfs := Model.famSort_container henvF h0 (h0le.trans hle) hnp hEV0 (@ih' hcl0)
              hprior hbase' ha
            exact Model.RuleValid.nested henvF hdr hctor hcres hpctor C hprior haux hbF hinst hle index hres
              hdfF (hnp _) (fun ⟨_, _, h, _⟩ => hnp _ _ h) hex (L := a.source.resultLevel) (by rw [hhn]; exact hfs)
              (fun hnz => by
                rw [hhl, ← VLevel.inst_inst]
                exact (hnz _ hmemF).of_equiv (VLevel.inst_congr_l hlev))
        · subst haux
          rw [C.ordinary_rules] at member
          obtain ⟨index, -, rfl⟩ := List.mem_map.1 member
          have hrec : g.recursor s.constructors[index].owner ∈ block.recursors := by
            rw [C.ordinary_recursors]; exact List.mem_map.2 ⟨_, List.mem_finRange _, rfl⟩
          have hex := hcl.excl h0 hdefeqs
            ⟨_, VInductBlock.install_recursor_lookup hinst hrec⟩ (hrecFresh _ hrec)
          -- the environment in which the rules are typed
          obtain ⟨tE, cE, rE, htE, hcE, hrE, htwf, hcwf, hrwf, hdfwf⟩ := hbwf
          cases ht.symm.trans htE
          cases hc.symm.trans hcE
          have hproj : block.projections = [] := by
            cases hp : block.projections with
            | nil => rfl
            | cons p ps =>
              exfalso
              refine hnp p.typeName p.info (hle.projections ?_)
              refine VEnv.addDefEqRules_le.projections ((VEnv.addConstVals_le hr).projections ?_)
              rw [hp]
              exact VEnv.addProjections_iff.2 (.inl ⟨p, List.mem_cons_self, rfl, rfl⟩)
          rw [hproj] at hr hrE hrwf
          cases hr.symm.trans hrE
          have hER : recursors.Ordered :=
            ((h0.addConstVals htwf ht).addConstVals hcwf hc).addConstVals hrwf hr
          have hERF : recursors ≤ envF := VEnv.addDefEqRules_le.trans hle
          have hvalidR : ∀ df, recursors.defeqs df → Model.RuleValid envF df := fun df h => by
            rw [VEnv.addConstVals_defeqs hr, VEnv.addProjections_defeqs,
              VEnv.addConstVals_defeqs hc, VEnv.addConstVals_defeqs ht] at h
            exact @ih' hcl0 df h
          have hmem : g.equation index ∈ block.rules := by
            rw [C.ordinary_rules]; exact List.mem_map.2 ⟨_, List.mem_finRange _, rfl⟩
          have hdoms : OnCtx (g.eqDoms index).reverse (recursors.IsType g.uvars) := by
            have hty := IsDefEq.isType hER (show OnCtx [] (recursors.IsType g.uvars) from trivial)
              (hdfwf _ hmem).1
            rw [g.equation_type_eq] at hty
            simpa using onCtx_wrapForalls hER (show OnCtx [] (recursors.IsType g.uvars) from trivial)
              hty
          exact Model.RuleValid.native henvF hdr hctor hcres hpctor C hinst hle index hdfF (hnp _)
            (fun ⟨_, _, h, _⟩ => hnp _ _ h) hex
            (Model.famSort henvF h0 hnp hEV0 (@ih' hcl0) C hbase' hinst hle _)
            (fun envE hE hsing U Δ Γ ls hΔ hlw _ i hi hidx => by
              have hEE : envE ≤ recursors := by
                rw [C.ordinary_expanded_types, ← C.types] at hE
                exact (addConstVals_mono hbase' hE ht).trans
                  ((VEnv.addConstVals_le hc).trans (VEnv.addConstVals_le hr))
              exact Model.proofBinder_of henvF hER hERF hvalidR
                (fun n p h => hnp n p (hERF.projections h))
                (hEV0.of_elims fun b s h => by
                  rwa [VEnv.addConstVals_eliminators hr, VEnv.addProjections_eliminators,
                    VEnv.addConstVals_eliminators hc, VEnv.addConstVals_eliminators ht] at h) hdoms
                (singleton_field_typing hER hEE hsing index hi hidx) hΔ hlw)
        · exact @ih' hcl0 df hdf
  | @inductEliminators _ _ key base env source block schema _ hW hble hcert _ hcond _ hsc _ ih =>
    intro hle hcl
    have hle0 : env ≤ envF :=
      (show env ≤ env.addEliminator key schema from ⟨id, id, id, fun h => .inr h⟩).trans hle
    have IH := ih hle0 (fun df h n ls hh hc => hcl df h n ls hh hc)
    have h0 : env.Ordered := (show env.WF from ⟨_, hW⟩).ordered
    refine ⟨fun df hdf => IH.1 df hdf, fun b schema' owner rules df hb hr hm => ?_⟩
    rcases hb with ⟨rfl, rfl⟩ | hb
    rotate_left
    · exact IH.2 _ _ _ _ _ hb hr hm
    have hbF : envF.eliminators b schema' := hle.eliminators (.inl ⟨rfl, rfl⟩)
    have hctorsIn : ∀ value ∈ block.ctors, envF.constants value.name = some value.toVConstant :=
      fun v hv => hle0.constants (hcond.1 v (List.mem_append_right _ hv))
    have hbase : base ≤ envF := hble.trans hle0
    obtain ⟨rule, hgen, -⟩ := CaseSchema.generates_of_genericEquation hr hm
    have hIrig := hF.case_family_head_rigid hbF hgen
    have hcert' := hcert
    obtain ⟨expanded, g0, aux, C, hprior, hrr, -⟩ := hcert'
    have hEV : Model.ElimsValid envF env := ⟨hEu, IH.2⟩
    rcases C.family_origin owner with
      ⟨envTypes, family, htypes, hfamily, hrel, hhn, hhl⟩ | ⟨a, ha, hhn, hhl, hlev⟩
    · obtain ⟨domains, body, level, exprType, hlev, h1, h2⟩ := hrel.type
      have hTE : envTypes ≤ env := addConstVals_le_of htypes hble fun v hv =>
        hcond.1 v (List.mem_append_left _ (by rw [C.types]; exact hv))
      have hfc : envF.constants family.name = some family.toVConstant :=
        hle0.constants (hcond.1 _ (List.mem_append_left _ (by
          rw [C.types]; exact List.mem_map_of_mem hfamily)))
      have hfs := Model.famSort_of henvF h0 hle0 IH.1 hnp hEV hfc (h1.mono hTE) (h2.mono hTE) hlev
      rw [← hhn, ← hrr] at hfs
      refine Model.ElimValid.of_certified henvF hEu hctor hnp hcert hbF hr hm hctorsIn hbase hIrig hfs
        fun levels target hlen hnz => ?_
      rw [hrr, hhl, VLevel.inst_inst, CaseSchema.genericLevels_inst' hlen]
      exact hnz
    · have hfs := Model.famSort_container henvF h0 hle0 hnp hEV IH.1 hprior hble ha
      rw [← hhn, ← hrr] at hfs
      refine Model.ElimValid.of_certified henvF hEu hctor hnp hcert hbF hr hm hctorsIn hbase hIrig hfs
        fun levels target hlen hnz => ?_
      rw [hrr, hhl, VLevel.inst_inst, List.map_map]
      have e : (VLevel.inst (target :: levels) ∘ VLevel.inst schema'.genericLevels) =
          VLevel.inst levels := by
        funext x
        simp only [Function.comp_apply, VLevel.inst_inst, CaseSchema.genericLevels_inst' hlen]
      rw [e, ← VLevel.inst_inst]
      exact hnz.of_equiv (VLevel.inst_congr_l hlev)
  | inductProjections _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih =>
    intro hle hcl
    have IH := ih (VEnv.addProjections_le.trans hle) (fun df' h n ls h' ⟨ci, hci⟩ => by
      have := hcl df' h n ls h' ⟨ci, by simpa using hci⟩; simpa using this)
    exact ⟨fun df hdf => IH.1 df (by simpa using hdf),
      fun b schema owner rules df hb hr hm => IH.2 b schema owner rules df (by simpa using hb) hr hm⟩

/-- The scope of stages B, D and E: no projections. Every native recursor rule (ordinary or
nested, every elimination mode) and every generic case equation is covered. -/
structure ProjFree (env : VEnv) : Prop where
  projections : ∀ n p, ¬ env.projections n p

/-- **Stages B, D and E**: chain-level head injectivity for well-formed environments without
projections. -/
theorem WF.headInjectivityCore_of_projFree {env : VEnv} (henv : env.WF)
    (hB : env.ProjFree) : env.HeadInjectivityCore := by
  obtain ⟨ds, H⟩ := henv
  have hvalid := WF'.ruleValid ⟨ds, H⟩ hB.projections H .rfl (fun _ h _ _ _ _ => h)
  exact WF.headInjectivityCore_of_sound ⟨ds, H⟩ fun hΔ H' =>
    Model.sound (VEnv.WF.ordered ⟨ds, H⟩) hΔ .rfl hvalid.1 (fun n p h => absurd h (hB.projections n p))
      ⟨fun _ _ _ h1 h2 => VEnv.WF.eliminators_unique ⟨ds, H⟩ h1 h2, hvalid.2⟩ H'

end VEnv
end Lean4Lean
