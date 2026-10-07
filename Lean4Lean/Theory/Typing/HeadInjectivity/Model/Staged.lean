import Lean4Lean.Theory.Typing.HeadInjectivity.Model.Extract
import Lean4Lean.Theory.Typing.HeadInjectivity.Model.Singleton

/-! # Staged soundness (decision D11) and stage B

`VEnv.WF'.ruleValid`: in a well-formed environment `envF` without projections or eliminators
whose native rules come from compilations without container specializations
(`OrdinaryNative`), every rule of every environment in the declaration history of `envF` is
valid in the model of `envF`. The proof is by induction on the history; the semantic fact
needed by a native rule of a data family (`FamSort`: the family's type observations end in its
recorded result sort) comes from the soundness, in the model of `envF`, of the definitional
equality between the family's declared type and a telescope ending in that sort, a derivation
of the environment before the rules of the family were installed, whose rules are valid by
the induction hypothesis.

`VEnv.WF.headInjectivityCore_of_ordinary`: chain-level head injectivity under that scope.

The proof-field fact needed by singleton eliminators (mode C) comes the same way from the
soundness of the field typings recorded by `SingletonElimination`, placed in the equation's
telescope (`Model/Singleton.lean`). Uniqueness of a native rule per head comes from
`HeadsClosed`: along the history, no later declaration adds a rule headed by an existing
constant, so the rules headed by a recursor are exactly its block's equations. -/

namespace Lean4Lean
namespace VEnv
open InductiveSignature
open private addDefEqs_as_rules addConsts_as_values defeqs_addRules
  from Lean4Lean.Theory.Typing.NativeConstructorRigidity

namespace Model

variable {env : VEnv} {U : Nat} {Δ : List VExpr}

local notation "Obs'" => Obs env U Δ

/-- `family_sort` through an intermediate type. -/
theorem family_sort₂ {T M X₁ X₂ : VExpr} {ds : List VExpr} {ks : List Key}
    (H1 : SoundAt env U Δ [] T M X₁) (H2 : SoundAt env U Δ [] M (.wrapForalls ds (.sort l)) X₂)
    (h : Obs' .id .empty T (piCodChain ks (.sort z))) : z = l.eval := by
  obtain ⟨o', h1, h2⟩ := (H1 .id .id .empty .nil TV.empty TV.empty).1 _ h
  obtain ⟨o'', h3, h4⟩ := (H2 .id .id .empty .nil TV.empty TV.empty).1 _ h1
  obtain ⟨ks', -, rfl⟩ := (h4.trans h2).piCodChain_sort_inv
  exact obs_wrapForalls_sort h3

end Model

/-- Congruence of a Pi telescope in its codomain. -/
theorem wrapForalls_congr {E : VEnv} (henv : E.Ordered) : ∀ {ds Γ : List VExpr} {b b' A : VExpr}
    {l : VLevel}, E.HasType U Γ (.wrapForalls ds b) A →
    E.IsDefEq U (ds.reverse ++ Γ) b b' (.sort l) →
    ∃ v, E.IsDefEq U Γ (.wrapForalls ds b) (.wrapForalls ds b') (.sort v)
  | [], _, _, _, _, _, _, h2 => ⟨_, by simpa [VExpr.wrapForalls] using h2⟩
  | d :: ds, Γ, b, b', A, l, h1, h2 => by
    obtain ⟨⟨u, hd⟩, ⟨w, hw⟩⟩ := HasType.forallE_inv henv h1
    obtain ⟨v, hv⟩ := wrapForalls_congr henv hw (by simpa using h2)
    exact ⟨_, .forallEDF hd hv⟩

theorem install_parts {env installed : VEnv} {block : VInductBlock}
    (H : VInductBlock.install env block = some installed) :
    ∃ types, env.addConstVals block.types = some types ∧ types ≤ installed := by
  simp only [VInductBlock.install, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.pure_def, Option.some.injEq] at H
  obtain ⟨types, ht, ctors, hc, recs, hr, rfl⟩ := H
  exact ⟨types, ht, (VEnv.addConstVals_le hc).trans <| VEnv.addProjections_le.trans <|
    (VEnv.addConstVals_le hr).trans VEnv.addDefEqRules_le⟩

/-- **The semantic sort of an ordinary family** (D11): its type observations end in its
recorded result sort, in the model of any later environment `envF` in which the rules of the
environment `env0` before the family are valid. -/
theorem Model.famSort {envF env0 installed base : VEnv} {source expanded : VInductDecl}
    {s : InductiveSignature} {g : Instance s} {block : VInductBlock}
    (henvF : envF.Ordered) (h0 : env0.Ordered)
    (hnp : ∀ n p, ¬ envF.projections n p) (hne : ∀ b s, ¬ envF.eliminators b s)
    (hvalid : ∀ df, env0.defeqs df → Model.RuleValid envF df)
    (C : CompilationData base source expanded s g [] block) (hb : base ≤ env0)
    (hinst : block.install env0 = some installed) (hle : installed ≤ envF)
    (o : Fin s.families.size) : Model.FamSort envF s.families[o].name s.families[o].resultLevel := by
  intro U Δ ci lsI ks z hΔ hci hls h
  obtain ⟨envTypes, direct, htypes, hdirect, -, hfamilies⟩ := C.correspondence
  have hd : direct = [] := by simpa using hdirect.symm
  subst hd
  obtain ⟨family, hfamily, hrel⟩ := Lean4Lean.List.Forall₂.forall_exists_l
    hfamilies _ (s.declarationFamily_mem o)
  rw [List.append_nil] at hfamily
  obtain ⟨domains, body, level, exprType, hlev, h1, h2⟩ := hrel.type
  obtain ⟨types', ht, hti⟩ := install_parts hinst
  rw [C.types] at ht
  obtain ⟨-, -, -, -, _, _, _, _, hwf, _⟩ := C.sourceWF
  have hE : types'.Ordered := h0.addConstVals (fun ci hci => by
    obtain ⟨t, htm, rfl⟩ := List.mem_map.1 hci
    exact (hwf t htm).mono hb) ht
  have hTE : envTypes ≤ types' := addConstVals_mono hb htypes ht
  have hEF : types' ≤ envF := hti.trans hle
  have hfc : envF.constants family.name = some family.toVConstant :=
    hEF.constants (addConstVals_get ht (List.mem_map_of_mem hfamily))
  have hn : s.families[o].name = family.name := hrel.name
  rw [hn, hfc] at hci
  cases hci
  obtain ⟨v, h3⟩ := wrapForalls_congr hE (h1.mono hTE).hasType.2
    (by rw [List.append_nil]; exact h2.mono hTE)
  have i1 := (h1.mono hTE).instL hls
  have i3 := h3.instL hls
  simp only [List.map_nil] at i1 i3
  have s1 := IsDefEq.strong hE (show OnCtx [] (types'.IsType U) from trivial) i1
  have s3 := IsDefEq.strong hE (show OnCtx [] (types'.IsType U) from trivial) i3
  have hvalid' : ∀ df, types'.defeqs df → Model.RuleValid envF df := by
    rw [VEnv.addConstVals_defeqs ht]; exact hvalid
  have hnpE : ∀ n p, ¬ types'.projections n p := fun n p h => hnp n p (hEF.projections h)
  have hneE : ∀ b s, ¬ types'.eliminators b s := fun b s h => hne b s (hEF.eliminators h)
  have S1 := (Model.sound henvF hΔ hEF hvalid' hnpE hneE s1).1
  have S3 := (Model.sound henvF hΔ hEF hvalid' hnpE hneE s3).1
  rw [Model.instL_wrapForalls'' domains (.sort level)] at S3
  have := Model.family_sort₂ S1 S3 h
  rw [this]
  exact VLevel.inst_congr_l hlev

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

/-- **Staged validity** (D11): every rule of every environment in the declaration history of a
well-formed `envF` in scope is valid in the model of `envF`. -/
theorem WF'.ruleValid {envF : VEnv} (hF : envF.WF) (hnp : ∀ n p, ¬ envF.projections n p)
    (hne : ∀ b s, ¬ envF.eliminators b s) (hon : Model.OrdinaryNative envF) :
    ∀ {ds env}, env.WF' ds → env ≤ envF → HeadsClosed envF env →
      ∀ df, env.defeqs df → Model.RuleValid envF df := by
  have henvF := hF.ordered
  have hdr := hF.defRules
  have hctor : ∀ c, Model.IsCtor envF c → envF.Rigid c :=
    fun _ ⟨_, hdf, hm⟩ => VEnv.nativeHeadRigid_iff.1 (hF.native_constructor_rigid hdf hm)
  have hcres : ∀ c, Model.IsCtor envF c → envF.CtorResultRigid c :=
    fun _ ⟨_, hdf, hm⟩ => hF.native_constructor_result_rigid hdf hm
  intro ds env H
  induction H with
  | empty => intro _ _ df h; cases h
  | @decl d env' ds env0 hdecl hbase ih =>
    intro hle hcl df hdf
    have h0le := declaration_le' hdecl
    have h0 : env0.Ordered := (show env0.WF from ⟨ds, hbase⟩).ordered
    have ih' := ih (h0le.trans hle)
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
      · exact Model.RuleValid.delta henvF hdr hctor hdfF rfl
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
        exact Model.RuleValid.delta henvF hdr hctor hdfF rfl
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
          (hex df' hdf' ls' h')) hdr hctor hcres hdfF
      · exact @ih' hcl0 df hdf
    | induct _ installed =>
      cases installed with
      | @intro block _ _ compiled hbwf hinst =>
        obtain ⟨base, expanded, s, g, aux, hbase', C, -⟩ :=
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
        · have haux := hon C df member hdfF
          subst haux
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
          exact Model.RuleValid.native henvF hdr hctor hcres C hinst hle index hdfF hex
            (Model.famSort henvF h0 hnp hne (@ih' hcl0) C hbase' hinst hle _)
            (fun envE hE hsing U Δ Γ ls hΔ hlw _ i hi hidx => by
              have hEE : envE ≤ recursors := by
                rw [C.ordinary_expanded_types, ← C.types] at hE
                exact (addConstVals_mono hbase' hE ht).trans
                  ((VEnv.addConstVals_le hc).trans (VEnv.addConstVals_le hr))
              exact Model.proofBinder_of henvF hER hERF hvalidR
                (fun n p h => hnp n p (hERF.projections h))
                (fun b s h => hne b s (hERF.eliminators h)) hdoms
                (singleton_field_typing hER hEE hsing index hi hidx) hΔ hlw)
        · exact @ih' hcl0 df hdf
  | inductEliminators _ _ _ _ _ _ _ _ _ =>
    intro hle
    exact absurd (hle.eliminators (VEnv.addEliminator_iff.2 (.inl ⟨rfl, rfl⟩))) (hne _ _)
  | inductProjections _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih =>
    intro hle hcl df hdf
    exact @ih (VEnv.addProjections_le.trans hle) (fun df' h n ls h' ⟨ci, hci⟩ => by
      have := hcl df' h n ls h' ⟨ci, by simpa using hci⟩; simpa using this) df (by simpa using hdf)

/-- The scope of stages B and D: no projections, no eliminators, and native rules only from
compilations without container specializations (every elimination mode, including singleton
large elimination and K-like rules). -/
structure OrdinaryScope (env : VEnv) : Prop where
  projections : ∀ n p, ¬ env.projections n p
  eliminators : ∀ b s, ¬ env.eliminators b s
  native : Model.OrdinaryNative env

/-- **Stages B and D**: chain-level head injectivity for well-formed environments without
projections or eliminators whose native recursor rules come from compilations without
container specializations. -/
theorem WF.headInjectivityCore_of_ordinary {env : VEnv} (henv : env.WF) (hB : env.OrdinaryScope) :
    env.HeadInjectivityCore := by
  obtain ⟨ds, H⟩ := henv
  have hvalid := WF'.ruleValid ⟨ds, H⟩ hB.projections hB.eliminators hB.native H .rfl
    (fun _ h _ _ _ _ => h)
  exact WF.headInjectivityCore_of_sound ⟨ds, H⟩ fun hΔ H' =>
    Model.sound (VEnv.WF.ordered ⟨ds, H⟩) hΔ .rfl hvalid hB.projections hB.eliminators H'

end VEnv
end Lean4Lean
