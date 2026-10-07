import Lean4Lean.Theory.Typing.HeadInjectivity.Model.Extract
import Lean4Lean.Theory.Typing.HeadInjectivity.Model.NativeRule

/-! # Staged soundness (decision D11) and stage B

`VEnv.WF'.ruleValid`: in a well-formed environment `envF` without projections or eliminators
whose native rules come from ordinary compilations with non-singleton elimination
(`OrdinaryNative`), every rule of every environment in the declaration history of `envF` is
valid in the model of `envF`. The proof is by induction on the history; the semantic fact
needed by a native rule of a data family (`FamSort`: the family's type observations end in its
recorded result sort) comes from the soundness, in the model of `envF`, of the definitional
equality between the family's declared type and a telescope ending in that sort, a derivation
of the environment before the rules of the family were installed, whose rules are valid by
the induction hypothesis.

`VEnv.WF.headInjectivityCore_of_stageB`: chain-level head injectivity under that scope. -/

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

/-- In stage B scope, the quotient rule is the only rule headed by `Quot.lift`: native recursor
names end in `rec`. -/
theorem Model.quot_unique_head {envF : VEnv} (hsh : envF.SameHead) (hon : Model.OrdinaryNative envF)
    (hq : envF.defeqs quotDefEq) : ∀ df' ls', envF.defeqs df' →
      df'.lhs.stripLams.getAppFnArgs.1 = .const ``Quot.lift ls' → df' = quotDefEq := by
  intro df' ls' hdf' h'
  have hQ : quotDefEq.lhs.stripLams.getAppFnArgs.1 = .const ``Quot.lift [.param 0, .param 1] := by
    rw [Model.quotDefEq_lhs]; exact VExpr.stripLams_wrapLams_mkApps_head
  obtain ⟨rs, hrs, hm, hm'⟩ := hsh _ _ hdf' hq _ _ _ h' hQ
  cases hrs with
  | «mutual» cis =>
    obtain ⟨ci, -, e⟩ := List.mem_map.1 hm'
    exact absurd (congrArg VDefEq.lhs e).symm quotDefEq_lhs_ne_const
  | quot => exact List.mem_singleton.1 hm
  | @native _ _ _ s' g' aux' block' C' =>
    obtain ⟨rfl, -⟩ := hon C' _ hm' hq
    rw [C'.ordinary_rules] at hm'
    obtain ⟨i, -, ei⟩ := List.mem_map.1 hm'
    have hl := g'.equation_lhs_eq i
    rw [ei] at hl
    obtain ⟨-, hn, -⟩ := Model.wrapLams_pat_inj (Model.quotDefEq_lhs.symm.trans hl)
    rw [C'.recursorNames] at hn
    injection hn with _ h2
    exact absurd h2 (by decide)

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
well-formed `envF` in stage B scope is valid in the model of `envF`. -/
theorem WF'.ruleValid {envF : VEnv} (hF : envF.WF) (hnp : ∀ n p, ¬ envF.projections n p)
    (hne : ∀ b s, ¬ envF.eliminators b s) (hon : Model.OrdinaryNative envF) :
    ∀ {ds env}, env.WF' ds → env ≤ envF → ∀ df, env.defeqs df → Model.RuleValid envF df := by
  have henvF := hF.ordered
  have hdr := hF.defRules
  have hsh := hF.sameHead
  have hctor : ∀ c, Model.IsCtor envF c → envF.Rigid c :=
    fun _ ⟨_, hdf, hm⟩ => VEnv.nativeHeadRigid_iff.1 (hF.native_constructor_rigid hdf hm)
  have hcres : ∀ c, Model.IsCtor envF c → envF.CtorResultRigid c :=
    fun _ ⟨_, hdf, hm⟩ => hF.native_constructor_result_rigid hdf hm
  intro ds env H
  induction H with
  | empty => intro _ df h; cases h
  | @decl d env' ds env0 hdecl hbase ih =>
    intro hle df hdf
    have h0le := declaration_le' hdecl
    have ih' := ih (h0le.trans hle)
    have hdfF := hle.defeqs hdf
    cases hdecl with
    | «axiom» _ hadd | «opaque» _ hadd =>
      exact @ih' df (by rwa [VEnv.addConst_defeqs hadd] at hdf)
    | «example» => exact @ih' df hdf
    | @«def» env₁ _ ci _ hadd =>
      rcases hdf with rfl | hdf
      · exact Model.RuleValid.delta henvF hdr hctor hdfF rfl
      · exact @ih' df (by rwa [VEnv.addConst_defeqs hadd] at hdf)
    | mutualDef _ hadd _ =>
      rw [addDefEqs_as_rules, defeqs_addRules] at hdf
      rcases hdf with member | hdf
      · obtain ⟨ci, _, rfl⟩ := List.mem_map.mp member
        exact Model.RuleValid.delta henvF hdr hctor hdfF rfl
      · exact @ih' df (by
          rwa [VEnv.addConstVals_defeqs (addConsts_as_values ▸ hadd)] at hdf)
    | quot _ installed =>
      simp only [VEnv.addQuot, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.some.injEq] at installed
      obtain ⟨a, ha, b, hb, c, hc, e, he, rfl⟩ := installed
      rcases hdf with rfl | hdf
      · have hq : Model.QuotConsts envF := by
          have hle' : e.addDefEq quotDefEq ≤ envF := hle
          refine ⟨?_, ?_, ?_⟩
          · exact hle'.constants (VEnv.addDefEq_le.constants ((VEnv.addConst_le he).constants
              ((VEnv.addConst_le hc).constants ((VEnv.addConst_le hb).constants
                (VEnv.addConst_self ha)))))
          · exact hle'.constants (VEnv.addDefEq_le.constants ((VEnv.addConst_le he).constants
              ((VEnv.addConst_le hc).constants (VEnv.addConst_self hb))))
          · exact hle'.constants (VEnv.addDefEq_le.constants ((VEnv.addConst_le he).constants
              (VEnv.addConst_self hc)))
        exact Model.RuleValid.quot henvF hq (Model.quot_unique_head hsh hon hdfF) hdr hctor
          hcres hdfF
      · exact @ih' df (by
          rwa [VEnv.addConst_defeqs he, VEnv.addConst_defeqs hc,
            VEnv.addConst_defeqs hb, VEnv.addConst_defeqs ha] at hdf)
    | induct _ installed =>
      cases installed with
      | @intro block _ _ compiled _ hinst =>
        obtain ⟨base, expanded, s, g, aux, hbase', C, -⟩ :=
          compiled.compiled.compilationOrigin
        have hinst' := hinst
        simp only [VInductBlock.install, Option.bind_eq_bind, Option.bind_eq_some_iff,
          Option.pure_def, Option.some.injEq] at hinst'
        obtain ⟨types, ht, ctors, hc, recursors, hr, rfl⟩ := hinst'
        rw [defeqs_addRules] at hdf
        rcases hdf with member | hdf
        · obtain ⟨rfl, -⟩ := hon C df member hdfF
          rw [C.ordinary_rules] at member
          obtain ⟨index, -, rfl⟩ := List.mem_map.1 member
          have h0 : env0.Ordered := (show env0.WF from ⟨ds, hbase⟩).ordered
          exact Model.RuleValid.native henvF hdr hsh hon hctor hcres C hinst hle index hdfF
            (fun _ => Model.famSort henvF h0 hnp hne ih' C hbase' hinst hle _)
        · exact @ih' df (by
            rwa [VEnv.addConstVals_defeqs hr, VEnv.addProjections_defeqs,
              VEnv.addConstVals_defeqs hc, VEnv.addConstVals_defeqs ht] at hdf)
  | inductEliminators _ _ _ _ _ _ _ _ _ =>
    intro hle
    exact absurd (hle.eliminators (VEnv.addEliminator_iff.2 (.inl ⟨rfl, rfl⟩))) (hne _ _)
  | inductProjections _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih =>
    intro hle df hdf
    exact @ih (VEnv.addProjections_le.trans hle) df (by simpa using hdf)

/-- The stage B scope: no projections, no eliminators, and native rules only from ordinary
compilations whose elimination is admissible by non-zero family sorts or a zero target. -/
structure StageB (env : VEnv) : Prop where
  projections : ∀ n p, ¬ env.projections n p
  eliminators : ∀ b s, ¬ env.eliminators b s
  native : Model.OrdinaryNative env

/-- **Stage B**: chain-level head injectivity for well-formed environments without projections
or eliminators whose native recursor rules come from ordinary compilations of families with
non-zero sorts or with elimination into `Prop`. -/
theorem WF.headInjectivityCore_of_stageB {env : VEnv} (henv : env.WF) (hB : env.StageB) :
    env.HeadInjectivityCore := by
  obtain ⟨ds, H⟩ := henv
  have hvalid := WF'.ruleValid ⟨ds, H⟩ hB.projections hB.eliminators hB.native H .rfl
  exact WF.headInjectivityCore_of_sound ⟨ds, H⟩ fun hΔ H' =>
    Model.sound (VEnv.WF.ordered ⟨ds, H⟩) hΔ .rfl hvalid hB.projections hB.eliminators H'

end VEnv
end Lean4Lean
