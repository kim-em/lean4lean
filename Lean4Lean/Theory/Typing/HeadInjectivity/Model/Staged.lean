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

end VEnv
end Lean4Lean
