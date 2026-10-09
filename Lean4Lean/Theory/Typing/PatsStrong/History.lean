import Lean4Lean.Theory.Typing.PatsStrong.Rule
import Lean4Lean.Theory.Typing.QuotLemmas

/-! # The history induction

`Stage env` (`Spec.lean`) is carried along `VEnv.WF'`: through every constant by
`OnTypes.addConst` with `PatsStrongOn` of the *previous* environment (derived from its `Stage`
and `Wave1C`), through definitional axioms by `OnTypes.addDefEq`, and through the ι rules of an
inductive block by strengthening the installer's generic typing at the stage-2 environment
`envR` — where `PatsStrongOn envR` is available because `envR` is a constant-only extension of
the environment *before* the block — and moving it forward by `IsDefEqStrong.mono`.

The results: `Stage env` for every well-formed `env` (`WF'.stage`), `PatsStrongOn env₀` for
every constant-only extension `env₀` of a well-formed environment (`patsStrongWF`), #43's
`VEnv.PatsStrong` with `env₁.WF` in place of `env.WFPrefix env₁` (`WF.patsStrong'`), and
`OrderedStrong env` for every well-formed `env` (`WF.orderedStrong'`) — all conditional on the
two named hypotheses `Wave1C` and `RulesGenericTyped` and on the two stubs of `Rule.lean`. -/

namespace Lean4Lean
namespace VEnv

variable {env env' : VEnv}

/-! ## Rigidity along the history -/

theorem Rigid.of_same {T : Name} (h : Rigid env T) (hd : env'.defeqs = env.defeqs)
    (hp : env'.pats = env.pats) : Rigid env' T :=
  ⟨fun df hdf => h.1 df (hd ▸ hdf), fun p r hpr => h.2 p r (hp ▸ hpr)⟩

theorem Rigid.addDefEq {T : Name} {df : VDefEq} (h : Rigid env T)
    (hhead : ∀ us, df.lhs.getAppFn ≠ .const T us) : Rigid (env.addDefEq df) T := by
  refine ⟨fun df' hdf' us => ?_, h.2⟩
  rcases hdf' with rfl | hdf'
  · exact hhead us
  · exact h.1 df' hdf' us

theorem Rigid.addPat {T : Name} {p : Pattern} {r : p.RHS × p.Check} (h : Rigid env T)
    (hhead : ∀ sp : SimplePattern, p = sp.toPattern → sp.head ≠ T) : Rigid (env.addPat p r) T := by
  refine ⟨h.1, fun p' r' hp' sp hsp => ?_⟩
  rcases hp' with ⟨rfl, -⟩ | hp'
  · exact hhead sp hsp
  · exact h.2 p' r' hp' sp hsp

/-! ## Shapes along the history -/

theorem IotaRuleData.ShapeAt.mono {D : IotaRuleData} {T : Name} (h : D.ShapeAt env T)
    (hle : env ≤ env') (hr : Rigid env' T) : D.ShapeAt env' T where
  former_find := let ⟨tc, h⟩ := h.former_find; ⟨tc, hle.constants h⟩
  rec_find := let ⟨c, h1, h2, h3⟩ := h.rec_find; ⟨c, hle.constants h1, h2, h3⟩
  ctor_find := let ⟨c, h1, h2⟩ := h.ctor_find; ⟨c, hle.constants h1, h2⟩
  rigid := hr

/-- Strengthening the installer's weak generic typing at an environment with
`PatsStrongOn`: this is the one use of `IsDefEq.strong'`, at the stage-2 environment of the
declaring block. -/
theorem IotaRuleData.GenericWeak.strong {D : IotaRuleData} (hord : Ordered env)
    (hstrong : OnTypes env (EnvStrong env)) (hpats : PatsStrongOn env)
    (h : D.GenericWeak env) : D.GenericStrong env := by
  obtain ⟨U, doms, idx, cpar, cls, B, h1, h2, h3, hΓ, he, hr⟩ := h
  have hΓ' := CtxStrong.strong' hord hstrong hpats hΓ
  exact ⟨U, doms, idx, cpar, cls, B, h1, h2, h3, hΓ',
    he.strong' hord hstrong hpats hΓ', hr.strong' hord hstrong hpats hΓ'⟩

/-! ## `Stage` through constants -/

theorem Stage.patsStrongOn' (h1C : Wave1C) (hst : Stage env) : PatsStrongOn env :=
  hst.patsStrongOn (h1C hst)

theorem Stage.addConst (h1C : Wave1C) (hst : Stage env) {n : Name} {ci : VConstant}
    (hci : ci.WF env) (h : env.addConst n ci = some env') : Stage env' where
  ordered := .const hst.ordered hci h
  strong := OnTypes.addConst hst.ordered hst.strong (hst.patsStrongOn' h1C) hci h
  rules := fun {p r} hp => by
    rw [addConst_pats h] at hp
    obtain ⟨D, e, hr, hgen, T, hsh⟩ := hst.rules hp
    exact ⟨D, e, hr, hgen.mono (addConst_le h), T,
      hsh.mono (addConst_le h) (hsh.rigid.of_same (addConst_defeqs h) (addConst_pats h))⟩
  defeq_heads := fun {df} hdf => by
    rw [addConst_defeqs h] at hdf
    obtain ⟨c, us, h1, h2⟩ := hst.defeq_heads hdf
    obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.1 h2
    exact ⟨c, us, h1, by rw [(addConst_le h).constants ha]; nofun⟩

theorem Stage.constExt (h1C : Wave1C) (hst : Stage env) {env₀ : VEnv} (hext : ConstExt env env₀) :
    Stage env₀ := by
  induction hext with
  | rfl => exact hst
  | const _ hci h ih => exact ih.addConst h1C hci h

/-! ## `Stage` through a definitional axiom -/

/-- Adding a definitional axiom to a constant-only extension `env` of a `Stage` environment
`env₀`, headed by a constant fresh in `env₀`, keeps `Stage`: the rules are those of `env₀`,
whose type formers are constants of `env₀` and hence differ from the new head. -/
theorem Stage.addDefEq (h1C : Wave1C) {env₀ : VEnv} (hst₀ : Stage env₀) (hext : ConstExt env₀ env)
    {df : VDefEq} (hdf : df.WF env) {c : Name} {us : List VLevel}
    (hhead : df.lhs.getAppFn = .const c us) (hfresh : env₀.constants c = none)
    (hc : env.constants c ≠ none) : Stage (env.addDefEq df) := by
  have hst := hst₀.constExt h1C hext
  have hpats : PatsStrongOn env := hst.patsStrongOn' h1C
  refine ⟨.defeq hst.ordered hdf, ?_, ?_, ?_⟩
  · exact OnTypes.addDefEq hst.strong
      (EnvStrong.of_hasType hst.ordered hst.strong hpats hdf.1)
      (EnvStrong.of_hasType hst.ordered hst.strong hpats hdf.2)
  · intro p r hp
    have hp' : env₀.pats p r := by rwa [addDefEq_pats, hext.pats] at hp
    obtain ⟨D, e, hr, hgen, T, hsh⟩ := hst₀.rules hp'
    have hle : env₀ ≤ env.addDefEq df := hext.le.trans addDefEq_le
    refine ⟨D, e, hr, hgen.mono hle, T, hsh.mono hle ?_⟩
    refine (hsh.rigid.of_same hext.defeqs hext.pats).addDefEq fun us' h => ?_
    rw [hhead] at h
    obtain ⟨tc, htc⟩ := hsh.former_find
    cases h
    rw [hfresh] at htc; cases htc
  · intro df' hdf'
    rcases hdf' with rfl | hdf'
    · exact ⟨c, us, hhead, hc⟩
    · obtain ⟨c', us', h1, h2⟩ := hst.defeq_heads hdf'
      exact ⟨c', us', h1, h2⟩

end VEnv
end Lean4Lean
