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

theorem IotaRuleData.SyntaxAt.mono {D : IotaRuleData} {T : Name} (h : D.SyntaxAt env T)
    (hle : env ≤ env') : D.SyntaxAt env' T where
  former_find := let ⟨tc, h⟩ := h.former_find; ⟨tc, hle.constants h⟩
  rec_find := let ⟨c, h1, h2, h3⟩ := h.rec_find; ⟨c, hle.constants h1, h2, h3⟩
  ctor_find := let ⟨c, h1, h2⟩ := h.ctor_find; ⟨c, hle.constants h1, h2⟩
  ctor_params := h.ctor_params

theorem IotaRuleData.ShapeAt.mono {D : IotaRuleData} {T : Name} (h : D.ShapeAt env T)
    (hle : env ≤ env') (hr : Rigid env' T) : D.ShapeAt env' T where
  toSyntaxAt := h.toSyntaxAt.mono hle
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
  defeq_heads := fun {df} hdf c us h1 => by
    rw [addConst_defeqs h] at hdf
    obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.1 (hst.defeq_heads hdf c us h1)
    rw [(addConst_le h).constants ha]; nofun

theorem Stage.constExt (h1C : Wave1C) (hst : Stage env) {env₀ : VEnv} (hext : ConstExt env env₀) :
    Stage env₀ := by
  induction hext with
  | rfl => exact hst
  | const _ hci h ih => exact ih.addConst h1C hci h

/-! ## `Stage` through a definitional axiom -/

/-- Two `IotaRuleData` with the same pattern name the same recursor and type former: the
pattern pins the recursor and the major index, the recursor's constant its type, the type its
former. -/
theorem IotaRuleData.former_eq {D D' : IotaRuleData} {T T' : Name} (he : D.pattern = D'.pattern)
    (h : D.SyntaxAt env T) (h' : D'.SyntaxAt env T') : T = T' := by
  obtain ⟨hn, hm, -, -⟩ := iota_toPattern_inj he
  obtain ⟨recC, h1, -, h2⟩ := h.rec_find
  obtain ⟨recC', h1', -, h2'⟩ := h'.rec_find
  rw [← hn, h1] at h1'; cases h1'
  rw [hm] at h2
  exact Option.some.inj (h2.symm.trans h2')

/-- The head of a simple pattern equal to an ι pattern is that ι pattern's recursor. -/
theorem _root_.Lean4Lean.SimplePattern.head_eq_of_iota {r : Name} {m : Nat} {c : Name} {n : Nat}
    {sp : SimplePattern} (h : (SimplePattern.iota r m c n).toPattern = sp.toPattern) : sp.head = r := by
  cases sp with
  | defn c' => cases h
  | iota r' m' c' n' => exact (iota_toPattern_inj h).1.symm

/-- Adding a definitional axiom to `env`, an environment with the rules of a `Stage`
environment `env₀ ≤ env`, headed by a constant fresh in `env₀`, keeps `Stage`: the type formers
of the rules are constants of `env₀`, hence differ from the new head, so they stay rigid. -/
theorem Stage.addDefEq' (h1C : Wave1C) {env₀ : VEnv} (hst₀ : Stage env₀) (hle : env₀ ≤ env)
    (hpe : env.pats = env₀.pats) (hst : Stage env) {df : VDefEq} (hdf : df.WF env)
    (hhead : ∀ c us, df.lhs.getAppFn = .const c us → env₀.constants c = none ∧ env.constants c ≠ none) :
    Stage (env.addDefEq df) := by
  have hpats : PatsStrongOn env := hst.patsStrongOn' h1C
  refine ⟨.defeq hst.ordered hdf, ?_, ?_, ?_⟩
  · exact OnTypes.addDefEq hst.strong
      (EnvStrong.of_hasType hst.ordered hst.strong hpats hdf.1)
      (EnvStrong.of_hasType hst.ordered hst.strong hpats hdf.2)
  · intro p r hp
    have hp' : env.pats p r := hp
    obtain ⟨D, e, hr, hgen, T, hsh⟩ := hst.rules hp'
    refine ⟨D, e, hr, hgen.mono addDefEq_le, T, hsh.mono addDefEq_le ?_⟩
    refine hsh.rigid.addDefEq fun us' h => ?_
    obtain ⟨hfresh, -⟩ := hhead _ _ h
    obtain ⟨D', e', -, -, T', hsh'⟩ := hst₀.rules (hpe ▸ hp')
    have hTT : T = T' :=
      IotaRuleData.former_eq (e.symm.trans e') hsh.toSyntaxAt (hsh'.toSyntaxAt.mono hle)
    obtain ⟨tc, htc⟩ := hsh'.former_find
    rw [← hTT, hfresh] at htc
    cases htc
  · intro df' hdf' c us h1
    rcases hdf' with rfl | hdf'
    · exact (hhead c us h1).2
    · exact hst.defeq_heads hdf' c us h1

/-- The definitional axioms of a mutual block, one `Stage.addDefEq'` each. -/
theorem Stage.addDefEqs (h1C : Wave1C) {env₀ : VEnv} (hst₀ : Stage env₀) :
    ∀ {cis : List VDefVal} {env : VEnv}, env₀ ≤ env → env.pats = env₀.pats → Stage env →
      (∀ ci ∈ cis, env.constants ci.name = some ci.toVConstant) → (∀ ci ∈ cis, ci.WF env) →
      (∀ ci ∈ cis, env₀.constants ci.name = none) → Stage (env.addDefEqs cis)
  | [], _, _, _, hst, _, _, _ => hst
  | ci :: cis, env, hle, hpe, hst, hmem, hw, hfresh => by
    show Stage ((env.addDefEq ci.toDefEq).addDefEqs cis)
    have hci : ci.WF env := hw _ (.head _)
    have hdf : ci.toDefEq.WF env := by
      refine ⟨?_, hci⟩
      simp [VDefVal.toDefEq]
      rw [← (hci.levelWF ⟨⟩).2.2.instL_id]
      exact .const (hmem _ (.head _)) VLevel.id_WF (by simp)
    have hst' := Stage.addDefEq' h1C hst₀ hle hpe hst hdf fun c us h => by
      obtain ⟨rfl, -⟩ := VExpr.const.inj h
      exact ⟨hfresh _ (.head _), by rw [hmem _ (.head _)]; nofun⟩
    exact Stage.addDefEqs h1C hst₀ (hle.trans addDefEq_le) hpe hst'
      (fun c hc => (addDefEq_le (df := ci.toDefEq)).constants (hmem c (.tail _ hc)))
      (fun c hc => (hw c (.tail _ hc)).mono addDefEq_le) (fun c hc => hfresh c (.tail _ hc))

/-- The left-hand side of the quotient rule is a λ-abstraction (`vdefeq` closes it over its
variables), so it is headed by no constant. -/
theorem quotDefEq_lhs_not_const (c : Name) (us : List VLevel) :
    quotDefEq.lhs.getAppFn ≠ .const c us := by
  intro h; simp [quotDefEq, VExpr.getAppFn] at h

/-- The quotient: four constants and one definitional axiom headed by `Quot.lift`. -/
theorem Stage.addQuot (h1C : Wave1C) (hst : Stage env) (hq : QuotReady env)
    (h : env.addQuot = some env') : Stage env' := by
  obtain ⟨q1, q2, q3, q4, w1, a1, w2, a2, w3, a3, w4, a4, wdf, rfl⟩ := addQuot_chain hq h
  have hext : ConstExt env q4 := (((ConstExt.rfl.const w1 a1).const w2 a2).const w3 a3).const w4 a4
  have hst4 := hst.constExt h1C hext
  exact Stage.addDefEq' h1C hst hext.le hext.pats hst4 wdf fun c us h =>
    absurd h (quotDefEq_lhs_not_const c us)

/-- An inductive block: three constant stages, then the rules. Each new rule's generic typing
is strengthened at the stage-2 environment `envR` with `PatsStrongOn envR` — `envR` is a
constant-only extension of `env`, the environment *before* the block, whose `Stage` is the
induction hypothesis — and moved to the final environment by monotonicity. Rigidity: the new
patterns are headed by the recursors, fresh in `envC`, while every type former (old or new) is a
constant of `envC`; the definitional axioms are unchanged and headed by constants of `env`,
while the new type formers are fresh in `env`. -/
theorem Stage.addInduct (h1C : Wave1C) (hgen : RulesGenericTyped) (hst : Stage env)
    {decl : VInductDecl} (hdecl : decl.WF env) (h : env.addInduct decl = some env') : Stage env' := by
  obtain ⟨envT, envC, envR, hT, hC, hR, hP⟩ := addInduct_stages h
  have hTC : decl.addTypesCtors env = some envC := by
    unfold VInductDecl.addTypesCtors; rw [hT]; exact hC
  have hTCR : decl.addTypesCtorsRecs env = some envR := by
    unfold VInductDecl.addTypesCtorsRecs; rw [hTC]; exact hR
  have leT := addTypes_le hT; have leC := addCtors_le hC
  have leR := addRecs_le hR; have leP := addRules_le hP
  have extT : ConstExt env envT := by
    unfold VInductDecl.addTypes at hT
    exact ConstExt.foldlM (nm := fun t : VInductiveType => t.name)
      (ci := fun t : VInductiveType => t.toVConstVal.toVConstant) hdecl.types_wf hT
  have extC : ConstExt envT envC := by
    unfold VInductDecl.addCtors at hC
    refine ConstExt.foldlM (nm := fun c : VConstVal => c.name)
      (ci := fun c : VConstVal => c.toVConstant) (fun c hc => ?_) hC
    obtain ⟨t, ht, hc⟩ := List.mem_flatMap.1 hc
    exact hdecl.ctors_wf envT hT t ht c hc
  have extR : ConstExt envC envR := by
    unfold VInductDecl.addRecs at hR
    exact ConstExt.foldlM (nm := fun r : VRecursor => r.name)
      (ci := fun r : VRecursor => r.toVConstVal.toVConstant) (hdecl.recs_wf envC hTC) hR
  have hstR := hst.constExt h1C (extT.trans (extC.trans extR))
  have hpatsR : PatsStrongOn envR := hstR.patsStrongOn' h1C
  have htfresh : ∀ t ∈ decl.types, env.constants t.name = none := by
    unfold VInductDecl.addTypes at hT; exact addConst_foldlM_fresh hT
  have hrfresh : ∀ r ∈ decl.recs, envC.constants r.name = none := addRecs_fresh hR
  have hle' := addInduct_le h
  -- the head of every pattern of `env'` is a constant of `env` or a recursor of the block
  have hheads : ∀ {p : Pattern} {rr : p.RHS × p.Check}, env'.pats p rr → ∀ sp : SimplePattern,
      p = sp.toPattern → env.constants sp.head ≠ none ∨ ∃ r ∈ decl.recs, sp.head = r.name := by
    intro p rr hp sp hsp
    rcases addInduct_pats_origin' h hp with hold | ⟨r, hr, ru, hru, hc, e, hrr⟩
    · obtain ⟨D, e, -, -, T, hsh⟩ := hst.rules hold
      obtain ⟨recC, hrecC, -, -⟩ := hsh.rec_find
      left
      rw [SimplePattern.head_eq_of_iota (e.symm.trans hsp), hrecC]; nofun
    · exact .inr ⟨r, hr, SimplePattern.head_eq_of_iota (e.symm.trans hsp)⟩
  refine ⟨addInduct_WF hst.ordered hdecl h, addRules_strong hstR.strong hP, ?_, ?_⟩
  · intro p rr hp
    rcases addInduct_pats_origin' h hp with hold | ⟨r, hr, ru, hru, hc, e, hrr⟩
    · -- an old rule: its type former is a constant of `env`, hence not a new recursor
      obtain ⟨D, e, hr', hgen', T, hsh⟩ := hst.rules hold
      refine ⟨D, e, hr', hgen'.mono hle', T, hsh.mono hle' ⟨fun df hdf us => ?_, fun p' rr' hp' sp hsp => ?_⟩⟩
      · rw [addInduct_defeqs h] at hdf; exact hsh.rigid.1 df hdf us
      · rcases addInduct_pats_origin' h hp' with hold' | ⟨r', hr', ru', hru', hc', e', hrr'⟩
        · exact hsh.rigid.2 p' rr' hold' sp hsp
        · rw [SimplePattern.head_eq_of_iota (e'.symm.trans hsp)]
          obtain ⟨tc, htc⟩ := hsh.former_find
          intro hT; rw [← hT] at htc
          rw [addInduct_rec_fresh h hr'] at htc; cases htc
    · -- a new rule: generic typing from the installer at `envR`, strengthened there
      subst e
      obtain ⟨hgw, T, hsyn⟩ := hgen hdecl hTCR r hr ru hru hc
      have hTt : ∃ t ∈ decl.types, T = t.name := by
        obtain ⟨recC, hrecC, -, hmaj⟩ := hsyn.rec_find
        have hrecC' : envR.constants r.name = some recC := hrecC
        rw [addRecs_find hR r hr] at hrecC'; cases hrecC'
        obtain ⟨t, ht, hmaj'⟩ := hdecl.recs_over_block r hr
        exact ⟨t, ht, Option.some.inj (hmaj.symm.trans hmaj')⟩
      obtain ⟨t, ht, rfl⟩ := hTt
      have hTenv : env.constants t.name = none := htfresh t ht
      have hTC' : envC.constants t.name ≠ none := by
        rw [leC.constants (addTypes_find hT t ht)]; nofun
      refine ⟨IotaRuleData.ofRule r ru hc, rfl, hrr,
        (hgw.strong hstR.ordered hstR.strong hpatsR).mono leP, t.name,
        ⟨hsyn.mono leP, fun df hdf us => ?_, fun p' rr' hp' sp hsp => ?_⟩⟩
      · rw [addInduct_defeqs h] at hdf
        intro h'; exact hst.defeq_heads hdf _ _ h' hTenv
      · intro hT
        rcases hheads hp' sp hsp with hc' | ⟨r', hr', hr'eq⟩
        · exact hc' (hT ▸ hTenv)
        · rw [hr'eq] at hT
          exact hTC' (hT ▸ hrfresh r' hr')
  · intro df hdf c us h1
    rw [addInduct_defeqs h] at hdf
    obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.1 (hst.defeq_heads hdf c us h1)
    rw [hle'.constants ha]; nofun

/-! ## The induction -/

/-- **`Stage` for every well-formed environment**, from the two named hypotheses. -/
theorem WF'.stage (h1C : Wave1C) (hgen : RulesGenericTyped) :
    ∀ {ds : List VDecl} {env : VEnv}, WF' ds env → Stage env := by
  intro ds env H
  induction H with
  | empty =>
    exact ⟨.empty, ⟨nofun, nofun⟩, fun hp => (nomatch hp), fun hdf => (nomatch hdf)⟩
  | decl hd _ ih =>
    cases hd with
    | «axiom» h1 h2 => exact ih.addConst h1C h1 h2
    | «opaque» h1 h2 => exact ih.addConst h1C (h1.isType (Γ := []) ih.ordered ⟨⟩) h2
    | «example» _ => exact ih
    | «def» h1 h2 =>
      have hisT := h1.isType (Γ := []) ih.ordered ⟨⟩
      have hst₁ := ih.addConst h1C hisT h2
      refine Stage.addDefEq' h1C ih (addConst_le h2) (addConst_pats h2) hst₁
        ⟨?_, h1.mono (addConst_le h2)⟩ fun c us h => ?_
      · simp [VDefVal.toDefEq]
        rw [← (h1.levelWF ⟨⟩).2.2.instL_id]
        exact .const (addConst_self h2) VLevel.id_WF (by simp)
      · obtain ⟨rfl, -⟩ := VExpr.const.inj h
        exact ⟨(addConst_eq h2).1, by rw [(addConst_eq h2).2.1]; nofun⟩
    | mutualDef h0 h1 h2 =>
      have h1' := h1
      unfold VEnv.addConsts at h1'
      have hext := ConstExt.foldlM (nm := fun c : VDefVal => c.name)
        (ci := fun c : VDefVal => c.toVConstant) h0 h1'
      exact Stage.addDefEqs h1C ih hext.le hext.pats (ih.constExt h1C hext)
        (addConsts_constants h1) h2 (addConst_foldlM_fresh h1')
    | quot h1 h2 => exact ih.addQuot h1C h1 h2
    | induct h1 h2 => exact ih.addInduct h1C hgen h1 h2

/-- Subject reduction of the registered ι rules in every constant-only extension of a
well-formed environment. -/
theorem patsStrongWF (h1C : Wave1C) (hgen : RulesGenericTyped) : PatsStrongWF :=
  fun {_ _} ⟨_, H⟩ hext => ((H.stage h1C hgen).constExt h1C hext).patsStrongOn' h1C

/-- #43's `VEnv.PatsStrong`, with `env₁.WF` in place of `env.WFPrefix env₁` and without the
unused bound `env₀ ≤ env`. -/
theorem WF.patsStrong' (h1C : Wave1C) (hgen : RulesGenericTyped) {env₁ env₀ : VEnv}
    (H₁ : env₁.WF) (hle : env₁ ≤ env₀) (hd : env₀.defeqs = env₁.defeqs)
    (hp : env₀.pats = env₁.pats) (hord : Ordered env₀) : PatsStrongOn env₀ :=
  patsStrongWF h1C hgen H₁ (ConstExt.of_ordered hle hd hp hord)

/-- `VEnv.WF.orderedStrong`, from the `Stage` of the environment itself. -/
theorem WF.orderedStrong' (h1C : Wave1C) (hgen : RulesGenericTyped) (H : env.WF) :
    OrderedStrong env :=
  let ⟨_, H⟩ := H
  have hst := H.stage h1C hgen
  ⟨hst.ordered, hst.strong, hst.patsStrongOn' h1C⟩

end VEnv
end Lean4Lean
