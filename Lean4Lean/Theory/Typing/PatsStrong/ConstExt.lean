import Lean4Lean.Theory.Typing.EnvLemmas

/-! # Constant-only extensions of an environment

`VEnv.WF.patsStrong` (`EnvLemmas.lean`) quantifies over the environments `env₀` with
`env₁ ≤ env₀ ≤ env`, `env₀.defeqs = env₁.defeqs`, `env₀.pats = env₁.pats` and `Ordered env₀`,
for `env₁` a `WFPrefix` of `env`. Every use of it in `VEnv.WF.strong` is at an `env₀` reached
from `env₁` by a fold of well-typed `addConst` steps: the stage environments of `addInduct`
and the intermediate environments of `addQuot`. This file names that shape (`VEnv.ConstExt`),
proves that the four hypotheses of `PatsStrong` are equivalent to it
(`VEnv.ConstExt.of_ordered`), and records the one place where #43's statement is looser than
what is provable by history induction: `VEnv.WFPrefix env env₁` does not make `env₁`
well-formed (`WFPrefix.rfl` holds for any `env₁`, and a `decl` step may be a re-ordering of
the real history that leaves `env₁` ill-typed), so the history argument needs `env₁.WF`
(`VEnv.PatsStrongWF`). -/

namespace Lean4Lean
namespace VEnv

/-- `env₀` extends `env` by well-typed constants alone: the shape of every stage
environment the strengthening argument walks through. -/
inductive ConstExt : VEnv → VEnv → Prop where
  | rfl {env : VEnv} : ConstExt env env
  | const {env env₀ env₀' : VEnv} {n : Name} {ci : VConstant} :
    ConstExt env env₀ → ci.WF env₀ → env₀.addConst n ci = some env₀' → ConstExt env env₀'

namespace ConstExt

theorem le {env env₀ : VEnv} (h : ConstExt env env₀) : env ≤ env₀ := by
  induction h with
  | rfl => exact .rfl
  | const _ _ h ih => exact ih.trans (addConst_le h)

theorem defeqs {env env₀ : VEnv} (h : ConstExt env env₀) : env₀.defeqs = env.defeqs := by
  induction h with
  | rfl => rfl
  | const _ _ h ih => exact (addConst_defeqs h).trans ih

theorem pats {env env₀ : VEnv} (h : ConstExt env env₀) : env₀.pats = env.pats := by
  induction h with
  | rfl => rfl
  | const _ _ h ih => exact (addConst_pats h).trans ih

theorem ordered {env env₀ : VEnv} (hord : Ordered env) (h : ConstExt env env₀) : Ordered env₀ := by
  induction h with
  | rfl => exact hord
  | const _ hci h ih => exact .const ih hci h

theorem trans {env env₁ env₂ : VEnv} (h₁ : ConstExt env env₁) (h₂ : ConstExt env₁ env₂) :
    ConstExt env env₂ := by
  induction h₂ with
  | rfl => exact h₁
  | const _ hci h ih => exact .const ih hci h

/-- A fold of `addConst` over constants typed in the environment the fold starts from is a
constant-only extension. -/
theorem foldlM {α} {nm : α → Name} {ci : α → VConstant} :
    ∀ {l : List α} {init final : VEnv},
      (∀ a ∈ l, (ci a).WF init) →
      l.foldlM (fun e a => e.addConst (nm a) (ci a)) init = some final →
      ConstExt init final
  | [], _, _, _, h => by simp [List.foldlM] at h; subst h; exact .rfl
  | a :: _, _, _, hwf, h => by
    simp only [List.foldlM] at h
    obtain ⟨env₁, h₁, h₂⟩ := Option.bind_eq_some_iff.1 h
    have hle₁ := addConst_le h₁
    exact (ConstExt.rfl.const (hwf a (.head _)) h₁).trans
      (foldlM (fun b hb => (hwf b (.tail _ hb)).mono hle₁) h₂)

/-- The four hypotheses of `VEnv.PatsStrong` on `env₀` imply that `env₀` is a constant-only
extension of `env₁`: the constants of `env₀` outside `env₁` can be added to `env₁` in the
order in which `Ordered env₀` adds them, each typed by monotonicity from the environment
`Ordered` typed it in (whose definitional axioms and rules are among `env₁`'s). -/
theorem of_ordered {env₁ env₀ : VEnv} (hle : env₁ ≤ env₀)
    (hd : env₀.defeqs = env₁.defeqs) (hp : env₀.pats = env₁.pats) (hord : Ordered env₀) :
    ConstExt env₁ env₀ := by
  -- `e ⊔ env₁`: `env₁` with the constants of `e` not in `env₁` added.
  let join (e : VEnv) : VEnv :=
    { constants := fun n => (env₁.constants n).or (e.constants n), defeqs := env₁.defeqs,
      pats := env₁.pats }
  have key : ∀ {e : VEnv}, Ordered e → e ≤ env₀ → ConstExt env₁ (join e) := by
    intro e he
    induction he with
    | empty =>
      intro _
      have : join ∅ = env₁ := by
        simp only [join]; ext1
        · funext n; simp [EmptyCollection.emptyCollection, VEnv.empty]
        · rfl
        · rfl
      exact this ▸ .rfl
    | @const e n ci e' hord' hci hadd ih =>
      intro hle'
      have hle₀ : e ≤ e' := addConst_le hadd
      have ih := ih (hle₀.trans hle')
      have hjoin_le : e ≤ join e := by
        refine ⟨fun {m a} h => ?_, fun h => ?_, fun h => ?_⟩
        · -- functionality of the constants of `env₀`
          show (env₁.constants m).or (e.constants m) = some a
          cases h₁ : env₁.constants m with
          | none => simpa using h
          | some b =>
            have := (hle.constants h₁).symm.trans ((hle₀.trans hle').constants h)
            cases this; simp
        · exact hd ▸ (hle₀.trans hle').defeqs h
        · exact hp ▸ (hle₀.trans hle').pats h
      obtain ⟨hnone, hsome, hconst⟩ := addConst_eq hadd
      have hjoin : ∀ m, n ≠ m → (join e').constants m = (join e).constants m := fun m hm => by
        show (env₁.constants m).or (e'.constants m) = (env₁.constants m).or (e.constants m)
        rw [hconst m hm]
      cases h₁ : env₁.constants n with
      | some b =>
        -- `n` is already a constant of `env₁`: the join does not change
        have : join e' = join e := by
          ext1
          · funext m
            by_cases hm : n = m
            · subst hm; show (env₁.constants n).or _ = (env₁.constants n).or _; simp [h₁]
            · exact hjoin m hm
          · rfl
          · rfl
        exact this ▸ ih
      | none =>
        -- `n` is new: one more `addConst` step on the join
        have hjoinNone : (join e).constants n = none := by
          show (env₁.constants n).or (e.constants n) = none; simp [h₁, hnone]
        refine ih.const (n := n) (hci.mono hjoin_le) ?_
        simp only [VEnv.addConst, hjoinNone]
        congr 1
        ext1
        · funext m
          by_cases hm : n = m
          · subst hm
            show _ = (env₁.constants n).or (e'.constants n)
            simp [h₁, hsome]
          · simp only [if_neg hm]; exact (hjoin m hm).symm
        · rfl
        · rfl
    | defeq _ _ ih => intro hle'; exact ih (addDefEq_le.trans hle')
    | pat _ _ ih => intro hle'; exact ih (addPat_le.trans hle')
  have : join env₀ = env₀ := by
    simp only [join]; ext1
    · funext n
      cases h₁ : env₁.constants n with
      | none => show (env₁.constants n).or _ = _; rw [h₁, Option.none_or]
      | some b => show (env₁.constants n).or _ = _; rw [h₁, hle.constants h₁, Option.some_or]
    · exact hd.symm
    · exact hp.symm
  exact this ▸ key hord .rfl

end ConstExt

/-- `VEnv.PatsStrong` with its prefix hypothesis tightened to well-formedness: subject
reduction of the registered ι rules in every constant-only extension of a well-formed
environment. `VEnv.WF.strong` only ever applies the hypothesis at a genuine prefix of the
history (so `env₁.WF` is available there) and at a `foldlM addConst` stage of it (so
`ConstExt env₁ env₀` is available); by `ConstExt.of_ordered` the remaining four hypotheses of
`PatsStrong` are exactly `ConstExt`. -/
def PatsStrongWF : Prop :=
  ∀ {env₁ env₀ : VEnv}, env₁.WF → ConstExt env₁ env₀ → PatsStrongOn env₀

end VEnv
end Lean4Lean
