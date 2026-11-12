import Lean4Lean.Theory.Typing.Strengthening.KlopSeparation.MinimalEnv
import Lean4Lean.Theory.Typing.Strengthening.KlopSeparation.Fundamental

/-! # Strengthening of definitional equality is false

Target of this directory: `not_weakN_iff_of_setModel`, the negation of the statement of
`IsDefEqU.weakN_iff`, for any `SetModel` (`SetModel.lean`: an applicative set theory with
dependent products, separation, replacement, pairing, unions and an embedding of the Lean
types of the lowest universe). `ZFSet.{0}` is a `SetModel`, so the hypothesis is satisfied
outright; the instance is in the model repository, which has Mathlib.

The proof is assembled here from the machine-checked half of the Klop example
(`KlopEnv.above`, `KlopEnv.not_strengthening`), the minimal environment
(`exists_minimalKlopEnv`, proved in `MinimalEnv.lean`: canonical `Eq` installed as a
hand-built inductive declaration, then the six declarations, with an exact inventory), the
interpretation of terms in the set model (`Interp.lean`, where `⟦C E⟧ = 1` and `⟦E⟧ = 0` is
proved), and the fundamental theorem of the model (`KlopInventory.sound`, in
`Fundamental.lean`): in an environment with that inventory, every derivable judgment
satisfies the semantic judgment `Sem`, the uniformity clause `SemU` and the head invariant.

The semantic universes are sets without any universe of sets in the metatheory because
function spaces contain only uniform functions (`Uniform.lean`, `UnifSem.lean`), which bounds
the Π-depth of every family of types (`ValidAny.mem_bset` in `ValidU.lean`).

No file of this directory uses `sorry`; `not_weakN_iff_of_setModel` depends on the axioms
`propext`, `Classical.choice` and `Quot.sound`.

Nothing outside this directory depends on these files.
-/

namespace Lean4Lean
namespace VEnv.Strengthening

/-- In an environment with the Klop inventory, `C E ≡ E` is not derivable in the empty
context: in any set model the two terms denote `1` and `0`. -/
theorem KlopInventory.separated (𝕊 : SetModel) {env : VEnv}
    (henv : env.WF) (heq : env.HasCanonicalEq) (K : KlopInventory env) :
    K.toKlopEnv.Separated 0 := by
  rintro ⟨A, H⟩
  exact 𝕊.den_CE_ne_E (fun _ => 𝕊.star) (K.den_sound 𝕊 henv heq H _)

/-- **The statement of `IsDefEqU.weakN_iff` is false**, given a set model (of which
`ZFSet.{0}` is one). -/
theorem not_weakN_iff_of_setModel (𝕊 : SetModel) :
    ¬ ∀ {env : VEnv} {U n k : Nat} {Γ Γ' : List VExpr} {e1 e2 : VExpr},
      env.WF → OnCtx Γ' (env.IsType U) → Ctx.LiftN n k Γ Γ' →
      (env.IsDefEqU U Γ' (e1.liftN n k) (e2.liftN n k) ↔ env.IsDefEqU U Γ e1 e2) := by
  intro H
  obtain ⟨env, henv, heq, K⟩ := exists_minimalKlopEnv
  exact K.toKlopEnv.not_strengthening henv heq (K.separated 𝕊 henv heq)
    (fun hΓ W => H henv hΓ W)

end VEnv.Strengthening
end Lean4Lean
