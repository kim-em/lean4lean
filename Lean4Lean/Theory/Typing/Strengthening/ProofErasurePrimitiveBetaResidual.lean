import Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedSpines
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureIota

/-! # Ordinary primitive residuals under raw beta reduction

Beta preserves visible pattern matches and reduces their captures pointwise.
Consequently every ordinary erased primitive has an exact primitive residual,
with a beta path between the outputs. No source typing or confluence is needed.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
namespace ProofShape

/-- A finite beta path preserves a visible pattern match, including each
capture's beta path. Captured arguments may be arbitrary raw proof shapes. -/
theorem Matches.beta_residual (HM : Matches p source ls captures)
    (R : BetaRed source reduced) :
    ∃ captures', Matches p reduced ls captures' ∧ ∀ i, BetaRed (captures i) (captures' i) := by
  induction R generalizing p ls captures with
  | refl => exact ⟨_, HM, fun _ => .refl⟩
  | trans _ _ ih₁ ih₂ =>
    obtain ⟨c₁, HM₁, HR₁⟩ := ih₁ HM
    obtain ⟨c₂, HM₂, HR₂⟩ := ih₂ HM₁
    exact ⟨c₂, HM₂, fun i => (HR₁ i).trans (HR₂ i)⟩
  | app Rf Ra ihf iha =>
    cases HM with
    | var HF =>
      obtain ⟨cf, HF', HR⟩ := ihf HF
      refine ⟨_, .var HF', ?_⟩
      intro i
      cases i with
      | none => exact Ra
      | some i => exact HR i
    | app HF HA =>
      obtain ⟨cf, HF', HRf⟩ := ihf HF
      obtain ⟨ca, HA', HRa⟩ := iha HA
      refine ⟨_, .app HF' HA', ?_⟩
      intro i
      cases i with
      | inl i => exact HRf i
      | inr i => exact HRa i
  | beta => cases HM with
    | var HF => cases HF
    | app HF _ => cases HF
  | lam | forallE | proj => cases HM

private theorem beta_proj_inv (R : BetaRed (.proj s i m) out) :
    ∃ m', out = .proj s i m' ∧ BetaRed m m' := by
  generalize E : ProofShape.proj s i m = source at R
  induction R generalizing m with
  | refl => exact ⟨_, E.symm, .refl⟩
  | trans _ _ ih₁ ih₂ =>
    obtain ⟨m₁, rfl, R₁⟩ := ih₁ E
    obtain ⟨m₂, E₂, R₂⟩ := ih₂ rfl
    exact ⟨m₂, E₂, R₁.trans R₂⟩
  | proj R => cases E; exact ⟨_, rfl, R⟩
  | app | lam | forallE | beta => cases E

private theorem beta_mkApps (HF : BetaRed f f') (HA : List.Forall₂ BetaRed args args') :
    BetaRed (mkApps f args) (mkApps f' args') := by
  induction HA generalizing f f' with
  | nil => exact HF
  | cons H _ ih => exact ih (.app HF H)

variable [Params]
private theorem primitive_beta (H : Primitive D source out) (R : BetaRed source reduced) :
    ∃ shared, BetaRed out shared ∧ Primitive D reduced shared := by
  cases H with
  | @delta c ls rhs HD =>
    have HM : Matches (.const c) (.const c ls) ls nofun := .const
    obtain ⟨_, HM', _⟩ := HM.beta_residual R
    cases HM'
    exact ⟨_, .refl, .delta HD⟩
  | projIota hi hlen hget =>
    rename_i s info args i ls
    obtain ⟨_, rfl, RM⟩ := beta_proj_inv R
    obtain ⟨args', rfl, HA⟩ := RM.const_spine
    obtain ⟨hj, HE⟩ := List.getElem?_eq_some_iff.1 hget
    have hj' : info.nparams + i < args'.length := by rw [← HA.length_eq]; exact hj
    refine ⟨args'[info.nparams + i]'hj', ?_, .projIota hi (HA.length_eq.symm.trans hlen)
      (List.getElem?_eq_getElem hj')⟩
    rw [← HE]
    exact HA.getElem_of _ hj hj'

end ProofShape
variable [Params]

/-- Every ordinary erased primitive commutes with any finite beta path from
its source. The residual is one primitive of the same collection and its
output is a beta reduct of the old output. No typing or soundness is required. -/
theorem erased_iota_primitive_beta_residual
    (H : ErasedIotaPrimitive D source out) (R : ProofShape.BetaRed source reduced) :
    ∃ shared, ProofShape.BetaRed out shared ∧ ErasedIotaPrimitive D reduced shared := by
  rcases H with (H | H) | H
  · obtain ⟨shared, RB, HS⟩ := ProofShape.primitive_beta H R
    exact ⟨shared, RB, .inl (.inl HS)⟩
  · cases H with
    | select hp hc hm =>
      obtain ⟨_, hm', HR⟩ := hm.beta_residual R
      exact ⟨_, HR _, .inl (.inr (.select hp hc hm'))⟩
    | apply hp hc hm =>
      obtain ⟨_, hm', HR⟩ := hm.beta_residual R
      exact ⟨_, .app (HR _) (HR _), .inl (.inr (.apply hp hc hm'))⟩
  · cases H with
    | intro hp hc ht hm =>
      obtain ⟨captures', hm', HR⟩ := hm.beta_residual R
      refine ⟨_, ProofShape.beta_mkApps .refl ?_, .inr (.intro hp hc ht hm')⟩
      apply List.forall₂_map_left_iff.mpr
      apply List.forall₂_map_right_iff.mpr
      exact Lean4Lean.List.Forall₂.rfl (fun i _ => HR i)

end Lean4Lean.VEnv.Strengthening
