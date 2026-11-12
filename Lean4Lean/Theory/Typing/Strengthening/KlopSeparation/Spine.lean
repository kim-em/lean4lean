import Lean4Lean.Theory.Typing.Strengthening.KlopSeparation.SoundEta

/-! # The head invariant on constant-headed application spines

`Chain env ρ w e o`: the semantic type `o` tracked along the application spine `e` of a
constant, starting from the denotation of the constant's declared type and following each
argument through a non-collapsed Π-type (`tPi` or `tPiP`); `none` once the type has collapsed
to a proposition. Each tracked step records that the argument is an element of the domain
(`tPi`) or that its value realizes the proposition domain (`tPiP`).

`SpineOK env ρ w e A`: if `e` is a constant-headed spine, it has a chain whose tracked type,
when present, is the denotation of the stated type `A`. This is the head invariant of
`FIRST_PRINCIPLES.md` §26, needed for the ι rule of `Eq.rec`. Only constant heads are needed:
the strong β rule carries the typing of its contractum as a premise.

This file proves the invariant for the application and constant rules; the other rules take
both sides from their premises or are not spines.
-/

namespace Lean4Lean
namespace VEnv.Strengthening

open Classical

/-- A constant applied to arguments. -/
def IsSpine : VExpr → Prop
  | .const _ _ => True
  | .app f _ => IsSpine f
  | _ => False

namespace SetModel
variable {𝕋 : SetModel}

local infix:50 " ∈ₛ " => 𝕋.mem

/-- The tracked semantic type of a constant-headed spine. -/
inductive Chain (𝕋 : SetModel) (env : VEnv) (ρ : Nat → 𝕋.S) (w : Nat → PVal) :
    VExpr → Option 𝕋.S → Prop where
  | const {c : Name} {ci : VConstant} {ls : List VLevel} : env.constants c = some ci →
      Chain 𝕋 env ρ w (.const c ls) (some (𝕋.den ρ (ci.type.instL ls)))
  | appPi {f x : VExpr} {D : 𝕋.S} {F : 𝕋.S → 𝕋.S} : Chain 𝕋 env ρ w f (some (𝕋.tPi D F)) →
      𝕋.mem (𝕋.den ρ x) (𝕋.El D) → Chain 𝕋 env ρ w (.app f x) (some (F (𝕋.den ρ x)))
  | appPiP {f x : VExpr} {c : Candidate} {B : 𝕋.S} :
      Chain 𝕋 env ρ w f (some (𝕋.tPiP c B)) → c.mem ((pval x).subst w) →
      𝕋.den ρ x = 𝕋.star → Chain 𝕋 env ρ w (.app f x) (some B)
  | appStop {f x : VExpr} {R : 𝕋.S} : Chain 𝕋 env ρ w f (some R) → 𝕋.IsCand R →
      Chain 𝕋 env ρ w (.app f x) none
  | appNone {f x : VExpr} : Chain 𝕋 env ρ w f none → Chain 𝕋 env ρ w (.app f x) none

/-- The head invariant for one side of a judgment. -/
def SpineOK (𝕋 : SetModel) (env : VEnv) (ρ : Nat → 𝕋.S) (w : Nat → PVal)
    (e A : VExpr) : Prop :=
  IsSpine e → ∃ o, 𝕋.Chain env ρ w e o ∧ ∀ R, o = some R → R = 𝕋.den ρ A

variable {env : VEnv} {ρ : Nat → 𝕋.S} {w : Nat → PVal}

theorem spineOK_of_not_spine {e A : VExpr} (h : ¬ IsSpine e) : 𝕋.SpineOK env ρ w e A :=
  fun hs => (h hs).elim

/-- Conversion: the stated type may be replaced by one with the same denotation. -/
theorem SpineOK.defeq {e A B : VExpr} (H : 𝕋.SpineOK env ρ w e A)
    (h : 𝕋.den ρ A = 𝕋.den ρ B) : 𝕋.SpineOK env ρ w e B := by
  intro hs
  obtain ⟨o, hc, hcl⟩ := H hs
  exact ⟨o, hc, fun R hR => h ▸ hcl R hR⟩

/-- The constant rule. -/
theorem spineOK_const {c : Name} {ci : VConstant} {ls : List VLevel}
    (h : env.constants c = some ci) :
    𝕋.SpineOK env ρ w (.const c ls) (ci.type.instL ls) :=
  fun _ => ⟨_, .const h, fun R hR => (Option.some.inj hR).symm⟩

/-- The application rule. -/
theorem SpineOK.app {f a A B : VExpr} (Hf : 𝕋.SpineOK env ρ w f (.forallE A B))
    (ham : 𝕋.mem (𝕋.den ρ a) (𝕋.El (𝕋.den ρ A)))
    (hav : 𝕋.IsCand (𝕋.den ρ A) → (𝕋.candOf (𝕋.den ρ A)).mem ((pval a).subst w)) :
    𝕋.SpineOK env ρ w (.app f a) (B.inst a) := by
  intro hs
  obtain ⟨o, hc, hcl⟩ := Hf hs
  cases o with
  | none => exact ⟨none, .appNone hc, fun R hR => nomatch hR⟩
  | some R =>
    have hR : R = 𝕋.mkPi (𝕋.den ρ A) fun d => 𝕋.den (𝕋.cons d ρ) B := hcl R rfl
    subst hR
    have hinst : 𝕋.den ρ (B.inst a) = 𝕋.den (𝕋.cons (𝕋.den ρ a) ρ) B := 𝕋.den_inst0 ..
    unfold mkPi at hc
    by_cases hDc : 𝕋.IsCand (𝕋.den ρ A)
    · rw [if_pos hDc] at hc
      have hDeq := isCand_eq hDc
      have hxs : 𝕋.den ρ a = 𝕋.star := by rw [hDeq] at ham; exact (𝕋.mem_El_cand.1 ham).1
      have hne : ∃ v, (𝕋.candOf (𝕋.den ρ A)).mem v := by
        rw [hDeq] at ham; exact (𝕋.mem_El_cand.1 ham).2
      rw [if_pos hne] at hc
      by_cases hFc : 𝕋.IsCand (𝕋.den (𝕋.cons 𝕋.star ρ) B)
      · rw [if_pos hFc] at hc
        exact ⟨none, .appStop hc ⟨_, rfl⟩, fun R hR => nomatch hR⟩
      · rw [if_neg hFc] at hc
        refine ⟨_, .appPiP hc (hav hDc) hxs, fun R hR => ?_⟩
        rw [← Option.some.inj hR, hinst, hxs]
    · rw [if_neg hDc] at hc
      by_cases hall : ∀ d, d ∈ₛ 𝕋.El (𝕋.den ρ A) → 𝕋.IsCand (𝕋.den (𝕋.cons d ρ) B)
      · rw [if_pos hall] at hc
        exact ⟨none, .appStop hc ⟨_, rfl⟩, fun R hR => nomatch hR⟩
      · rw [if_neg hall] at hc
        refine ⟨_, .appPi hc ham, fun R hR => ?_⟩
        rw [← Option.some.inj hR, hinst]

end SetModel
end VEnv.Strengthening
end Lean4Lean
