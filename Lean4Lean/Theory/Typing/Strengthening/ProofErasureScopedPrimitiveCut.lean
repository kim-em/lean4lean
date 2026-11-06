import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypedComputeSubstitution

/-! # A first primitive outside a chosen computation fragment

The decomposition retains a complete prefix in the smaller fragment, the exact
hole context and root step, and a complete suffix in the original relation.
Binder bodies are processed before their annotations, preserving their actual
source contexts without assuming context conversion for either relation.
-/
namespace Lean4Lean.VEnv.Strengthening.ProofShape

/-- A single computation hole with its exact ambient context. -/
inductive ScopedHole : List ProofShape → List ProofShape → Type where
  | hole : ScopedHole Δ Δ
  | appFn : ScopedHole Δ Θ → ProofShape → ScopedHole Δ Θ
  | appArg : ProofShape → ScopedHole Δ Θ → ScopedHole Δ Θ
  | proj : Name → Nat → ScopedHole Δ Θ → ScopedHole Δ Θ
  | lamDomain : ScopedHole Δ Θ → ProofShape → ScopedHole Δ Θ
  | lamBody (A : ProofShape) : ScopedHole (A :: Δ) Θ → ScopedHole Δ Θ
  | piDomain : ScopedHole Δ Θ → ProofShape → ScopedHole Δ Θ
  | piBody (A : ProofShape) : ScopedHole (A :: Δ) Θ → ScopedHole Δ Θ

/-- Fill the distinguished hole without substituting beneath its binders. -/
def ScopedHole.plug : ScopedHole Δ Θ → ProofShape → ProofShape
  | .hole, e => e
  | .appFn C a, e => .app (C.plug e) a
  | .appArg f C, e => .app f (C.plug e)
  | .proj s i C, e => .proj s i (C.plug e)
  | .lamDomain C b, e => .lam (C.plug e) b
  | .lamBody A C, e => .lam A (C.plug e)
  | .piDomain C b, e => .forallE (C.plug e) b
  | .piBody A C, e => .forallE A (C.plug e)

/-- Any compatible computation can be lifted through the retained hole. -/
theorem ScopedHole.compute (C : ScopedHole Δ Θ) (R : ScopedCompute Step Θ a b) :
    ScopedCompute Step Δ (C.plug a) (C.plug b) := by
  induction C with
  | hole => exact R
  | appFn _ _ ih => exact .app (ih R) .refl
  | appArg _ _ ih => exact .app .refl (ih R)
  | proj _ _ _ ih => exact .proj (ih R)
  | lamDomain _ _ ih => exact .lam (ih R) .refl
  | lamBody _ _ ih => exact .lam .refl (ih R)
  | piDomain _ _ ih => exact .forallE (ih R) .refl
  | piBody _ _ ih => exact .forallE .refl (ih R)

/-- Either every needed root belongs to the target fragment, or one can
choose an escaping root with a target-only prefix and the original full tail.
No inclusion, substitution closure, typing or confluence premise is used. -/
theorem ScopedCompute.fragment_or_cut (R : ScopedCompute Source Δ e out) :
    ScopedCompute Target Δ e out ∨
      ∃ Θ a b, ∃ C : ScopedHole Δ Θ, ScopedCompute Target Δ e (C.plug a) ∧
        Source Θ a b ∧ ¬ Target Θ a b ∧ ScopedCompute Source Δ (C.plug b) out := by
  classical
  induction R with
  | @base Δ e out H =>
    by_cases HT : Target Δ e out
    · exact .inl (.base HT)
    · exact .inr ⟨_, _, _, .hole, .refl, H, HT, .refl⟩
  | beta R => exact .inl (.beta R)
  | trans R₁ R₂ ih₁ ih₂ =>
    rcases ih₁ with R₁' | ⟨Θ, a, b, C, RP, H, HN, RT⟩
    · rcases ih₂ with R₂' | ⟨Θ, a, b, C, RP, H, HN, RT⟩
      · exact .inl (R₁'.trans R₂')
      · exact .inr ⟨Θ, a, b, C, R₁'.trans RP, H, HN, RT⟩
    · exact .inr ⟨Θ, a, b, C, RP, H, HN, RT.trans R₂⟩
  | @app Δ f f' x x' RF RX ihf ihx =>
    rcases ihf with RF' | ⟨Θ, a, b, C, RP, H, HN, RT⟩
    · rcases ihx with RX' | ⟨Θ, a, b, C, RP, H, HN, RT⟩
      · exact .inl (.app RF' RX')
      · exact .inr ⟨Θ, a, b, .appArg f' C, .app RF' RP, H, HN, .app .refl RT⟩
    · exact .inr ⟨Θ, a, b, .appFn C x, .app RP .refl, H, HN, .app RT RX⟩
  | @proj Δ m m' s i R ih =>
    rcases ih with R' | ⟨Θ, a, b, C, RP, H, HN, RT⟩
    · exact .inl (.proj R')
    · exact .inr ⟨Θ, a, b, .proj s i C, .proj RP, H, HN, .proj RT⟩
  | @lam Δ A A' body body' RA RB ihA ihB =>
    rcases ihB with RB' | ⟨Θ, a, b, C, RP, H, HN, RT⟩
    · rcases ihA with RA' | ⟨Θ, a, b, C, RP, H, HN, RT⟩
      · exact .inl (.lam RA' RB')
      · exact .inr ⟨Θ, a, b, .lamDomain C body', .lam RP RB', H, HN, .lam RT .refl⟩
    · exact .inr ⟨Θ, a, b, .lamBody A C, .lam .refl RP, H, HN, .lam RA RT⟩
  | @forallE Δ A A' body body' RA RB ihA ihB =>
    rcases ihB with RB' | ⟨Θ, a, b, C, RP, H, HN, RT⟩
    · rcases ihA with RA' | ⟨Θ, a, b, C, RP, H, HN, RT⟩
      · exact .inl (.forallE RA' RB')
      · exact .inr ⟨Θ, a, b, .piDomain C body', .forallE RP RB', H, HN, .forallE RT .refl⟩
    · exact .inr ⟨Θ, a, b, .piBody A C, .forallE .refl RP, H, HN, .forallE RA RT⟩

end Lean4Lean.VEnv.Strengthening.ProofShape

namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private erase_app_inv erase_proj_inv erase_lam_inv erase_forallE_inv
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
variable [Params]

/-- A typed plugged expression supplies an actual typed source for the hole,
including the precise source annotations of every enclosing binder. -/
theorem ProofShape.ScopedHole.typed (C : ScopedHole Δ Θ) (HT : TypedSource Δ (C.plug a)) :
    TypedSource Θ a := by
  induction C with
  | hole => exact HT
  | appFn C x ih =>
    obtain ⟨Γ, e, T, hΓ, EΓ, ht, Ee⟩ := HT
    obtain ⟨f, x, rfl, _, Ef, _⟩ := erase_app_inv Ee
    obtain ⟨_, _, hf, _⟩ := ht.app_inv henv hΓ
    exact ih ⟨Γ, f, _, hΓ, EΓ, hf, Ef⟩
  | appArg f C ih =>
    obtain ⟨Γ, e, T, hΓ, EΓ, ht, Ee⟩ := HT
    obtain ⟨f, x, rfl, _, _, Ex⟩ := erase_app_inv Ee
    obtain ⟨_, _, _, hx⟩ := ht.app_inv henv hΓ
    exact ih ⟨Γ, x, _, hΓ, EΓ, hx, Ex⟩
  | proj s i C ih =>
    obtain ⟨Γ, e, T, hΓ, EΓ, ht, Ee⟩ := HT
    obtain ⟨m, rfl, _, Em⟩ := erase_proj_inv Ee
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ := ht.proj_inv henv hΓ
    exact ih ⟨Γ, m, _, hΓ, EΓ, hm.hasType.2, Em⟩
  | lamDomain C b ih =>
    obtain ⟨Γ, e, T, hΓ, EΓ, ht, Ee⟩ := HT
    obtain ⟨A, b, rfl, _, EA, _⟩ := erase_lam_inv Ee
    obtain ⟨⟨u, hA⟩, _, _⟩ := ht.lam_inv henv hΓ
    exact ih ⟨Γ, A, _, hΓ, EΓ, hA, EA⟩
  | lamBody A C ih =>
    obtain ⟨Γ, e, T, hΓ, EΓ, ht, Ee⟩ := HT
    obtain ⟨A₀, b, rfl, _, EA, Eb⟩ := erase_lam_inv Ee
    obtain ⟨⟨u, hA⟩, _, hb⟩ := ht.lam_inv henv hΓ
    exact ih ⟨A₀ :: Γ, b, _, ⟨hΓ, u, hA⟩, by simp only [proofEraseCtx, EA, EΓ], hb, Eb⟩
  | piDomain C b ih =>
    obtain ⟨Γ, e, T, hΓ, EΓ, ht, Ee⟩ := HT
    obtain ⟨A, b, rfl, _, EA, _⟩ := erase_forallE_inv Ee
    obtain ⟨⟨u, hA⟩, _, _⟩ := ht.forallE_inv henv
    exact ih ⟨Γ, A, _, hΓ, EΓ, hA, EA⟩
  | piBody A C ih =>
    obtain ⟨Γ, e, T, hΓ, EΓ, ht, Ee⟩ := HT
    obtain ⟨A₀, b, rfl, _, EA, Eb⟩ := erase_forallE_inv Ee
    obtain ⟨⟨u, hA⟩, _, hb⟩ := ht.forallE_inv henv
    exact ih ⟨A₀ :: Γ, b, _, ⟨hΓ, u, hA⟩, by simp only [proofEraseCtx, EA, EΓ], hb, Eb⟩

/-- Replay only the target-fragment prefix to type the escaping occurrence.
No replay of the larger source relation or chosen root is required. -/
theorem ProofShape.ScopedCompute.typed_fragment_or_cut
    (hTarget : ErasedScopedPrimitiveDescent Target)
    (R : ScopedCompute Source Δ e out) (HT : TypedSource Δ e) :
    ScopedCompute Target Δ e out ∨
      ∃ Θ a b, ∃ C : ScopedHole Δ Θ, ScopedCompute Target Δ e (C.plug a) ∧
        TypedSource Θ a ∧ Source Θ a b ∧ ¬ Target Θ a b ∧
        ScopedCompute Source Δ (C.plug b) out := by
  rcases R.fragment_or_cut with H | ⟨Θ, a, b, C, RP, H, HN, RT⟩
  · exact .inl H
  · obtain ⟨Γ, e₀, T, hΓ, EΓ, ht, Ee⟩ := HT
    obtain ⟨e', HE, EE⟩ := proofErase_scoped_compute_realize hTarget hΓ ht EΓ Ee RP
    exact .inr ⟨Θ, a, b, C, RP, C.typed ⟨Γ, e', T, hΓ, EΓ, HE.hasType.2, EE⟩, H, HN, RT⟩

end Lean4Lean.VEnv.Strengthening
