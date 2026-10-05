import Lean4Lean.Theory.Typing.AnchoredFunctionFuture
import Lean4Lean.Theory.Typing.AnchoredFrame

/-! Introduce the actual per-atom, future, proof-saturated term relation from
one checked function behavior and its actual type capability. -/

namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles
set_option backward.isDefEq.respectTransparency false

theorem Related.function
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {Γ : List VExpr} {left right type : VExpr}
    {key : Key n} {output : Atom n} {support : Profile (n + 1)}
    (typed : (Profile.fn key output).HasType support)
    (code : TypeRelated env U registry Γ type type support)
    (behavior : FunctionBehavior env U registry (relations env U registry n)
      Γ left right type key output support) :
    Related env U registry Γ left right type (Profile.fn key output) support := by
  intro requested hm
  have he : requested = AtomData.fn key output := List.mem_singleton.mp hm
  subst requested
  intro Δ ρ future
  have typed' := (Profile.rename_hasType_iff (ρ := ρ)).mpr typed
  have code' := code.future henv future
  have behavior' := behavior.future henv hscoped future
  refine .inr ⟨Δ, .refl, .refl (future.targetWF henv), ?_, ?_, ?_⟩
  · simpa only [Profile.rename_refl, Profile.fn] using typed'
  · change TypeRelated env U registry Δ ((type.lift' ρ).lift' .refl)
      ((type.lift' ρ).lift' .refl) ((support.rename ρ).rename .refl)
    simpa only [lift'_refl, Profile.rename_refl] using code'
  · intro atom ha
    simp only [Profile.rename_singleton] at ha
    cases List.mem_singleton.mp ha
    simp only [lift'_refl, Profile.rename_refl, Atom.rename_refl]
    change FunctionBehavior env U registry (relations env U registry n) Δ
      (left.lift' ρ) (right.lift' ρ) (type.lift' ρ) (key.rename ρ)
      (output.rename ρ) (support.rename ρ)
    exact behavior'

end Lean4Lean.AnchoredSemantics
