import Lean4Lean.Theory.Typing.AnchoredLive
import Lean4Lean.Theory.Typing.AnchoredFramedApplication

/-! Actual term relations supply every finite function anchor needed for
source substitution. The private assigned type is never retracted: only the
finite profiles and their hereditary anchor admissions descend to the base. -/

namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles
set_option backward.isDefEq.respectTransparency false

theorem Related.atom_live_inFrame
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {Γ Δ : List VExpr} {ρ : Lift} {left right type : VExpr}
    {atom : Atom n} {support : Profile n}
    (frame : ProofInsertion env U Γ Δ ρ)
    (related : Related env U registry Δ left right type
      (.singleton (atom.rename ρ)) (support.rename ρ)) :
    Atom.Live env U registry Γ atom := by
  induction n generalizing Γ Δ ρ left right type with
  | zero => trivial
  | succ n ih =>
    cases atom with
    | sort | pi | family | ctor | record => trivial
    | fn key output =>
      refine ⟨related.fn_seed_inFrame henv hscoped frame, ?_⟩
      obtain ⟨Ω, τ, insertion, l, r, A, result, outputRelated⟩ :=
        related.fn_output_inFrame henv frame
      exact ih insertion outputRelated
    | pad lower =>
      have original := related (.pad (lower.rename ρ)) (List.mem_singleton_self _)
        Δ .refl (.refl (frame.targetWF henv))
      simp only [lift'_refl, Profile.rename_refl] at original
      rcases original with empty | ⟨Ω, τ, insertion, _, _, values⟩
      · cases empty
      · have output := values (.pad ((lower.rename ρ).rename τ)) (List.mem_singleton_self _)
        apply ih (frame.comp insertion henv)
        simpa only [← Profile.rename_comp, ← Atom.rename_comp, Profile.down_rename,
          Related, TermAtom] using output

theorem Related.live_inFrame
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {Γ Δ : List VExpr} {ρ : Lift} {left right type : VExpr}
    {value support : Profile n}
    (frame : ProofInsertion env U Γ Δ ρ)
    (related : Related env U registry Δ left right type (value.rename ρ) (support.rename ρ)) :
    Profile.Live env U registry Γ value := by
  intro atom member
  exact (related.singleton_of_mem (List.mem_map_of_mem member)).atom_live_inFrame
    henv hscoped frame

theorem Related.live
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {Γ : List VExpr} {left right type : VExpr} {value support : Profile n}
    (hΓ : OnCtx Γ (env.IsType U))
    (related : Related env U registry Γ left right type value support) :
    Profile.Live env U registry Γ value := by
  apply Related.live_inFrame henv hscoped (.refl hΓ)
  simpa only [Profile.rename_refl] using related

end Lean4Lean.AnchoredSemantics
