import Lean4Lean.Theory.Typing.AnchoredTracePrefix
import Lean4Lean.Theory.Typing.AnchoredExposureTransport

/-! Code expansion through a concrete proof-generating trace. Future worlds
rename the original generated frame, retaining its inhabitants and every
chosen Pi display. This theorem does not assert term/function expansion. -/

namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles InductiveSignature.NativeRecursorData
set_option backward.isDefEq.respectTransparency false

private theorem frontMap (ρ : Lift) (front : List VExpr) :
    (Lift.skipN .refl front.length).comp (ρ.consN front.length) =
      ρ.comp (.skipN .refl (renameAdded ρ front).length) := by
  simp only [renameAdded_length, Lift.skipN_comp_consN, Lift.refl_comp,
    Lift.comp_skipN, Lift.comp]

private theorem path_future
    {env : VEnv} {U : Nat} {Γ Δ front : List VExpr}
    {expression result : VExpr} {ρ : Lift}
    (henv : env.Ordered)
    (path : TypeConversion env U (front ++ Γ)
      (expression.lift' (.skipN .refl front.length)) result)
    (future : FutureInsertion env U (front ++ Γ) (renameAdded ρ front ++ Δ)
      (ρ.consN front.length)) :
    TypeConversion env U (renameAdded ρ front ++ Δ)
      ((expression.lift' ρ).lift' (.skipN .refl (renameAdded ρ front).length))
      (result.lift' (ρ.consN front.length)) := by
  simpa only [← lift'_comp, frontMap] using path.weak' henv future.weakening

theorem TypeRelated.prependTrace
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {Γ front : List VExpr} {left right leftResult rightResult : VExpr}
    {profile : Profile n}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (leftTrace : CanonicalDataHead.Trace registry left front leftResult)
    (rightTrace : CanonicalDataHead.Trace registry right front rightResult)
    (generated : ProofInsertion env U Γ (front ++ Γ) (.skipN .refl front.length))
    (leftPath : TypeConversion env U (front ++ Γ)
      (left.lift' (.skipN .refl front.length)) leftResult)
    (rightPath : TypeConversion env U (front ++ Γ)
      (right.lift' (.skipN .refl front.length)) rightResult)
    (related : TypeRelated env U registry (front ++ Γ) leftResult rightResult
      (profile.rename (.skipN .refl front.length))) :
    TypeRelated env U registry Γ left right profile := by
  induction n generalizing Γ front left right leftResult rightResult with
  | zero =>
    intro Δ ρ future atom member
    obtain ⟨newGenerated, extended⟩ := generated.renameFront front future henv
    have leftPath' := path_future henv leftPath extended
    have rightPath' := path_future henv rightPath extended
    have result := related _ _ extended
    rw [← Profile.rename_comp, frontMap, Profile.rename_comp] at result
    have member' : atom ∈ ((profile.rename ρ).rename
        (.skipN .refl (renameAdded ρ front).length)).atoms := by
      simpa [Profile.rename, Profile.atoms, Atom.rename] using member
    exact SortRelated.prependTrace henv (leftTrace.rename hscoped ρ)
      (rightTrace.rename hscoped ρ)
      (by simpa only [renameAdded_length] using newGenerated)
      leftPath' rightPath' (result atom member')
  | succ n ih =>
    intro Δ ρ future atom member
    obtain ⟨newGenerated, extended⟩ := generated.renameFront front future henv
    have leftPath' := path_future henv leftPath extended
    have rightPath' := path_future henv rightPath extended
    have result := related _ _ extended
    rw [← Profile.rename_comp, frontMap, Profile.rename_comp] at result
    have member' : atom.rename (.skipN .refl (renameAdded ρ front).length) ∈
        ((profile.rename ρ).rename (.skipN .refl (renameAdded ρ front).length)).atoms :=
      List.mem_map.mpr ⟨atom, member, rfl⟩
    have value := result _ member'
    have generated' : ProofInsertion env U Δ (renameAdded ρ front ++ Δ)
        (.skipN .refl (renameAdded ρ front).length) := by
      simpa only [renameAdded_length] using newGenerated
    cases atom with
    | sort flag =>
      exact SortRelated.prependTrace henv (leftTrace.rename hscoped ρ)
        (rightTrace.rename hscoped ρ) generated' leftPath' rightPath' value
    | fn | ctor | record => exact value.elim
    | family demand =>
      obtain ⟨display⟩ := value
      exact ⟨display.prependTrace henv (leftTrace.rename hscoped ρ)
        (rightTrace.rename hscoped ρ) generated' leftPath' rightPath'⟩
    | pi A B domain rows =>
      obtain ⟨display⟩ := value
      exact ⟨display.prependTrace henv (leftTrace.rename hscoped ρ)
        (rightTrace.rename hscoped ρ) generated' leftPath' rightPath'⟩
    | pad atom =>
      change TypeRelated env U registry (renameAdded ρ front ++ Δ)
        (leftResult.lift' (ρ.consN front.length)) (rightResult.lift' (ρ.consN front.length))
        (.singleton (atom.rename (.skipN .refl (renameAdded ρ front).length))) at value
      rw [← Profile.rename_singleton] at value
      exact ih (leftTrace.rename hscoped ρ) (rightTrace.rename hscoped ρ)
        generated' leftPath' rightPath' value

end Lean4Lean.AnchoredSemantics
