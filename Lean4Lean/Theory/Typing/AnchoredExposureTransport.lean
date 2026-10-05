import Lean4Lean.Theory.Typing.AnchoredSemantics
import Lean4Lean.Theory.Typing.DependentTypeConversion

/-! Forward transport of canonical exposures along generated future worlds.
The trace telescope is renamed literally, including every fresh proof slot.
Its inhabitants are transported by typed weakening, and the final private
proof insertion is pushed forward using the generated insertion histories.
No semantic relation or arbitrary split embedding is a premise.
-/

namespace Lean4Lean.VEnv
open VExpr InductiveSignature.NativeRecursorData

private theorem proofSkip_inv
    {env : VEnv} {U : Nat} {Γ Δ : List VExpr} {ρ : Lift} {P : VExpr}
    (H : ProofInsertion env U Γ (P :: Δ) ρ.skip) :
    ∃ q, ProofInsertion env U Γ Δ ρ ∧
      env.HasType U Δ P (.sort .zero) ∧ env.HasType U Δ q P := by
  cases H with
  | skip previous hP hq => exact ⟨_, previous, hP, hq⟩

/-- Rename a front proof telescope, retaining its fresh binders while moving
the base context forward. Both resulting legs retain generated histories. -/
theorem ProofInsertion.renameFront
    {env : VEnv} {U : Nat} {Γ Δ : List VExpr} {ρ : Lift}
    (added : List VExpr)
    (H : ProofInsertion env U Γ (added ++ Γ) (.skipN .refl added.length))
    (K : FutureInsertion env U Γ Δ ρ) (henv : env.Ordered) :
    ProofInsertion env U Δ (renameAdded ρ added ++ Δ) (.skipN .refl added.length) ∧
    FutureInsertion env U (added ++ Γ) (renameAdded ρ added ++ Δ)
      (ρ.consN added.length) := by
  induction added with
  | nil => exact ⟨.refl (K.targetWF henv), K⟩
  | cons P rest ih =>
    change ProofInsertion env U Γ (P :: (rest ++ Γ))
      (.skip (.skipN .refl rest.length)) at H
    obtain ⟨q, previous, hP, hq⟩ := proofSkip_inv H
    obtain ⟨hi, hj⟩ := ih previous
    exact ⟨hi.skip (hP.weak' henv hj.weakening) (hq.weak' henv hj.weakening),
      hj.cons hP⟩

end Lean4Lean.VEnv

namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv InductiveSignature.NativeRecursorData

/-- Future worlds transport the whole concrete exposure. The result uses the
renamed trace telescope and an actually generated post-insertion, and the
final future leg commutes literally with the original exposure map. -/
theorem Exposure.future
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {Γ Δ Ω : List VExpr} {expression head : VExpr} {map τ : Lift}
    (E : Exposure env U registry Γ expression Ω map head)
    (K : FutureInsertion env U Γ Δ τ)
    (henv : env.Ordered) (hscoped : registry.Scoped) :
    ∃ Ω' map' j, FutureInsertion env U Ω Ω' j ∧ map.comp j = τ.comp map' ∧
      Nonempty (Exposure env U registry Δ (expression.lift' τ) Ω' map' (head.lift' j)) := by
  obtain ⟨hg, hk⟩ := E.generated.renameFront E.added K henv
  obtain ⟨postContext, i, j, hi, hj, he⟩ := E.post.pushout hk henv
  obtain ⟨Ω', finalFuture, terminal⟩ := E.terminal.pushFuture henv hj
  let map' := (Lift.skipN .refl E.added.length).comp i
  have hmap : map.comp j = τ.comp map' := by
    rw [← E.map_eq, Lift.comp_assoc, he, ← Lift.comp_assoc,
      Lift.skipN_comp_consN, Lift.refl_comp]
    dsimp only [map']
    rw [← Lift.comp_assoc, Lift.comp_skipN]
    rfl
  refine ⟨Ω', map', j, finalFuture, hmap, ⟨{
    added := renameAdded τ E.added
    result := E.result.lift' (τ.consN E.added.length)
    postMap := i
    trace := E.trace.rename hscoped τ
    generated := ?_
    postContext := postContext
    post := hi
    terminal := terminal
    map_eq := ?_
    result_eq := ?_
    sound := ?_
    headType := ?_
  }⟩⟩
  · simpa only [renameAdded_length] using hg
  · simp only [renameAdded_length]
    rfl
  · rw [← lift'_comp, ← he, lift'_comp, E.result_eq]
  · simpa only [← lift'_comp, hmap] using E.sound.weak' henv finalFuture.weakening
  · obtain ⟨u, hs⟩ := E.headType
    exact ⟨u, by simpa only [lift'] using hs.weak' henv finalFuture.weakening⟩

end Lean4Lean.AnchoredSemantics
