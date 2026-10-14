import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrefixTelescope
import Lean4Lean.Theory.Typing.PrefixUnfolding.Layout

/-! # Opening erased residual telescopes

The raw context determines whether a variable is a proof in any well-formed
realization. This semantic selector is independent of the chosen realization;
it does not assert an executable test for propositionhood. It gives a uniform
opened provider vector for generated singleton prefixes.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params InductiveSignature Classical
variable [Params]

namespace ProofShape
/-- Variable erasure determined by a raw context. Existence of a proof in a
well-formed realization is invariant under changing that realization. -/
noncomputable def contextVariable (Δ : List ProofShape) (i : Nat) : ProofShape :=
  if ∃ Γ, OnCtx Γ (env.IsType univs) ∧ proofEraseCtx Γ = Δ ∧ IsProof Γ (.bvar i)
  then .proof else .bvar i

/-- Fresh variables in binder order, with proof markers selected by the context. -/
noncomputable def contextVars (Δ : List ProofShape) (count below : Nat) : List ProofShape :=
  (List.range count).reverse.map fun i => contextVariable Δ (below + i)

/-- Open a raw supplied prefix beneath a residual telescope. -/
noncomputable def openPrefixArguments (Δ domains args : List ProofShape) : List ProofShape :=
  args.map (·.liftN domains.length) ++ contextVars (domains.reverse ++ Δ) domains.length 0
end ProofShape

/-- Every well-formed realization gives the same exact erased variable,
including when the variable is a proof. -/
theorem proofErase_contextVariable (hΓ : OnCtx Γ (env.IsType univs)) :
    proofErase Γ (.bvar i) = ProofShape.contextVariable (proofEraseCtx Γ) i := by
  have hp : (∃ Γ', OnCtx Γ' (env.IsType univs) ∧ proofEraseCtx Γ' = proofEraseCtx Γ ∧
      IsProof Γ' (.bvar i)) ↔ IsProof Γ (.bvar i) := by
    constructor
    · rintro ⟨Γ', hΓ', he, hp⟩
      exact (isProof_defeqCtx (proofEraseCtx_defeq hΓ' hΓ he)).1 hp
    · intro hp
      exact ⟨Γ, hΓ, rfl, hp⟩
  simp only [proofErase, ProofShape.contextVariable, hp]

/-- The fresh suffix erases solely from its raw context and index range. -/
theorem proofErase_contextVars (hΓ : OnCtx Γ (env.IsType univs)) :
    (vars count below).map (proofErase Γ) =
      ProofShape.contextVars (proofEraseCtx Γ) count below := by
  simp only [vars, ProofShape.contextVars, List.map_map, Function.comp_def,
    proofErase_contextVariable hΓ]

/-- The exact opened provider vector of a typed generated prefix is determined
by its raw ambient context, residual annotations, and supplied arguments. -/
theorem proofErase_singleton_prefix_arguments (hΓ : OnCtx Γ (env.IsType univs))
    (H : RecursorRegistered env data) (hw : ∀ l ∈ levels, l.WF univs)
    (hg : data.singletonUnfolding env univs levels args = some program)
    (ht : VExpr.WF env univs Γ (mkApps (.const data.name levels) args)) :
    (data.openedArguments args).map (proofErase (program.domains.reverse ++ Γ)) =
      ProofShape.openPrefixArguments (proofEraseCtx Γ)
        (proofEraseDomains Γ program.domains) (args.map (proofErase Γ)) := by
  have hctx := ((H.prefixType henv hΓ hw hg ht).etaOpen_wf henv.ordered hΓ).1
  obtain ⟨_, _, _, _, hlen, _, _⟩ := RecursorData.singletonUnfolding_layout hg
  have W : Ctx.LiftN program.domains.length 0 Γ (program.domains.reverse ++ Γ) := by
    exact Ctx.LiftN.zero program.domains.reverse (by simp only [List.length_reverse])
  have hargs := (mkApps_arguments_wf henv hΓ ht).2
  have hm : (args.map (fun a => a.liftN program.domains.length)).map
      (proofErase (program.domains.reverse ++ Γ)) =
      (args.map (proofErase Γ)).map (·.liftN program.domains.length) := by
    simp only [List.map_map]
    apply List.map_congr_left
    intro a ha
    obtain ⟨T, hT⟩ := hargs a ha
    exact proofErase_liftN hΓ hctx W hT
  simp only [RecursorData.openedArguments, ← hlen, List.map_append,
    hm, proofErase_contextVars hctx, proofEraseDomains_context,
    ProofShape.openPrefixArguments, proofEraseDomains_length]

/-- Equal erased inputs in the same raw ambient context give equal opened
provider vectors, even when the original residual telescopes differ. -/
theorem proofErase_singleton_prefix_arguments_congr
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (H : RecursorRegistered env data) (hw : ∀ l ∈ levels, l.WF univs)
    (hrec : data.recursorType = some recType)
    (hg : data.singletonUnfolding env univs levels args = some program)
    (hg' : data.singletonUnfolding env univs levels args' = some program')
    (ht : VExpr.WF env univs Γ (mkApps (.const data.name levels) args))
    (ht' : VExpr.WF env univs Γ' (mkApps (.const data.name levels) args'))
    (hctx : proofEraseCtx Γ = proofEraseCtx Γ')
    (ha : args.map (proofErase Γ) = args'.map (proofErase Γ')) :
    (data.openedArguments args).map (proofErase (program.domains.reverse ++ Γ)) =
      (data.openedArguments args').map (proofErase (program'.domains.reverse ++ Γ')) := by
  rw [proofErase_singleton_prefix_arguments hΓ H hw hg ht,
    proofErase_singleton_prefix_arguments hΓ' H hw hg' ht', hctx, ha,
    (proofErase_singleton_prefix_telescope_congr hΓ hΓ' H hw hrec hg hg' ht ht' ha).1]

end Lean4Lean.VEnv.Strengthening
