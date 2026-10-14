import Lean4Lean.Theory.Typing.Strengthening.ProofErasureComparedK
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureBetaForward

/-! # Forward simulation of visible registered pattern instances

At a non-proof core iota redex the major cannot be a proof: the original
universe guard excludes precisely that case. Thus its full match survives
erasure, including proof-valued captures.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
open PureObservation (Definitions PatternCompute CheckFromTyping)
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
variable [Params]

private theorem matches_captures_congr {p : Pattern} {e : ProofShape} {ls : List VLevel}
    {c d : p.Path → ProofShape} (H : ProofShape.Matches p e ls c) (he : ∀ i, c i = d i) :
    ProofShape.Matches p e ls d := (funext he) ▸ H

/-- A typed non-proof constant spine retains its entire visible pattern match. -/
theorem proofErase_varN_match (hΓ : OnCtx Γ (env.IsType univs))
    (hm : ((Pattern.const c).varN n).Matches e ls captures)
    (ht : env.HasType univs Γ e T) (hn : ¬ IsProof Γ e) :
    ProofShape.Matches ((Pattern.const c).varN n) (proofErase Γ e) ls
      (fun i => proofErase Γ (captures i)) := by
  induction n generalizing e T with
  | zero =>
    cases hm
    simp only [proofErase, if_neg hn]
    exact matches_captures_congr .const nofun
  | succ n ih =>
    cases hm with
    | var hm =>
      obtain ⟨_, _, hf, ha⟩ := ht.app_inv henv hΓ
      simp only [proofErase, if_neg hn]
      apply matches_captures_congr (.var (ih hm hf (not_isProof_fn hΓ hf ha hn)))
      intro i
      cases i <;> rfl

/-- Every enabled core pattern at a non-proof source has a visible erased match.
For iota, the actual rule guard forces the major to be non-proof as well. -/
theorem proofErase_pattern_match_forward (hΓ : OnCtx Γ (env.IsType univs))
    (hp : Pat p r) (hm : p.Matches e ls captures)
    (hc : r.2.OK (env.IsDefEqU univs Γ) ls captures)
    (ht : env.HasType univs Γ e T) (hn : ¬ IsProof Γ e) :
    ProofShape.Matches p (proofErase Γ e) ls (fun i => proofErase Γ (captures i)) := by
  obtain ⟨sp, rfl⟩ := Params.pat_simple hp
  cases sp with
  | defn c =>
    cases hm
    simp only [proofErase, if_neg hn]
    exact matches_captures_congr .const nofun
  | iota rc mr cc kc =>
    cases hm with
    | app hf hm =>
      rename_i F M lsc cf cm
      obtain ⟨_, _, hF, hM⟩ := ht.app_inv henv hΓ
      have hnM : ¬ IsProof Γ M := by
        rintro ⟨P, hMP, hP⟩
        exact hn ⟨T, ht, Params.major_proof hΓ hp (.app hf hm) hc ht hMP hP⟩
      simp only [proofErase, if_neg hn]
      apply matches_captures_congr
        (.app (proofErase_varN_match hΓ hf hF (not_isProof_fn hΓ hF hM hn))
          (proofErase_varN_match hΓ hm hM hnM))
      intro i
      cases i <;> rfl

/-- A typed fixed-template rule simulates forwards after erasure; whole-proof
steps collapse to identity, while data results use the visible template rule. -/
theorem proofErase_template_forward (hΓ : OnCtx Γ (env.IsType univs))
    {p : Pattern} {check : p.Check} {paths : List p.Path} {captures : p.Path → VExpr} {rhs : VExpr} {hclosed : rhs.Closed}
    (hp : Pat p ((paths.map Pattern.RHS.var).foldl Pattern.RHS.app (.fixed rhs hclosed), check))
    (hc : CheckFromTyping env univs p
      ((paths.map Pattern.RHS.var).foldl Pattern.RHS.app (.fixed rhs hclosed), check) ls)
    (hr : env.HasType univs [] (rhs.instL ls) R)
    (hm : p.Matches e ls captures) (ht : env.HasType univs Γ e T) :
    ProofShape.Compute (ErasedIotaPrimitive D) (proofErase Γ e)
      (proofErase Γ (mkApps (rhs.instL ls) (paths.map captures))) := by
  have HE := (pat_wf hΓ hp hm ht (hc hΓ hm ht)).of_l henv hΓ ht
  simp only [Pattern.RHS.apply_foldl_var, Pattern.RHS.apply] at HE
  by_cases hn : IsProof Γ e
  · rw [proofErase_eq_proof.2 hn, proofErase_eq_proof.2 ((isProof_congr hΓ HE).1 hn)]
    exact .refl
  have hn' := mt (isProof_congr hΓ HE).2 hn
  rw [proofErase_mkApps hΓ HE.hasType.2 hn',
    proofErase_closed_context (hr.closedN' henv.ordered.closed (by trivial)).1 hr hΓ]
  have hm' := proofErase_pattern_match_forward hΓ hp hm (hc hΓ hm ht) ht hn
  have H : ProofShape.TemplatePrimitive (proofErase Γ e)
      (ProofShape.mkApps (proofErase [] (rhs.instL ls))
        (paths.map (fun i => proofErase Γ (captures i)))) := .intro hp hc hr hm'
  simpa only [List.map_map, Function.comp_def] using
    (ProofShape.Compute.base (Step := ErasedIotaPrimitive D) (.inr H))

end Lean4Lean.VEnv.Strengthening
