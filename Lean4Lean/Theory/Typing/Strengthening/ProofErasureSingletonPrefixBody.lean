import Lean4Lean.Theory.Typing.Strengthening.ProofErasureSingletonSlots
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTelescope

/-! # Exact body templates for checked generated singleton prefixes

The stored equation supplies a closed typed body. After the actual family check
has typed the bare fields, its captures erase to visible prefix arguments,
selected indices and proof markers, including layouts with dependent data.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr InductiveSignature PropElim Params
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
variable [Params] {S : SingletonLayout} {E : PropElim}

/-- The generated equation's open RHS has its own closed typed telescope,
independently of the occurrence's source and family guard. -/
theorem singleton_prefix_body_typed (H : RecursorRegistered env data)
    (hw : ∀ l ∈ levels, l.WF univs)
    (hg : data.singletonUnfolding env univs levels args = some program) :
    OnCtx (program.equationBody.domains.map (·.instL program.levels)).reverse (env.IsType univs) ∧
      env.HasType univs (program.equationBody.domains.map (·.instL program.levels)).reverse
        (program.equationBody.rhs.instL program.levels)
        (program.equationBody.type.instL program.levels) := by
  obtain ⟨_, _, hlv, _, hseq, hbody, _⟩ := RecursorData.singletonUnfolding_spec hg
  obtain ⟨index, _, hgen⟩ := RecursorData.singletonEquation_eq hseq
  have hr := (H.equation_typed hgen).2
  obtain ⟨_, hrhs, htype⟩ := RecursorSchema.EquationBody.extract_sound hbody
  rw [← hrhs, ← htype] at hr
  have hr := hr.instL (U' := univs) (ls := program.levels) (by rwa [hlv])
  simp only [instL_wrapLams, instL_wrapForalls, List.map_nil] at hr
  simpa only [List.append_nil] using HasType.wrapLams_inv henv (by trivial) hr

/-- The actual checked capture list has a uniform erased description: the
visible prefix followed by selected indices and hidden proof fields. -/
theorem proofErase_singleton_prefix_captures (heq : env.HasCanonicalEq)
    (hΓ : OnCtx Γ (env.IsType univs)) (H : RecursorRegistered env data)
    (hlarge : data.largeTarget = true) (hzero : data.sourceLevel levels ≈ .zero)
    (hw : ∀ l ∈ levels, l.WF univs)
    (hS : data.singletonLayout env levels = some S) (hE : data.propElim levels = some E)
    (hg : data.singletonUnfolding env univs levels args = some program)
    (HC : UnfoldingCheck env univs Γ (mkApps (.const data.name levels) args) program) :
    let Δ := program.domains.reverse ++ Γ
    let all := (data.openedArguments args).map (proofErase Δ)
    program.captures.map (proofErase Δ) = all.take data.indexOffset ++
      ProofShape.singletonSlots S.slot S.fields.length
        ((all.drop data.indexOffset).take data.numIndices) := by
  dsimp only
  obtain ⟨_, _, hlv, hlvlen, hseq, _, _⟩ := RecursorData.singletonUnfolding_spec hg
  have hlen : levels.length = data.uvars := by
    rw [hlv] at hlvlen
    exact hlvlen.trans (RecursorData.singletonEquation_uvars hseq)
  obtain ⟨index, howner, _⟩ := RecursorData.singletonEquation_eq hseq
  obtain ⟨S', E', hS', hE', W⟩ := RecursorData.propElim_wf henv H hlarge hzero hw hlen ⟨index, howner⟩
  cases Option.some.inj (hS'.symm.trans hS)
  cases Option.some.inj (hE'.symm.trans hE)
  obtain ⟨hctx, hps, _, hidx, _, _, hargs⟩ :=
    GuardedSingleton.registered_opened_args henv hΓ H hlarge hzero hw hlen howner hS hE hg
      ⟨_, HC.source_typed⟩ W
  have hguard := GuardedSingleton.family_conversion_of_check henv heq hΓ H hlarge hzero
    hw hlen howner hS hE hg HC
  obtain ⟨family, ls, hfamily, hrigid⟩ :=
    RecursorData.propElim_family_rigid henv H hlarge hzero howner hE
  have hslot := RecursorData.singleton_slot_lt H hlarge hzero howner hS
  have hf := (reconstruction_of_family_conversion henv heq W hctx hfamily hrigid hslot
    hps hargs hguard).1
  obtain ⟨S'', E'', hS'', hE'', _, _, hcaps⟩ := RecursorData.singletonUnfolding_layout hg
  cases Option.some.inj (hS''.symm.trans hS)
  cases Option.some.inj (hE''.symm.trans hE)
  rw [hcaps, List.map_append]
  rw [← List.map_take, ← List.map_drop, ← List.map_take]
  exact congrArg (_ ++ ·) (proofErase_singleton_occ_slots W hps hidx hf)

/-- A checked generated RHS body erases by applying the closed equation-body
template to the explicit slot vector. No proof-only or unindexed restriction is
made; the actual unfolding check supplies the necessary bare-field typing. -/
theorem proofErase_singleton_prefix_body (heq : env.HasCanonicalEq)
    (hΓ : OnCtx Γ (env.IsType univs)) (H : RecursorRegistered env data)
    (hlarge : data.largeTarget = true) (hzero : data.sourceLevel levels ≈ .zero)
    (hw : ∀ l ∈ levels, l.WF univs)
    (hS : data.singletonLayout env levels = some S) (hE : data.propElim levels = some E)
    (hg : data.singletonUnfolding env univs levels args = some program)
    (HC : UnfoldingCheck env univs Γ (mkApps (.const data.name levels) args) program) :
    let Δ := program.domains.reverse ++ Γ
    let all := (data.openedArguments args).map (proofErase Δ)
    proofErase Δ ((program.equationBody.rhs.instL program.levels).instOuter program.captures) =
      (proofErase (program.equationBody.domains.map (·.instL program.levels)).reverse
        (program.equationBody.rhs.instL program.levels)).instOuter
          (all.take data.indexOffset ++ ProofShape.singletonSlots S.slot S.fields.length
            ((all.drop data.indexOffset).take data.numIndices)) := by
  dsimp only
  obtain ⟨hbodyCtx, hbody⟩ := singleton_prefix_body_typed H hw hg
  have hctx := (HC.source_typed.etaOpen_wf henv.ordered hΓ).1
  have hcaps : TelInst env univs (program.domains.reverse ++ Γ)
      (program.equationBody.domains.map (·.instL program.levels)) program.captures := by
    refine ⟨by simpa only [List.length_map] using HC.captures_length, ?_⟩
    intro j hj hd
    simpa only [List.getElem_map] using HC.captures_typed j hj (by simpa only [List.length_map] using hd)
  rw [proofErase_instOuter hctx hbodyCtx hbody hcaps,
    proofErase_singleton_prefix_captures heq hΓ H hlarge hzero hw hS hE hg HC]

/-- A checked non-proof prefix has an exact raw output built from its residual
annotations, fixed equation-body template, and erased slot captures. -/
theorem proofErase_singleton_prefix_output (heq : env.HasCanonicalEq)
    (hΓ : OnCtx Γ (env.IsType univs)) (H : RecursorRegistered env data)
    (hlarge : data.largeTarget = true) (hzero : data.sourceLevel levels ≈ .zero)
    (hw : ∀ l ∈ levels, l.WF univs)
    (hS : data.singletonLayout env levels = some S) (hE : data.propElim levels = some E)
    (hg : data.singletonUnfolding env univs levels args = some program)
    (HC : UnfoldingCheck env univs Γ (mkApps (.const data.name levels) args) program)
    (hn : ¬ IsProof Γ (mkApps (.const data.name levels) args)) :
    let Δ := program.domains.reverse ++ Γ
    let all := (data.openedArguments args).map (proofErase Δ)
    proofErase Γ program.rhs =
      ProofShape.wrapLams (proofEraseDomains Γ program.domains)
        ((proofErase (program.equationBody.domains.map (·.instL program.levels)).reverse
          (program.equationBody.rhs.instL program.levels)).instOuter
            (all.take data.indexOffset ++ ProofShape.singletonSlots S.slot S.fields.length
              ((all.drop data.indexOffset).take data.numIndices))) := by
  dsimp only
  have hctx := (HC.source_typed.etaOpen_wf henv.ordered hΓ).1
  have hn' : ¬ IsProof Γ program.rhs := mt (isProof_congr hΓ (HC.defeq henv hΓ)).2 hn
  rw [RecursorData.PrefixUnfolding.rhs] at hn' ⊢
  rw [proofErase_wrapLams_nonproof hctx hn', instantiateParams_eq_instOuter,
    proofErase_singleton_prefix_body heq hΓ H hlarge hzero hw hS hE hg HC]

end Lean4Lean.VEnv.Strengthening
