import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqPairedInsertion

/-! # Compose paired insertions at different depths

Each block retains its actual source and outgoing context insertion. A finite
chain records their literal order rather than flattening separated blocks into
one. The lower target assignments remain below the entire chain.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape

/-- Ordered unused blocks, each with its insertion count and current offset. -/
abbrev EqInsertionPath := List (Nat × Nat)

/-- Apply the recorded blocks to an actual term, in their recorded order. -/
def EqInsertionPath.actual : EqInsertionPath → VExpr → VExpr
  | [], e => e
  | (n,k) :: blocks, e => EqInsertionPath.actual blocks (e.liftN n k)

/-- Apply the same blocks to erased syntax. -/
def EqInsertionPath.erased : EqInsertionPath → ProofShape → ProofShape
  | [], e => e
  | (n,k) :: blocks, e => EqInsertionPath.erased blocks (e.liftN n k)

/-- Entering one common binder moves every recorded insertion one slot deeper. -/
def EqInsertionPath.underBinder (blocks : EqInsertionPath) : EqInsertionPath :=
  blocks.map fun (n,k) => (n,k+1)

theorem EqInsertionPath.actual_snoc (blocks : EqInsertionPath) (e : VExpr) :
    (blocks ++ [(n,k)]).actual e = (blocks.actual e).liftN n k := by
  induction blocks generalizing e with
  | nil => rfl
  | cons p blocks ih => cases p; exact ih _

theorem EqInsertionPath.erased_snoc (blocks : EqInsertionPath) (e : ProofShape) :
    (blocks ++ [(n,k)]).erased e = (blocks.erased e).liftN n k := by
  induction blocks generalizing e with
  | nil => rfl
  | cons p blocks ih => cases p; exact ih _

theorem EqInsertionPath.actual_sort (blocks : EqInsertionPath) (u : VLevel) :
    blocks.actual (.sort u) = .sort u := by
  induction blocks with
  | nil => rfl
  | cons p blocks ih => cases p; simpa only [EqInsertionPath.actual, VExpr.liftN] using ih

open private ProofShape.liftN_forallE_inv
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypedReplay
open private erase_forallE_inv
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta

/-- A recovered Pi image through separated insertions has one exact lower Pi
shape. Its domain follows the old chain and its body follows the shifted chain. -/
theorem EqInsertionPath.forall_inv (blocks : EqInsertionPath)
    (E : blocks.erased e = .forallE rawA rawB) :
    ∃ A B, e = .forallE A B ∧ blocks.erased A = rawA ∧ blocks.underBinder.erased B = rawB := by
  induction blocks generalizing e rawA rawB with
  | nil => exact ⟨rawA, rawB, E, rfl, rfl⟩
  | cons p blocks ih =>
    obtain ⟨n,k⟩ := p
    obtain ⟨A', B', EE, EA, EB⟩ := ih E
    obtain ⟨A, B, Ee, EAlift, EBlift⟩ := ProofShape.liftN_forallE_inv EE
    refine ⟨A, B, Ee, ?_, ?_⟩
    · simpa only [EqInsertionPath.erased, EAlift] using EA
    · simpa only [EqInsertionPath.underBinder, List.map_cons, EqInsertionPath.erased, EBlift] using EB

/-- The native fresh-body recipe commutes with the shifted insertion chain. -/
theorem EqInsertionPath.erased_eta (blocks : EqInsertionPath) (f : ProofShape) (u : VLevel) :
    blocks.underBinder.erased (.app (f.liftN 1) (etaArgument u)) =
      .app ((blocks.erased f).liftN 1) (etaArgument u) := by
  induction blocks generalizing f with
  | nil => rfl
  | cons p blocks ih =>
    obtain ⟨n,k⟩ := p
    change EqInsertionPath.erased (EqInsertionPath.underBinder blocks) ((ProofShape.app (f.liftN 1) (etaArgument u)).liftN n (k+1)) = _
    rw [ProofShape.liftN, etaArgument_liftN,
      ← ProofShape.liftN_comm f n 1 k 0 (Nat.zero_le _)]
    exact ih (f.liftN n k)

/-- Every block preserves the constant spine and transforms only its arguments. -/
theorem EqInsertionPath.erased_const_spine (blocks : EqInsertionPath) (args : List ProofShape) :
    blocks.erased (ProofShape.mkApps (.const c ls) args) =
      ProofShape.mkApps (.const c ls) (args.map blocks.erased) := by
  induction blocks generalizing args with
  | nil => simp only [EqInsertionPath.erased, List.map_id_fun', id]
  | cons p blocks ih =>
    obtain ⟨n,k⟩ := p
    simp only [EqInsertionPath.erased, ProofShape.liftN_mkApps, ProofShape.liftN, ih,
      List.map_map, Function.comp_def]

variable [Params]

/-- A finite sequence of paired actual insertions. The upper map of each block
is the lower map of the next. Its stored context witnesses and commuting
squares are never replaced by unrelated existential target assignments. -/
inductive EqFrameInsertionChain (Γ Γ' : List VExpr) (ρ : VExpr.Subst) (τ : ProofShape.Subst) :
    List VExpr → List VExpr → VExpr.Subst → ProofShape.Subst → EqInsertionPath → Prop where
  | refl : EqFrameInsertionChain Γ Γ' ρ τ Γ Γ' ρ τ []
  | step : EqFrameInsertionChain Γ Γ' ρ τ Λ Λ' κ υ blocks →
      EqFrameInsertion Λ Λ' Ψ Ψ' n k κ υ χ ω →
      EqFrameInsertionChain Γ Γ' ρ τ Ψ Ψ' χ ω (blocks ++ [(n,k)])

/-- Chained actual insertion weakens a lower typing through the exact source scopes. -/
theorem EqFrameInsertionChain.weak
    (J : EqFrameInsertionChain Γ Γ' ρ τ Λ Λ' κ υ blocks)
    (he : env.HasType univs Γ e T) :
    env.HasType univs Λ (blocks.actual e) (blocks.actual T) := by
  induction J with
  | refl => exact he
  | step J I ih => simpa only [EqInsertionPath.actual_snoc] using ih.weakN henv I.source

/-- The final actual map and erasure are retained through every block. -/
theorem EqFrameInsertionChain.actual
    (J : EqFrameInsertionChain Γ Γ' ρ τ Λ Λ' κ υ blocks)
    (W : EqSpecializationFrame Γ Γ' Δ σ σ' ρ τ) :
    OnCtx Λ' (env.IsType univs) ∧ Ctx.SubstEq env univs Λ' κ κ Λ ∧ ErasedSubstAgreement Λ Λ' κ υ := by
  cases J with
  | refl => exact ⟨W.target.wf, W.actual, W.erase⟩
  | step _ I => exact ⟨I.target_wf, I.actual, I.erase⟩

/-- Semantic commutation composes without merging the insertion blocks. -/
theorem EqFrameInsertionChain.semantic
    (J : EqFrameInsertionChain Γ Γ' ρ τ Λ Λ' κ υ blocks) (e : VExpr) :
    (blocks.actual e).subst κ = blocks.actual (e.subst ρ) := by
  induction J with
  | refl => rfl
  | step J I ih => simp only [EqInsertionPath.actual_snoc, I.semantic, ih]

/-- The exact raw endpoint commutes with the full upper map. -/
theorem EqFrameInsertionChain.erased
    (J : EqFrameInsertionChain Γ Γ' ρ τ Λ Λ' κ υ blocks) (e : ProofShape) :
    (blocks.erased e).subst υ = blocks.erased (e.subst τ) := by
  induction J with
  | refl => rfl
  | step J I ih => simp only [EqInsertionPath.erased_snoc, I.erased, ih]

/-- Append separately constructed insertion chains, preserving their literal order. -/
theorem EqFrameInsertionChain.append
    (J : EqFrameInsertionChain Γ Γ' ρ τ Λ Λ' κ υ blocks)
    (K : EqFrameInsertionChain Λ Λ' κ υ Ψ Ψ' χ ω more) :
    EqFrameInsertionChain Γ Γ' ρ τ Ψ Ψ' χ ω (blocks ++ more) := by
  induction K with
  | refl => simpa only [List.append_nil] using J
  | step K I ih => simpa only [List.append_assoc] using ih.step I

/-- Add another unused actual domain after every previous insertion. The upper
actual map determines its outgoing domain; no target assignment is extended. -/
theorem EqFrameInsertionChain.insert_domain
    (J : EqFrameInsertionChain Γ Γ' ρ τ Λ Λ' κ υ blocks)
    (W : EqSpecializationFrame Γ Γ' Δ σ σ' ρ τ)
    (hA : env.HasType univs Λ A (.sort u)) :
    EqFrameInsertionChain Γ Γ' ρ τ (A :: Λ) (A.subst κ :: Λ') κ.lift υ.lift (blocks ++ [(1,0)]) := by
  obtain ⟨hΛ', S, ES⟩ := J.actual W
  apply J.step
  refine ⟨Ctx.LiftN.one, Ctx.LiftN.one,
    ⟨hΛ', u, hA.subst henv.orderedStrong S hΛ'⟩, S.lift henv.ordered hA,
    ErasedSubstAgreement.lift hΛ' S hA ES, ?_, ?_⟩
  · intro e; exact VExpr.lift_subst_lift
  · intro e; exact ProofShape.lift_subst_lift e υ

/-- Enter a dependent binder beneath every recorded block. Every intermediate
upper map is obtained from the chain, so no target assignments to intermediate
inserted contexts are needed. The same chain can later receive further insertions. -/
theorem EqFrameInsertionChain.under_binder
    (J : EqFrameInsertionChain Γ Γ' ρ τ Λ Λ' κ υ blocks)
    (W : EqSpecializationFrame Γ Γ' Δ σ σ' ρ τ)
    (hA : env.HasType univs Γ A (.sort u)) :
    EqFrameInsertionChain (A :: Γ) (A.subst ρ :: Γ') ρ.lift τ.lift
      (blocks.actual A :: Λ) (blocks.actual (A.subst ρ) :: Λ')
      κ.lift υ.lift blocks.underBinder := by
  induction J with
  | refl => exact .refl
  | @step Λ Λ' κ υ blocks Ψ Ψ' n k χ ω J I ih =>
    obtain ⟨hΛ', S, _⟩ := J.actual W
    have hAmid : env.HasType univs Λ (blocks.actual A) (.sort u) := by
      have H := J.weak hA
      simpa only [EqInsertionPath.actual_sort] using H
    have IN := I.under_binder_actual hΛ' S hAmid
    rw [J.semantic A] at IN
    have H := ih.step IN
    simpa only [EqInsertionPath.underBinder, List.map_append, List.map_cons, List.map_nil,
      EqInsertionPath.actual_snoc] using H

/-- Erasure of a typed lower term is the literal recorded raw insertion path. -/
theorem EqFrameInsertionChain.erase_actual
    (J : EqFrameInsertionChain Γ Γ' ρ τ Λ Λ' κ υ blocks)
    (W : EqSpecializationFrame Γ Γ' Δ σ σ' ρ τ)
    (he : env.HasType univs Γ e T) :
    proofErase Λ (blocks.actual e) = blocks.erased (proofErase Γ e) := by
  induction J with
  | refl => rfl
  | step J I ih =>
    rw [EqInsertionPath.actual_snoc, EqInsertionPath.erased_snoc,
      proofErase_liftN (J.actual W).2.1.wf I.actual.wf I.source (J.weak he), ih]

/-- Actual certificates descend through every recorded block, preserving the
exact lower source scope and exact upper endpoint. This is the path-level
bridge needed before the original chosen assignment is applied. -/
theorem EqFrameInsertionChain.compute_certificate
    (hstep : ErasedScopedPrimitiveCertificateDescent Step Step)
    (J : EqFrameInsertionChain Γ Γ' ρ τ Λ Λ' κ υ blocks)
    (W : EqSpecializationFrame Γ Γ' Δ σ σ' ρ τ)
    (he : env.HasType univs Γ e T)
    (R : ScopedCompute Step (proofEraseCtx Λ) (blocks.erased (proofErase Γ e)) out) :
    ∃ e', env.IsDefEq univs Γ e e' T ∧
      ScopedCompute Step (proofEraseCtx Γ) (proofErase Γ e) (proofErase Γ e') ∧
      blocks.erased (proofErase Γ e') = out := by
  induction J generalizing out with
  | refl =>
    obtain ⟨e', HE, ER, EE⟩ := proofErase_scoped_compute_certificate_descend hstep
      W.actual.wf W.actual.wf (Ctx.LiftN.zero []) he rfl
      (by simpa only [EqInsertionPath.erased, List.length_nil, ProofShape.liftN_zero] using R)
    exact ⟨e', HE, ER, by simpa only [EqInsertionPath.erased, List.length_nil, ProofShape.liftN_zero] using EE⟩
  | @step Λ Λ' κ υ blocks Ψ Ψ' n k χ ω J I ih =>
    have RM : ScopedCompute Step (proofEraseCtx Ψ) ((proofErase Λ (blocks.actual e)).liftN n k) out := by
      simpa only [EqInsertionPath.erased_snoc, J.erase_actual W he] using R
    obtain ⟨mid, _, RM, EM⟩ := proofErase_scoped_compute_certificate_descend hstep
      (J.actual W).2.1.wf I.actual.wf I.source (J.weak he) rfl RM
    obtain ⟨e', HE, RE, EE⟩ := ih (by simpa only [J.erase_actual W he] using RM)
    exact ⟨e', HE, RE, by simpa only [EqInsertionPath.erased_snoc, EE] using EM⟩

/-- Lower every actual component certificate through the whole insertion chain.
The result keeps the exact upper raw vector, without selecting target images
for any inserted domain. -/
theorem EqFrameInsertionChain.components_certificate {args : List VExpr}
    (hstep : ErasedScopedPrimitiveCertificateDescent Step Step)
    (J : EqFrameInsertionChain Γ Γ' ρ τ Λ Λ' κ υ blocks)
    (W : EqSpecializationFrame Γ Γ' Δ σ σ' ρ τ)
    (HT : ∀ e ∈ args, VExpr.WF env univs Γ e)
    (HA : List.Forall₂ (ScopedCompute Step (proofEraseCtx Λ))
      ((args.map (proofErase Γ)).map blocks.erased) raw) :
    ∃ lower, List.Forall₂ (ScopedCompute Step (proofEraseCtx Γ))
      (args.map (proofErase Γ)) lower ∧ lower.map blocks.erased = raw := by
  induction args generalizing raw with
  | nil => cases HA; exact ⟨[], .nil, rfl⟩
  | cons e args ih =>
    cases raw with
    | nil => cases HA
    | cons r raw =>
      cases HA with
      | cons R HA =>
        obtain ⟨T, he⟩ := HT e (by simp)
        obtain ⟨e', _, RE, EE⟩ := J.compute_certificate hstep W he R
        obtain ⟨lower, RL, EL⟩ := ih (fun e he => HT e (by simp [he])) HA
        exact ⟨proofErase Γ e' :: lower, .cons RE RL, by simp only [List.map_cons, EE, EL]⟩

/-- Preserve the original chosen assignments across component computation
under any finite sequence of separated insertions. Certificates descend in
reverse insertion order before the lower semantic realization is chosen.
The final raw vector commutes with the original chain's actual upper map. -/
theorem EqPrefixSpecializationAt.compute_insertion_chain
    (hstep : ErasedScopedPrimitiveCertificateDescent Step Step)
    (hΔ : OnCtx Δ (env.IsType univs))
    (H : EqPrefixSpecializationAt Γ Δ v w v' w' original pre σ pending)
    (W : EqSpecializationFrame Γ Γ' Δ σ σ' ρ τ)
    (J : EqFrameInsertionChain Γ Γ' ρ τ Λ Λ' κ υ blocks)
    (hf : env.HasType univs Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre) F)
    (HC : env.IsDefEqU univs Γ (.const ``Eq.rec [v',w']) (.const ``Eq.rec [v'',w'']))
    (HA : List.Forall₂ (ScopedCompute Step (proofEraseCtx Λ))
      ((pre.map (proofErase Γ)).map blocks.erased) raw) :
    ∃ pre', EqPrefixSpecializationAt Γ Δ v w v'' w'' original pre' σ pending ∧
      EqPrefixSpecializationAt Γ' Δ v w v'' w'' original (pre'.map (·.subst ρ)) σ' pending ∧
      env.HasType univs Γ' (VExpr.mkApps (.const ``Eq.rec [v'',w'']) (pre'.map (·.subst ρ))) (F.subst ρ) ∧
      ((pre'.map (proofErase Γ)).map blocks.erased) = raw ∧
      (((pre'.map (·.subst ρ)).map (proofErase Γ')).map blocks.erased) = raw.map (·.subst υ) ∧
      env.IsDefEq univs Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre)
        (VExpr.mkApps (.const ``Eq.rec [v'',w'']) pre') F := by
  obtain ⟨lower, RL, EL⟩ := J.components_certificate hstep W
    (mkApps_arguments_wf henv H.1.wf ⟨_, hf⟩).2 HA
  obtain ⟨pre', HP, EP, HE⟩ := H.compute hstep.descent H.1.wf H.1.wf
    (Ctx.LiftN.zero []) hΔ hf HC
    (by simpa only [List.length_nil, ProofShape.liftN_zero, List.map_id_fun', id] using RL)
  have EP : pre'.map (proofErase Γ) = lower := by
    simpa only [List.length_nil, ProofShape.liftN_zero, List.map_id_fun', id] using EP
  have Eraw : ((pre'.map (proofErase Γ)).map blocks.erased) = raw := by rw [EP]; exact EL
  obtain ⟨Hout, hout, Eout⟩ := HP.frame hΔ W HE.hasType.2
  refine ⟨pre', HP, Hout, hout, Eraw, ?_, HE⟩
  rw [← Eraw, Eout]
  simp only [List.map_map, Function.comp_def, J.erased]

/-- Native type-recovery certificates also descend through the full chain.
The recovered lower actual type and its exact inserted raw image are retained;
no recovery certificate is transported through the agreeing frame. -/
theorem EqFrameInsertionChain.recovery_certificate
    (hstep : ErasedScopedPrimitiveCertificateDescent Step Step)
    (J : EqFrameInsertionChain Γ Γ' ρ τ Λ Λ' κ υ blocks)
    (W : EqSpecializationFrame Γ Γ' Δ σ σ' ρ τ)
    (he : env.HasType univs Γ e T)
    (R : ScopedTypeRecovery Step (proofEraseCtx Λ) (blocks.erased (proofErase Γ e)) rawT) :
    ∃ F, env.HasType univs Γ e F ∧
      ScopedTypeRecovery Step (proofEraseCtx Γ) (proofErase Γ e) (proofErase Γ F) ∧
      blocks.erased (proofErase Γ F) = rawT := by
  induction J generalizing rawT with
  | refl =>
    obtain ⟨F, hF, RF, EF⟩ := proofErase_scoped_recovery_certificate_descend hstep
      W.actual.wf W.actual.wf (Ctx.LiftN.zero []) he rfl
      (by simpa only [EqInsertionPath.erased, List.length_nil, ProofShape.liftN_zero] using R)
    exact ⟨F, hF, RF, by simpa only [EqInsertionPath.erased, List.length_nil, ProofShape.liftN_zero] using EF⟩
  | @step Λ Λ' κ υ blocks Ψ Ψ' n k χ ω J I ih =>
    have RM : ScopedTypeRecovery Step (proofEraseCtx Ψ)
        ((proofErase Λ (blocks.actual e)).liftN n k) rawT := by
      simpa only [EqInsertionPath.erased_snoc, J.erase_actual W he] using R
    obtain ⟨mid, _, RM, EM⟩ := proofErase_scoped_recovery_certificate_descend hstep
      (J.actual W).2.1.wf I.actual.wf I.source (J.weak he) rfl RM
    obtain ⟨F, hF, RF, EF⟩ := ih (by simpa only [J.erase_actual W he] using RM)
    exact ⟨F, hF, RF, by simpa only [EqInsertionPath.erased_snoc, EF] using EM⟩

/-- A domain-sort witness at the top of the chain determines the lower
already-typed domain's sort. Each recorded insertion is descended separately. -/
theorem EqFrameInsertionChain.domain_sort
    (J : EqFrameInsertionChain Γ Γ' ρ τ Λ Λ' κ υ blocks)
    (W : EqSpecializationFrame Γ Γ' Δ σ σ' ρ τ)
    (hA : env.HasType univs Γ A (.sort v))
    (SD : DomainSort (proofEraseCtx Λ) (blocks.erased (proofErase Γ A)) u) :
    env.HasType univs Γ A (.sort u) := by
  induction J with
  | refl =>
    exact (show DomainSort (proofEraseCtx Γ) ((proofErase Γ A).liftN 0) u from
      by simpa only [EqInsertionPath.erased, ProofShape.liftN_zero] using SD).descend
        W.actual.wf W.actual.wf (Ctx.LiftN.zero []) hA
  | @step Λ Λ' κ υ blocks Ψ Ψ' n k χ ω J I ih =>
    have hAmid : env.HasType univs Λ (blocks.actual A) (.sort v) := by
      simpa only [EqInsertionPath.actual_sort] using J.weak hA
    have SDup : DomainSort (proofEraseCtx Ψ) ((proofErase Λ (blocks.actual A)).liftN n k) u := by
      simpa only [EqInsertionPath.erased_snoc, J.erase_actual W hA] using SD
    have hAmidU := SDup.descend (J.actual W).2.1.wf I.actual.wf I.source hAmid
    apply ih
    simpa only [J.erase_actual W hA] using DomainSort.of_typed (J.actual W).2.1.wf hAmidU

/-- Reify a native recovered Pi at the lower source, retaining the exact raw
annotation at the top and the exact body image under the shifted chain. -/
theorem EqFrameInsertionChain.recovered_pi
    (hstep : ErasedScopedPrimitiveCertificateDescent Step Step)
    (J : EqFrameInsertionChain Γ Γ' ρ τ Λ Λ' κ υ blocks)
    (W : EqSpecializationFrame Γ Γ' Δ σ σ' ρ τ)
    (he : env.HasType univs Γ e T)
    (R : ScopedTypeRecovery Step (proofEraseCtx Λ) (blocks.erased (proofErase Γ e)) (.forallE rawA rawB))
    (SD : DomainSort (proofEraseCtx Λ) rawA u) :
    ∃ A B, env.HasType univs Γ A (.sort u) ∧ env.HasType univs Γ e (.forallE A B) ∧
      blocks.erased (proofErase Γ A) = rawA ∧ blocks.underBinder.erased (proofErase (A :: Γ) B) = rawB := by
  obtain ⟨F, hf, _, EF⟩ := J.recovery_certificate hstep W he R
  obtain ⟨rawD, rawC, EF, EA, EB⟩ := blocks.forall_inv EF
  obtain ⟨A, B, rfl, _, ED, EC⟩ := erase_forallE_inv EF
  have EA : blocks.erased (proofErase Γ A) = rawA := by simpa only [← ED] using EA
  have EB : blocks.underBinder.erased (proofErase (A :: Γ) B) = rawB := by simpa only [← EC] using EB
  obtain ⟨_, hPi⟩ := hf.isType henv W.actual.wf
  obtain ⟨⟨_, hA⟩, _, _⟩ := hPi.forallE_inv henv
  exact ⟨A, B, J.domain_sort W hA (EA.symm ▸ SD), hf, EA, EB⟩
/-- Open recovered eta through any finite sequence of separated paired
insertions. Recovery and sort witnesses descend block by block before the
lower chosen assignment is extended. The entire chain then moves beneath
that binder, retaining exact upper context and body erasures. No target image
for an inserted declaration or additional frame agreement is assumed. -/
theorem EqPrefixSpecializationAt.eta_insertion_chain
    (hguard : ErasedScopedPrimitiveCertificateDescent Guard Guard)
    (hΔ : OnCtx Δ (env.IsType univs))
    (H : EqPrefixSpecializationAt Γ Δ v w v' w' original pre σ (y :: rest))
    (W : EqSpecializationFrame Γ Γ' Δ σ σ' ρ τ)
    (J : EqFrameInsertionChain Γ Γ' ρ τ Λ Λ' κ υ blocks)
    (ht : env.HasType univs Δ (VExpr.mkApps (.const ``Eq.rec [v,w]) original) T)
    (hf : env.HasType univs Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre) F)
    (hn : ¬ IsProof Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre))
    (RN : ScopedTypeRecovery Guard (proofEraseCtx Λ)
      (blocks.erased (proofErase Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre)))
      (.forallE rawA rawB))
    (SD : DomainSort (proofEraseCtx Λ) rawA u) :
    ∃ A B,
      env.HasType univs Γ A (.sort u) ∧
      env.HasType univs Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre) (.forallE A B) ∧
      proofEraseCtx (blocks.actual A :: Λ) = rawA :: proofEraseCtx Λ ∧
      EqPrefixSpecializationAt (A :: Γ) Δ v w v' w' original
        (pre.map VExpr.lift ++ [VExpr.bvar 0]) (σ.cons y) rest ∧
      EqSpecializationFrame (A :: Γ) (A.subst ρ :: Γ') Δ
        (σ.cons y) (σ'.cons y) ρ.lift τ.lift ∧
      EqFrameInsertionChain (A :: Γ) (A.subst ρ :: Γ') ρ.lift τ.lift
        (blocks.actual A :: Λ) (blocks.actual (A.subst ρ) :: Λ')
        κ.lift υ.lift blocks.underBinder ∧
      env.HasType univs (A :: Γ)
        (VExpr.mkApps (.const ``Eq.rec [v',w']) (pre.map VExpr.lift ++ [VExpr.bvar 0])) B ∧
      ¬ IsProof (A :: Γ)
        (VExpr.mkApps (.const ``Eq.rec [v',w']) (pre.map VExpr.lift ++ [VExpr.bvar 0])) ∧
      (blocks.underBinder.erased (proofErase (A :: Γ)
        (VExpr.mkApps (.const ``Eq.rec [v',w']) (pre.map VExpr.lift ++ [VExpr.bvar 0])))) =
        .app ((blocks.erased (proofErase Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre))).liftN 1)
          (etaArgument u) := by
  obtain ⟨A, B, hA, hfPi, EA, _⟩ := J.recovered_pi hguard W hf RN SD
  obtain ⟨Hfresh, Wfresh, _, _, _⟩ := H.eta_frame hΔ W ht hA hfPi
  have Ectx : proofEraseCtx (blocks.actual A :: Λ) = rawA :: proofEraseCtx Λ := by
    rw [proofEraseCtx, J.erase_actual W hA, EA]
  have hfw : env.HasType univs (A :: Γ)
      (VExpr.mkApps (.const ``Eq.rec [v',w']) pre).lift
      (.forallE A.lift (B.liftN 1 1)) := hfPi.weak henv
  have Ebody : VExpr.mkApps (.const ``Eq.rec [v',w']) (pre.map VExpr.lift ++ [VExpr.bvar 0]) =
      .app (VExpr.mkApps (.const ``Eq.rec [v',w']) pre).lift (.bvar 0) := by
    simp only [VExpr.mkApps_append, VExpr.mkApps_cons, VExpr.mkApps_nil,
      VExpr.lift, VExpr.liftN_mkApps, VExpr.liftN]
  have hb : env.HasType univs (A :: Γ)
      (VExpr.mkApps (.const ``Eq.rec [v',w']) (pre.map VExpr.lift ++ [VExpr.bvar 0])) B := by
    rw [Ebody]
    simpa only [VExpr.inst_liftN_bvar] using hfw.app (HasType.bvar .zero)
  have EB := proofErase_eta_body H.1.wf hA hfPi hn
  rw [← Ebody] at EB
  have hnb : ¬ IsProof (A :: Γ)
      (VExpr.mkApps (.const ``Eq.rec [v',w']) (pre.map VExpr.lift ++ [VExpr.bvar 0])) := by
    intro hp
    rw [proofErase_eq_proof.2 hp] at EB
    cases EB
  refine ⟨A, B, hA, hfPi, Ectx, Hfresh, Wfresh, J.under_binder W hA, hb, hnb, ?_⟩
  rw [EB]
  exact blocks.erased_eta _ _

/-- The same recorded insertion chain supplies the existing iterated
completion readout. This forgetful map does not change either chosen frame
or the actual insertion witnesses retained by the chain itself. -/
theorem EqFrameInsertionChain.completion
    (J : EqFrameInsertionChain Γ Γ' ρ τ Λ Λ' κ υ blocks)
    (W : EqSpecializationFrame Γ Γ' Δ σ σ' ρ τ)
    (hf : env.HasType univs Γ f F)
    (HP : IteratedAmbientEqCompletion Δ v w original (proofEraseCtx Γ) (proofErase Γ f)) :
    IteratedAmbientEqCompletion Δ v w original (proofEraseCtx Λ) (blocks.erased (proofErase Γ f)) := by
  induction J with
  | refl => exact HP
  | @step Λ Λ' κ υ blocks Ψ Ψ' n k χ ω J I ih =>
    have Hmid : IteratedAmbientEqCompletion Δ v w original (proofEraseCtx Λ)
        (proofErase Λ (blocks.actual f)) := by
      rw [J.erase_actual W hf]
      exact ih
    have HH := IteratedAmbientEqCompletion.insert (J.actual W).2.1.wf I.actual.wf I.source (J.weak hf) Hmid
    simpa only [J.erase_actual W hf, EqInsertionPath.erased_snoc] using HH

/-- A real short-prefix cut beneath separated insertion blocks strictly
descends while retaining the full shifted chain and lower agreeing frame.
The exact upper raw body and context are identified after blockwise recovery
descent. Positive singleton guards still read the original target equation.
Further saturated opening and actual continuation consumption still need
integration into the global recursion. -/
theorem EqPrefixSpecializationAt.chain_hole_cut_eq_or_smaller
    {C : ScopedHole Ξ (proofEraseCtx Λ)}
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hRec : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hΔ : OnCtx Δ (env.IsType univs))
    (ht : env.HasType univs Δ (eqRecBeforeMajor v w α a M minor b) T)
    (H : EqPrefixSpecializationAt Γ Δ v w v' w' [α,a,M,minor,b] pre σ (y :: rest))
    (W : EqSpecializationFrame Γ Γ' Δ σ σ' ρ τ)
    (J : EqFrameInsertionChain Γ Γ' ρ τ Λ Λ' κ υ blocks)
    (hf : env.HasType univs Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre) F)
    (hn : ¬ IsProof Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre))
    (HC : SpineBinderHole C) (HT : TypedSource Ξ source)
    (RP : ScopedComputeCount (PiInertStage D n) cp Ξ source
      (C.plug (ProofShape.mkApps (.const ``Eq.rec [v',w'])
        ((pre.map (proofErase Γ)).map blocks.erased))))
    (HR : PiInertStage D n (proofEraseCtx Λ)
      (ProofShape.mkApps (.const ``Eq.rec [v',w']) ((pre.map (proofErase Γ)).map blocks.erased)) target)
    (HN : ¬ LevelPrimitive univs
      (ProofShape.mkApps (.const ``Eq.rec [v',w']) ((pre.map (proofErase Γ)).map blocks.erased)) target)
    (RT : ScopedComputeCount (PiInertStage D n) ct Ξ (C.plug target) endpoint)
    (HK : PiInertTypedContinuationRun D Ω out Ξ K endpoint ck)
    (HE : CarrierExposure out) (HO : ControlTyping Ω out (.sort outU))
    (hcost : cp+1+ct+ck ≤ cost)
    (hmin : ∀ later j tail k, ScopedComputeCount (PiInertStage D later) j Ξ source tail →
      K tail k → cost ≤ j+k) :
    env.IsDefEq univs Δ a b α ∨ ∃ A B u,
      env.HasType univs Γ A (.sort u) ∧ ct+ck < cost ∧
      PiInertTypedContinuationMinimum D Ω out (proofEraseCtx (blocks.actual A :: Λ))
        (blocks.underBinder.erased (proofErase (A :: Γ)
          (VExpr.mkApps (.const ``Eq.rec [v',w']) (pre.map VExpr.lift ++ [VExpr.bvar 0])))) (ct+ck) ∧
      EqPrefixSpecializationAt (A :: Γ) Δ v w v' w' [α,a,M,minor,b]
        (pre.map VExpr.lift ++ [VExpr.bvar 0]) (σ.cons y) rest ∧
      EqSpecializationFrame (A :: Γ) (A.subst ρ :: Γ') Δ
        (σ.cons y) (σ'.cons y) ρ.lift τ.lift ∧
      EqFrameInsertionChain (A :: Γ) (A.subst ρ :: Γ') ρ.lift τ.lift
        (blocks.actual A :: Λ) (blocks.actual (A.subst ρ) :: Λ')
        κ.lift υ.lift blocks.underBinder ∧
      env.HasType univs (A :: Γ)
        (VExpr.mkApps (.const ``Eq.rec [v',w']) (pre.map VExpr.lift ++ [VExpr.bvar 0])) B ∧
      ¬ IsProof (A :: Γ)
        (VExpr.mkApps (.const ``Eq.rec [v',w']) (pre.map VExpr.lift ++ [VExpr.bvar 0])) := by
  have Ee := proofErase_const_spine H.1.wf hf hn
  have HPbase : EqHeadCompletion Δ v w [α,a,M,minor,b] (proofEraseCtx Γ)
      (proofErase Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre)) := by
    refine ⟨Γ, Γ, 0, 0, v', w', pre, F, H.1.wf, H.1.wf, Ctx.LiftN.zero [], rfl,
      hf, hn, H.forget, ?_⟩
    simp only [ProofShape.liftN_zero]
  have HP := (EqTargetPrefixCompletion.of_completion (J.completion W hf (.base HPbase))).embedding
  rw [Ee, EqInsertionPath.erased_const_spine] at HP
  rcases HP.hole_cut_eq_or_smaller heq hs hreg hoff hRec hΔ ht
      HC HT RP HR HN RT HK HE HO hcost hmin with
    Hlower | ⟨k, rawA, rawB, u, _, _, RN, SD, hsmall, HM, _⟩
  · exact .inl Hlower
  · obtain ⟨A, B, hA, _, Ectx, Hfresh, Wfresh, Ifresh, hb, hnb, EB⟩ :=
      H.eta_insertion_chain (erased_static_structure_eta_expansion_stage_certificate_descent heq hs k)
        hΔ W J ht hf hn
        (by simpa only [Ee, EqInsertionPath.erased_const_spine] using RN) SD
    refine .inr ⟨A, B, u, hA, hsmall, ?_, Hfresh, Wfresh, Ifresh, hb, hnb⟩
    simpa only [Ectx, EB, Ee, EqInsertionPath.erased_const_spine] using HM

end Lean4Lean.VEnv.Strengthening
