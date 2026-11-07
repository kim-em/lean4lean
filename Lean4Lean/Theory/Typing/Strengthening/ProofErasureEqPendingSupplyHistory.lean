import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqReturningSupplyHistory
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqChainArgumentHistory

/-! # Retained histories carrying their actual pending argument supplies

A wrapper alone does not identify the chosen image of a later consumed argument.
Record its typed lower supply, exact upper vector, and pending-vector equation
at the same source scope. Unused binders occur only after chosen completion.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params]

/-- The arguments attached to one retained chosen binder. The local chosen
supply followed by the enclosing pending vector begins with that binder's
chosen image. A nonempty lower supply has its head typed at the original domain.
Untracked upper extras can occur only after the enclosing pending vector ends. -/
def EqRetainedArgumentSupply (Γ Δ : List VExpr) (σ : VExpr.Subst)
    (blocks : EqInsertionPath) (A y : VExpr) (pending remaining : List VExpr)
    (raw : List ProofShape) : Prop :=
  ∃ supplied actual extra,
    EqArgumentSupplyAt Γ Δ σ supplied actual ∧
    (∀ x xs, actual = x :: xs → env.HasType univs Γ x A) ∧
    supplied ++ pending = y :: remaining ∧ (extra = [] ∨ pending = []) ∧
    ((actual.map (proofErase Γ)).map blocks.erased) ++ extra = raw

/-- An argument-free retained lambda takes its chosen image from the enclosing
pending vector and preserves the exact empty local vector. -/
theorem EqRetainedArgumentSupply.empty :
    EqRetainedArgumentSupply Γ Δ σ blocks A y (y :: pending) pending [] := by
  refine ⟨[], [], [], ⟨?_, .nil⟩, ?_, rfl, .inl rfl, rfl⟩
  · intro e he; cases he
  · intro x xs he; cases he

/-- The actual source equalities in a retained eta origin give the computed
head's domain typing. Its chosen images and exact raw vector determine the
pending-vector transition, including all untracked upper extras. -/
theorem EqRetainedArgumentSupply.of_computed
    (hΓ : OnCtx Γ (env.IsType univs))
    (HS : EqArgumentSupplyAt Γ Δ σ (y :: chosen) actual)
    (HE : List.Forall₂ (env.IsDefEqU univs Γ) (x :: previous) actual)
    (hx : env.HasType univs Γ x A)
    (hextra : extra = [] ∨ pending = [])
    (ER : ((actual.map (proofErase Γ)).map blocks.erased) ++ extra = raw) :
    EqRetainedArgumentSupply Γ Δ σ blocks A y pending (chosen ++ pending) raw := by
  refine ⟨y :: chosen, actual, extra, HS, ?_, rfl, hextra, ER⟩
  intro a args ha
  subst actual
  cases HE with
  | cons HX _ => exact (HX.of_l henv hΓ hx).hasType.2

/-- The same supplied images survive an agreeing realization and annotation
conversion. The raw vector follows the actual upper map exactly; no argument
computation or guarded annotation path is substituted. -/
theorem EqRetainedArgumentSupply.frame
    (hΔ : OnCtx Δ (env.IsType univs))
    (H : EqRetainedArgumentSupply Γ Δ σ incoming A y pending remaining raw)
    (Q : EqSupplyInsertionSquare Γ Γ' Δ σ σ' ρ τ Λ Λ' κ υ incoming outgoing)
    (HAB : env.IsDefEq univs Γ A B (.sort u)) :
    EqRetainedArgumentSupply Γ' Δ σ' outgoing (B.subst ρ) y pending remaining
      (raw.map (·.subst υ)) := by
  obtain ⟨supplied, actual, extra, HS, hx, EP, hextra, ER⟩ := H
  obtain ⟨HS', ES⟩ := HS.frame hΔ Q.lower
  refine ⟨supplied, actual.map (·.subst ρ), extra.map (·.subst υ), HS', ?_, EP, ?_, ?_⟩
  · intro x xs he
    cases actual with
    | nil => cases he
    | cons a args =>
      have EX := (List.cons.inj he).1
      subst x
      exact (hx a args rfl |>.defeqU_r henv Q.lower.actual.wf HAB.toU).subst
        henv.orderedStrong Q.lower.actual Q.lower.target.wf
  · rcases hextra with rfl | hp
    · exact .inl rfl
    · exact .inr hp
  · rw [ES, ← ER]
    simp only [List.map_append, List.map_map, Function.comp_def, Q.erased]

/-- The source history now also records how each retained frame consumes the
pending chosen vector and which actual arguments can later supply that frame.
The outgoing placeholders remain independent of the source argument records. -/
inductive EqPendingSupplyHistory (D : Definitions) (Δ Γ₀ Λ₀ : List VExpr)
    (σ₀ : VExpr.Subst) (blocks₀ : EqInsertionPath) (pending₀ : List VExpr)
    (Ψ₀ : List ProofShape) (υ₀ : ProofShape.Subst) :
    List VExpr → List VExpr → VExpr.Subst → EqInsertionPath → List VExpr →
    List ProofShape → ProofShape.Subst → (ProofShape → ProofShape) → Nat → Nat → Prop where
  | base : EqPendingSupplyHistory D Δ Γ₀ Λ₀ σ₀ blocks₀ pending₀ Ψ₀ υ₀
      Γ₀ Λ₀ σ₀ blocks₀ pending₀ Ψ₀ υ₀ id 0 0
  | retained : EqPendingSupplyHistory D Δ Γ₀ Λ₀ σ₀ blocks₀ pending₀ Ψ₀ υ₀
        Γ Λ σ blocks pending Ψ υ plug chosen depth →
      env.HasType univs Γ A (.sort u) → env.HasType univs Δ y (A.subst σ) →
      ScopedComputeCount (PiInertStage D n) cd (proofEraseCtx Λ)
        (blocks.erased (proofErase Γ A)) rawA' →
      EqRetainedArgumentSupply Γ Δ σ blocks A y pending remaining args →
      EqPendingSupplyHistory D Δ Γ₀ Λ₀ σ₀ blocks₀ pending₀ Ψ₀ υ₀
        (A :: Γ) (blocks.actual A :: Λ) (σ.cons y) blocks.underBinder remaining
        (rawA'.subst υ :: Ψ) υ.lift
        (fun e => plug (ProofShape.mkApps (.lam rawA' e) args)) (chosen+1) (depth+1)
  | unused : EqPendingSupplyHistory D Δ Γ₀ Λ₀ σ₀ blocks₀ pending₀ Ψ₀ υ₀
        Γ Λ σ blocks [] Ψ υ plug chosen depth →
      env.HasType univs Λ A (.sort u) →
      ScopedComputeCount (PiInertStage D n) cd (proofEraseCtx Λ) (proofErase Λ A) rawA' →
      EqPendingSupplyHistory D Δ Γ₀ Λ₀ σ₀ blocks₀ pending₀ Ψ₀ υ₀
        Γ (A :: Λ) σ (blocks ++ [(1,0)]) [] (rawA'.subst υ :: Ψ) υ.lift
        (fun e => plug (ProofShape.mkApps (.lam rawA' e) args)) chosen (depth+1)

/-- Forget the pending argument metadata without changing any actual history
scope, wrapper, chosen image, annotation path or binder count. -/
theorem EqPendingSupplyHistory.forget
    (H : EqPendingSupplyHistory D Δ Γ₀ Λ₀ σ₀ blocks₀ pending₀ Ψ₀ υ₀
      Γ Λ σ blocks pending Ψ υ plug chosen depth) :
    EqInterleavedSupplyHistory D Δ Γ₀ Λ₀ σ₀ blocks₀ Ψ₀ υ₀
      Γ Λ σ blocks Ψ υ plug chosen depth := by
  induction H with
  | base => exact .base
  | retained _ hA hy RD _ ih => exact .retained ih hA hy RD
  | unused _ hA RD ih => exact .unused ih hA RD

/-- Source pending supplies are unchanged when outgoing placeholders are filled
from a later actual consumption. -/
theorem EqPendingSupplyHistory.rebase_endpoint
    (H : EqPendingSupplyHistory D Δ Γ₀ Λ₀ σ₀ blocks₀ pending₀ Ψ₀ υ₀
      Γ Λ σ blocks pending Ψ υ plug chosen depth)
    (newTarget : List ProofShape) (newMap : ProofShape.Subst) :
    ∃ Ψ' υ', EqPendingSupplyHistory D Δ Γ₀ Λ₀ σ₀ blocks₀ pending₀ newTarget newMap
      Γ Λ σ blocks pending Ψ' υ' plug chosen depth := by
  induction H with
  | base => exact ⟨_, _, .base⟩
  | retained _ hA hy RD HA ih =>
    obtain ⟨Ψ', υ', HR⟩ := ih
    exact ⟨_, _, .retained HR hA hy RD HA⟩
  | unused _ hA RD ih =>
    obtain ⟨Ψ', υ', HR⟩ := ih
    exact ⟨_, _, .unused HR hA RD⟩

/-- Joining histories requires the inner base pending vector to be the older
history's current vector. Thus the supplied-image chain is retained across the
join, as well as the exact source scopes and wrapper composition. -/
theorem EqPendingSupplyHistory.append
    (H : EqPendingSupplyHistory D Δ Γ₀ Λ₀ σ₀ blocks₀ pending₀ Ψ₀ υ₀
      Γ₁ Λ₁ σ₁ blocks₁ pending₁ Ψ₁ υ₁ plug₁ chosen₁ depth₁)
    (K : EqPendingSupplyHistory D Δ Γ₁ Λ₁ σ₁ blocks₁ pending₁ Ψ₁ υ₁
      Γ₂ Λ₂ σ₂ blocks₂ pending₂ Ψ₂ υ₂ plug₂ chosen₂ depth₂) :
    EqPendingSupplyHistory D Δ Γ₀ Λ₀ σ₀ blocks₀ pending₀ Ψ₀ υ₀
      Γ₂ Λ₂ σ₂ blocks₂ pending₂ Ψ₂ υ₂ (fun e => plug₁ (plug₂ e))
      (chosen₁+chosen₂) (depth₁+depth₂) := by
  induction K with
  | base => simpa only [id_eq, Nat.add_zero] using H
  | retained _ hA hy RD HA ih =>
    simpa only [Nat.add_assoc] using EqPendingSupplyHistory.retained ih hA hy RD HA
  | unused _ hA RD ih =>
    simpa only [Nat.add_assoc] using EqPendingSupplyHistory.unused ih hA RD

/-- Realization rebuilds all waiting supplies along with the outgoing source
history. Chosen images and pending vectors stay fixed, head arguments are
converted to the computed domains, and every actual vector follows the exact
upper substitution. Native annotation paths are replaced by reflexive paths at
the computed outgoing domains, rather than transported under substitution. -/
theorem EqPendingSupplyHistory.realize_returning
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΔ : OnCtx Δ (env.IsType univs))
    (H : EqPendingSupplyHistory D Δ Γ₀ Λ₀ σ₀ incoming pending₀ Ψ₀ υ₀
      Γ Λ σ blocks pending Ψ υ plug chosen depth)
    (Q : EqSupplyInsertionSquare Γ₀ Γ₀' Δ σ₀ σ₀' ρ₀ τ₀ Λ₀ Λ₀' κ₀ υ₀ incoming outgoing)
    (EΨ : Ψ₀ = proofEraseCtx Λ₀') :
    ∃ (Γ' Λ' : List VExpr) (σ' : VExpr.Subst) (outblocks : EqInsertionPath) (plug' : ProofShape → ProofShape),
      EqSupplyInsertionSquare Γ Γ' Δ σ σ' (ρ₀.liftN chosen) (τ₀.liftN chosen)
        Λ Λ' (κ₀.liftN depth) υ blocks outblocks ∧ Ψ = proofEraseCtx Λ' ∧
      EqPendingSupplyHistory D Δ Γ₀' Λ₀' σ₀' outgoing pending₀ (proofEraseCtx Λ₀') ProofShape.Subst.id
        Γ' Λ' σ' outblocks pending (proofEraseCtx Λ') ProofShape.Subst.id plug' chosen depth ∧
      ∀ e : ProofShape, (plug e).subst υ₀ = plug' (e.subst υ) := by
  induction H with
  | base => exact ⟨Γ₀', Λ₀', σ₀', outgoing, id, Q, EΨ, .base, fun _ => rfl⟩
  | @retained Γ Λ σ blocks pending Ψ υ plug chosen depth A u y n cd rawA' remaining args H hA hy RD HA ih =>
    obtain ⟨Γ', Λ', σ', outblocks, plug', Q, EΨ, HR, EW⟩ := ih
    obtain ⟨B, HAB, _, Qnew, EB⟩ := Q.retained heq hs hΔ hA hy RD.forget
    have hBout : env.HasType univs Γ' (B.subst (ρ₀.liftN chosen)) (.sort u) := by
      simpa only [VExpr.subst] using HAB.hasType.2.subst henv.orderedStrong Q.lower.actual Q.lower.target.wf
    have hyout : env.HasType univs Δ y ((B.subst (ρ₀.liftN chosen)).subst σ') := by
      cases Qnew.lower.target with | cons _ _ hy => exact hy.hasType.1
    have WT := EqSpecializationFrame.of_conversion hΔ Q.lower.target (.refl Q.lower.target.wf)
    have ER : outblocks.erased (proofErase Γ' (B.subst (ρ₀.liftN chosen))) = rawA'.subst υ :=
      (Q.target.erase_actual WT hBout).symm.trans EB
    have RDout : ScopedComputeCount (PiInertStage D 0) 0 (proofEraseCtx Λ')
        (outblocks.erased (proofErase Γ' (B.subst (ρ₀.liftN chosen)))) (rawA'.subst υ) := by
      rw [ER]; exact .beta .refl
    have HRnew := EqPendingSupplyHistory.retained (args := args.map (·.subst υ)) HR hBout hyout RDout (HA.frame hΔ Q HAB)
    refine ⟨_, _, _, _, (fun e => plug' (ProofShape.mkApps (.lam (rawA'.subst υ) e) (args.map (·.subst υ)))),
      Qnew, (by simp only [proofEraseCtx, ← EΨ, EB]), ?_, ?_⟩
    · simpa only [ProofShape.Subst.id_lift, ProofShape.subst_id, proofEraseCtx, EB] using HRnew
    · intro e
      simpa only [ProofShape.subst_mkApps, ProofShape.subst] using EW (ProofShape.mkApps (.lam rawA' e) args)
  | @unused Γ Λ σ blocks Ψ υ plug chosen depth A u n cd rawA' args H hA RD ih =>
    obtain ⟨Γ', Λ', σ', outblocks, plug', Q, EΨ, HR, EW⟩ := ih
    obtain ⟨B, HAB, _, Qnew, EB⟩ := Q.unused heq hs hΔ hA RD.forget
    have hBout : env.HasType univs Λ' (B.subst (κ₀.liftN depth)) (.sort u) := by
      simpa only [VExpr.subst] using HAB.hasType.2.subst henv.orderedStrong Q.actual Q.target_wf
    have RDout : ScopedComputeCount (PiInertStage D 0) 0 (proofEraseCtx Λ')
        (proofErase Λ' (B.subst (κ₀.liftN depth))) (rawA'.subst υ) := by
      rw [EB]; exact .beta .refl
    have HRnew := EqPendingSupplyHistory.unused (args := args.map (·.subst υ)) HR hBout RDout
    refine ⟨_, _, _, _, (fun e => plug' (ProofShape.mkApps (.lam (rawA'.subst υ) e) (args.map (·.subst υ)))),
      Qnew, (by simp only [proofEraseCtx, ← EΨ, EB]), ?_, ?_⟩
    · simpa only [ProofShape.Subst.id_lift, ProofShape.subst_id, proofEraseCtx, EB] using HRnew
    · intro e
      simpa only [ProofShape.subst_mkApps, ProofShape.subst] using EW (ProofShape.mkApps (.lam rawA' e) args)


/-- If no enclosing arguments are pending, a retained chosen binder must
have an actual lower argument at the head of its local vector. Its chosen image
and domain typing are read from the same stored supply, not guessed from raw
syntax or from an independently selected frame. -/
theorem EqRetainedArgumentSupply.complete_head
    (hΔ : OnCtx Δ (env.IsType univs))
    (H : EqRetainedArgumentSupply Γ Δ σ blocks A y [] remaining raw)
    (S : Ctx.SubstEq env univs Δ σ σ Γ) :
    ∃ x actual extra,
      env.HasType univs Γ x A ∧
      env.IsDefEq univs Δ y (x.subst σ) (A.subst σ) ∧
      EqArgumentSupplyAt Γ Δ σ remaining actual ∧
      raw = blocks.erased (proofErase Γ x) ::
        (((actual.map (proofErase Γ)).map blocks.erased) ++ extra) := by
  obtain ⟨supplied, actual, extra, HS, hx, EP, _, ER⟩ := H
  simp only [List.append_nil] at EP
  subst supplied
  cases actual with
  | nil => cases HS.2
  | cons x actual =>
    have hx := hx x actual rfl
    obtain ⟨HT, HE⟩ := HS
    cases HE with
    | cons HY HR =>
      refine ⟨x, actual, extra, hx, HY.of_r henv hΔ
        (hx.subst henv.orderedStrong S hΔ), ⟨?_, HR⟩, ?_⟩
      · intro e he; exact HT e (List.mem_cons_of_mem x he)
      · simpa only [List.map_cons, List.cons_append] using ER.symm

/-- A stored chosen-image equality gives the actual supply square for that
binder. Unlike the earlier source-argument specialization, the chosen image
need not be syntactically the substitution of an original argument. -/
theorem EqSupplyInsertionSquare.of_chosen_argument
    (hΔ : OnCtx Δ (env.IsType univs))
    (W : EqSpecializationFrame Γ Γ' Δ σ σ' ρ τ)
    (J : EqFrameInsertionChain Γ Γ' ρ τ Λ Λ' κ υ blocks)
    (hA : env.HasType univs Γ A (.sort u))
    (hx : env.HasType univs Γ x A)
    (HY : env.IsDefEq univs Δ y (x.subst σ) (A.subst σ)) :
    EqSupplyInsertionSquare (A :: Γ) Γ Δ (σ.cons y) σ
      (VExpr.Subst.one x) (ProofShape.Subst.one (proofErase Γ x))
      (blocks.actual A :: Λ) Λ (VExpr.Subst.one (blocks.actual x))
      (ProofShape.Subst.one (blocks.erased (proofErase Γ x))) blocks.underBinder blocks := by
  have WI := EqSpecializationFrame.inst W.agree.left hA hx HY
  have W₀ := EqSpecializationFrame.of_conversion hΔ W.agree.left (.refl W.actual.wf)
  have JS := J.source_identity.under_binder W₀ hA
  have hΛ := (J.actual W).2.1.wf
  have hAup : env.HasType univs Λ (blocks.actual A) (.sort u) := by
    simpa only [EqInsertionPath.actual_sort] using J.weak hA
  have hΛA : OnCtx (blocks.actual A :: Λ) (env.IsType univs) := ⟨hΛ, u, hAup⟩
  have EXup := J.erase_actual W hx
  refine ⟨WI, ?_, J.source_identity, hΛ,
    Ctx.InstN.zero.substEq hΛA (J.weak hx), ?_, ?_, ?_⟩
  · simpa only [VExpr.id_lift, ProofShape.Subst.id_lift, VExpr.subst_id] using JS
  · intro i T hl hn
    simpa only [EXup] using erasedSubstAgreement_one hΛA (J.weak hx) hl hn
  · intro e
    simpa only [VExpr.inst_eq] using (blocks.actual_inst e x).symm
  · intro e
    simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using
      (blocks.erased_inst e (proofErase Γ x)).symm

/-- A complete retained frame derives its next consumption square and its
remaining waiting supply together. Both use the same actual head argument and
literal tail of the recorded raw vector. This is a local pop rule; matching
arbitrary later computations and recursively returning bodies is still required. -/
theorem EqRetainedArgumentSupply.consume_complete
    (hΔ : OnCtx Δ (env.IsType univs))
    (H : EqRetainedArgumentSupply Γ Δ σ blocks A y [] remaining raw)
    (W : EqSpecializationFrame Γ Γ' Δ σ σ' ρ τ)
    (J : EqFrameInsertionChain Γ Γ' ρ τ Λ Λ' κ υ blocks)
    (hA : env.HasType univs Γ A (.sort u)) :
    ∃ x actual extra,
      env.HasType univs Γ x A ∧ EqArgumentSupplyAt Γ Δ σ remaining actual ∧
      raw = blocks.erased (proofErase Γ x) ::
        (((actual.map (proofErase Γ)).map blocks.erased) ++ extra) ∧
      EqSupplyInsertionSquare (A :: Γ) Γ Δ (σ.cons y) σ
        (VExpr.Subst.one x) (ProofShape.Subst.one (proofErase Γ x))
        (blocks.actual A :: Λ) Λ (VExpr.Subst.one (blocks.actual x))
        (ProofShape.Subst.one (blocks.erased (proofErase Γ x))) blocks.underBinder blocks := by
  obtain ⟨x, actual, extra, hx, HY, HS, ER⟩ := H.complete_head hΔ W.agree.left
  exact ⟨x, actual, extra, hx, HS, ER,
    EqSupplyInsertionSquare.of_chosen_argument hΔ W J hA hx HY⟩

/-- The retained branch of an actual supplied eta origin extends the pending
history with its computed vector. Source equalities provide the new head typing;
chosen images determine the inner pending vector. The native annotation path is
kept in its original scope. -/
theorem EqPendingSupplyHistory.retained_of_computed
    (H : EqPendingSupplyHistory D Δ Γ₀ Λ₀ σ₀ blocks₀ pending₀ Ψ₀ υ₀
      Γ Λ σ blocks pending Ψ υ plug chosen depth)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) (hy : env.HasType univs Δ y (A.subst σ))
    (hx : env.HasType univs Γ x A)
    (RD : ScopedComputeCount (PiInertStage D n) cd (proofEraseCtx Λ)
      (blocks.erased (proofErase Γ A)) rawA')
    (HS : EqArgumentSupplyAt Γ Δ σ (y :: supplied) actual)
    (HE : List.Forall₂ (env.IsDefEqU univs Γ) (x :: previous) actual)
    (hextra : extra = [] ∨ pending = [])
    (ER : ((actual.map (proofErase Γ)).map blocks.erased) ++ extra = raw) :
    EqPendingSupplyHistory D Δ Γ₀ Λ₀ σ₀ blocks₀ pending₀ Ψ₀ υ₀
      (A :: Γ) (blocks.actual A :: Λ) (σ.cons y) blocks.underBinder (supplied ++ pending)
      (rawA'.subst υ :: Ψ) υ.lift
      (fun e => plug (ProofShape.mkApps (.lam rawA' e) raw)) (chosen+1) (depth+1) := by
  exact .retained H hA hy RD (EqRetainedArgumentSupply.of_computed hΓ HS HE hx hextra ER)

/-- Further actual argument computation preserves the entire retained supply
record. Head typing comes from the old head's source equality, while the pending
vector and chosen images remain fixed. Upper extras follow their actual paths. -/
theorem EqRetainedArgumentSupply.chain_compute
    (hstep : ErasedScopedPrimitiveCertificateDescent Step Step)
    (hΔ : OnCtx Δ (env.IsType univs))
    (H : EqRetainedArgumentSupply Γ Δ σ blocks A y pending remaining raw)
    (W : EqSpecializationFrame Γ Γ' Δ σ σ' ρ τ)
    (J : EqFrameInsertionChain Γ Γ' ρ τ Λ Λ' κ υ blocks)
    (RA : List.Forall₂ (ScopedCompute Step (proofEraseCtx Λ)) raw raw') :
    EqRetainedArgumentSupply Γ Δ σ blocks A y pending remaining raw' := by
  obtain ⟨supplied, actual, extra, HS, hx, EP, hextra, ER⟩ := H
  rw [← ER] at RA
  obtain ⟨actual', extra', HS', HE, ER', RX⟩ := HS.chain_compute_prefix hstep hΔ W J RA
  refine ⟨supplied, actual', extra', HS', ?_, EP, ?_, ER'⟩
  · intro x xs he
    subst actual'
    cases actual with
    | nil => cases HE
    | cons a args =>
      cases HE with
      | cons HX _ => exact (HX.of_l henv W.actual.wf (hx a args rfl)).hasType.2
  · rcases hextra with rfl | hp
    · cases RX; exact .inl rfl
    · exact .inr hp

/-- The next actual computed raw argument determines a matching chosen supply
square. No replacement image or independent consumption-map agreement is an
input. The remaining typed supply is the exact computed raw tail. -/
theorem EqRetainedArgumentSupply.compute_consume_complete
    (hstep : ErasedScopedPrimitiveCertificateDescent Step Step)
    (hΔ : OnCtx Δ (env.IsType univs))
    (H : EqRetainedArgumentSupply Γ Δ σ blocks A y [] remaining raw)
    (W : EqSpecializationFrame Γ Γ' Δ σ σ' ρ τ)
    (J : EqFrameInsertionChain Γ Γ' ρ τ Λ Λ' κ υ blocks)
    (hA : env.HasType univs Γ A (.sort u))
    (RA : List.Forall₂ (ScopedCompute Step (proofEraseCtx Λ)) raw (rawX :: rawRest)) :
    ∃ x actual extra,
      env.HasType univs Γ x A ∧ EqArgumentSupplyAt Γ Δ σ remaining actual ∧
      blocks.erased (proofErase Γ x) = rawX ∧
      ((actual.map (proofErase Γ)).map blocks.erased) ++ extra = rawRest ∧
      EqSupplyInsertionSquare (A :: Γ) Γ Δ (σ.cons y) σ
        (VExpr.Subst.one x) (ProofShape.Subst.one (proofErase Γ x))
        (blocks.actual A :: Λ) Λ (VExpr.Subst.one (blocks.actual x))
        (ProofShape.Subst.one rawX) blocks.underBinder blocks := by
  have H' := H.chain_compute hstep hΔ W J RA
  obtain ⟨x, actual, extra, hx, HS, ER, Q⟩ := H'.consume_complete hΔ W J hA
  obtain ⟨EX, ET⟩ := List.cons.inj ER.symm
  exact ⟨x, actual, extra, hx, HS, EX, ET, by simpa only [EX] using Q⟩

/-- Pop a supplied chosen frame after its actual argument computation and
realize all surviving inner pending histories through that exact argument.
The waiting tail remains separately typed at the restored base scope, with
precisely the inner history's base pending images. Reattaching that supply to
the returned body requires the recursive source-return invariant; it is not
asserted by raw wrapper concatenation here. -/
theorem EqPendingSupplyHistory.consume_complete
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΔ : OnCtx Δ (env.IsType univs))
    (W : EqSpecializationFrame Γ₀ Γ₀' Δ σ₀ σ₀' ρ τ)
    (J : EqFrameInsertionChain Γ₀ Γ₀' ρ τ Λ₀ Λ₀' κ ω incoming)
    (hA : env.HasType univs Γ₀ A (.sort u))
    (HA : EqRetainedArgumentSupply Γ₀ Δ σ₀ incoming A y [] pending₀ raw)
    (RA : List.Forall₂ (ScopedCompute (PiInertStage D n) (proofEraseCtx Λ₀)) raw (rawX :: rawRest))
    (H : EqPendingSupplyHistory D Δ (A :: Γ₀) (incoming.actual A :: Λ₀)
      (σ₀.cons y) incoming.underBinder pending₀ historyTarget historyMap
      Γ Λ σ blocks pending Ψ υ plug chosen depth) :
    ∃ (x : VExpr) (actual : List VExpr) (extra : List ProofShape)
      (Γ' Λ' : List VExpr) (σ' : VExpr.Subst) (outblocks : EqInsertionPath)
      (returned : ProofShape → ProofShape),
      env.HasType univs Γ₀ x A ∧ EqArgumentSupplyAt Γ₀ Δ σ₀ pending₀ actual ∧
      incoming.erased (proofErase Γ₀ x) = rawX ∧
      ((actual.map (proofErase Γ₀)).map incoming.erased) ++ extra = rawRest ∧
      EqSupplyInsertionSquare Γ Γ' Δ σ σ' ((VExpr.Subst.one x).liftN chosen)
        ((ProofShape.Subst.one (proofErase Γ₀ x)).liftN chosen) Λ Λ'
        ((VExpr.Subst.one (incoming.actual x)).liftN depth)
        ((ProofShape.Subst.one rawX).liftN depth) blocks outblocks ∧
      EqPendingSupplyHistory D Δ Γ₀ Λ₀ σ₀ incoming pending₀ (proofEraseCtx Λ₀) ProofShape.Subst.id
        Γ' Λ' σ' outblocks pending (proofEraseCtx Λ') ProofShape.Subst.id returned chosen depth ∧
      ∀ e : ProofShape, ProofShape.mkApps ((plug e).inst rawX) rawRest =
        ProofShape.mkApps (returned (e.subst ((ProofShape.Subst.one rawX).liftN depth))) rawRest := by
  obtain ⟨x, actual, extra, hx, HS, EX, ER, Q⟩ := HA.compute_consume_complete
    (pi_inert_stage_certificate_descent heq hs n) hΔ W J hA RA
  obtain ⟨Ξ, χ, HR⟩ := H.rebase_endpoint (proofEraseCtx Λ₀) (ProofShape.Subst.one rawX)
  obtain ⟨Γ', Λ', σ', outblocks, returned, Qnew, EΞ, HRout, EW⟩ :=
    HR.realize_returning heq hs hΔ Q rfl
  have Eχ := HR.forget.shape.2
  refine ⟨x, actual, extra, Γ', Λ', σ', outblocks, returned, hx, HS, EX, ER,
    (by simpa only [Eχ] using Qnew), HRout, ?_⟩
  intro e
  simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN, Eχ] using
    congrArg (fun f => ProofShape.mkApps f rawRest) (EW e)

/-- The actual supplied eta-origin split either extends the pending history
with its retained computed vector or exposes the original consumed branch with
all its actual paths and minima. This constructs the stronger record from the
execution witnesses; later consumption does not need an extra image agreement. -/
theorem EqSuppliedEtaContinuation.pending_history_or_consumed
    (W : EqSpecializationFrame Γ Γ' Δ σ σ' ρ τ)
    (J : EqFrameInsertionChain Γ Γ' ρ τ Λ Λ' κ υ blocks)
    (HH : EqPendingSupplyHistory D Δ Γ₀ Λ₀ σ₀ blocks₀ pending₀ Ψ₀ υ₀
      Γ Λ σ blocks pending Ξ χ plug hchosen depth)
    (hA : env.HasType univs Γ A (.sort u)) (hy : env.HasType univs Δ y (A.subst σ))
    (hx : env.HasType univs Γ x A) (hextra : extra = [] ∨ pending = [])
    (H : EqSuppliedEtaContinuation D n Γ Δ Λ σ blocks A x y chosen actual f u
      Ω out endpoint ck cost extra K) :
    (∃ A' body' raw cd cb m,
      EqPendingSupplyHistory D Δ Γ₀ Λ₀ σ₀ blocks₀ pending₀ Ψ₀ υ₀
        (A :: Γ) (blocks.actual A :: Λ) (σ.cons y) blocks.underBinder (chosen ++ pending)
        (A'.subst χ :: Ξ) χ.lift
        (fun e => plug (ProofShape.mkApps (.lam A' e) raw)) (hchosen+1) (depth+1) ∧
      endpoint = ProofShape.mkApps (.lam A' body') raw ∧
      ScopedComputeCount (PiInertStage D n) cd (proofEraseCtx Λ)
        (blocks.erased (proofErase Γ A)) A' ∧
      TypedSource (proofEraseCtx (blocks.actual A :: Λ)) (.app (f.liftN 1) (etaArgument u)) ∧
      ScopedComputeCount (PiInertStage D m) cb (proofEraseCtx (blocks.actual A :: Λ))
        (.app (f.liftN 1) (etaArgument u)) body' ∧
      PiInertTypedContinuationRun D Ω out (proofEraseCtx (blocks.actual A :: Λ))
        (fun body k => K (ProofShape.mkApps (.lam A' body) raw) k) body' ck ∧ cb+ck < cost ∧
      ∀ later j body k, ScopedComputeCount (PiInertStage D later) j
        (proofEraseCtx (blocks.actual A :: Λ)) (.app (f.liftN 1) (etaArgument u)) body →
        K (ProofShape.mkApps (.lam A' body) raw) k → cb+ck ≤ j+k) ∨
    (∃ x' rest' rawX rawRest rawExtra body' cb cs m,
      env.IsDefEq univs Γ x x' A ∧ blocks.erased (proofErase Γ x') = rawX ∧
      ((rest'.map (proofErase Γ)).map blocks.erased) ++ rawExtra = rawRest ∧
      List.Forall₂ (ScopedCompute (PiInertStage D n) (proofEraseCtx Λ)) extra rawExtra ∧
      EqSpecializationFrame (A :: Γ) Γ Δ (σ.cons y) σ (VExpr.Subst.one x')
        (ProofShape.Subst.one (proofErase Γ x')) ∧ EqArgumentSupplyAt Γ Δ σ chosen rest' ∧
      List.Forall₂ (env.IsDefEqU univs Γ) actual rest' ∧
      TypedSource (proofEraseCtx (blocks.actual A :: Λ)) (.app (f.liftN 1) (etaArgument u)) ∧
      ScopedComputeCount (PiInertStage D m) cb (proofEraseCtx (blocks.actual A :: Λ))
        (.app (f.liftN 1) (etaArgument u)) body' ∧
      TypedSource (proofEraseCtx Λ) (ProofShape.mkApps (body'.inst rawX) rawRest) ∧
      ScopedComputeCount (PiInertStage D n) cs (proofEraseCtx Λ)
        (ProofShape.mkApps (body'.inst rawX) rawRest) endpoint ∧
      PiInertTypedContinuationRun D Ω out (proofEraseCtx (blocks.actual A :: Λ))
        (PiInertApplicationContinuation D (proofEraseCtx Λ) (ProofShape.Subst.one rawX) rawRest K)
        body' (cs+ck) ∧ cb+(cs+ck) < cost ∧
      ∀ later j body k, ScopedComputeCount (PiInertStage D later) j
        (proofEraseCtx (blocks.actual A :: Λ)) (.app (f.liftN 1) (etaArgument u)) body →
        PiInertApplicationContinuation D (proofEraseCtx Λ) (ProofShape.Subst.one rawX) rawRest K body k →
        cb+(cs+ck) ≤ j+k) := by
  rcases H.2 with HR | HC
  · obtain ⟨A', body', args', raw, rawExtra, cd, cb, m,
      HS, HE, ER, RX, EO, RD, HT, RB, HK, hsmall, HM⟩ := HR
    have hextra' : rawExtra = [] ∨ pending = [] := by
      rcases hextra with rfl | hp
      · cases RX; exact .inl rfl
      · exact .inr hp
    have RD' : ScopedComputeCount (PiInertStage D n) cd (proofEraseCtx Λ)
        (blocks.erased (proofErase Γ A)) A' := by
      simpa only [J.erase_actual W hA] using RD
    have HH' := HH.retained_of_computed W.actual.wf hA hy hx RD' HS HE hextra' ER
    exact .inl ⟨A', body', raw, cd, cb, m, HH', EO, RD', HT, RB, HK, hsmall, HM⟩
  · exact .inr HC

end Lean4Lean.VEnv.Strengthening
