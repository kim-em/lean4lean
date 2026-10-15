import Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedLoopReadout
import Lean4Lean.Theory.Typing.Confluence.EtaSpine

/-! # Pi exposure from typed scoped comparisons

For sort-typed endpoints, eta and structure checking cannot hide the outer Pi.
A scoped certificate against a displayed Pi therefore supplies a computation
to a Pi in the same primitive relation. This uses typed replay, not completeness
or confluence of that relation.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private erase_lam_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta

private theorem beta_pi (R : ProofShape.BetaRed a b) (E : a = .forallE A B) :
    ∃ A' B', b = .forallE A' B' := by
  induction R generalizing A B with
  | refl => exact ⟨_, _, E⟩
  | trans _ _ ih₁ ih₂ => obtain ⟨_, _, E'⟩ := ih₁ E; exact ih₂ E'
  | forallE => cases E; exact ⟨_, _, rfl⟩
  | app | proj | lam | beta => cases E

/-- Scoped computation preserves a displayed Pi head when primitives have
constant or projection heads. Body contexts may change along the path. -/
theorem ProofShape.ScopedCompute.forallE_head
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (R : ScopedCompute Step Δ (.forallE A B) out) : ∃ A' B', out = .forallE A' B' := by
  generalize E : ProofShape.forallE A B = a at R
  induction R generalizing A B with
  | base H => exact (E ▸ hhead H).elim
  | beta H => exact beta_pi H E.symm
  | trans _ _ ih₁ ih₂ => obtain ⟨_, _, E'⟩ := ih₁ E; exact ih₂ E'.symm
  | forallE => cases E; exact ⟨_, _, rfl⟩
  | app | proj | lam => cases E

variable [Params]
private theorem sort_not_lam (hΓ : OnCtx Γ (env.IsType univs))
    (he : env.HasType univs Γ e (.sort u)) (E : proofErase Γ e = .lam A b) : False := by
  obtain ⟨D, body, rfl, _, _, _⟩ := erase_lam_inv E
  obtain ⟨⟨_, hD⟩, _, hb⟩ := he.lam_inv henv hΓ
  exact (he.uniqU henv hΓ (HasType.lam hD hb)).sort_forallE_inv henv hΓ

private theorem sort_not_constructor (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ e (.sort u))
    (hi : env.projections family info) (hx : info.nindices = 0)
    (hp : ps.length = info.nparams) (hf : fields.length = info.numFields)
    (Ee : proofErase Γ e = ProofShape.mkApps (.const info.ctorName ls) (ps ++ fields)) : False := by
  obtain ⟨args, rfl, Hargs⟩ := proofErase_const_spine_inv Ee
  have hlen := congrArg List.length Hargs
  simp only [List.length_append, List.length_map, hp, hf] at hlen
  have hnat := structure_constructor_family hΓ hi hx hlen.symm ht
  exact HasType.sortTele_not_rigid (as := []) (doms := []) hΓ (henv.projectionRigid hi) ht hnat

private theorem pi_exposure_pair
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (H : ScopedCompare Step Δ mode a b)
    (hΓ : OnCtx Γ (env.IsType univs))
    (he : env.HasType univs Γ e (.sort u)) (hf : env.HasType univs Γ f (.sort v))
    (EΔ : proofEraseCtx Γ = Δ) (Ee : proofErase Γ e = a) (Ef : proofErase Γ f = b) :
    ((∃ A B, a = .forallE A B) → ∃ A B, ScopedCompute Step Δ b (.forallE A B)) ∧
    ((∃ A B, b = .forallE A B) → ∃ A B, ScopedCompute Step Δ a (.forallE A B)) := by
  induction H generalizing Γ e f u v with
  | leaf H =>
    cases H with
    | refl => exact ⟨fun ⟨A, B, E⟩ => ⟨A, B, E ▸ .refl⟩, fun ⟨A, B, E⟩ => ⟨A, B, E ▸ .refl⟩⟩
    | sort | const => constructor <;> rintro ⟨_, _, E⟩ <;> cases E
    | etaL H =>
      obtain ⟨_, _, E, _⟩ := H.shape
      exact (sort_not_lam hΓ he (Ee.trans E)).elim
    | etaR H =>
      obtain ⟨_, _, E, _⟩ := H.shape
      exact (sort_not_lam hΓ hf (Ef.trans E)).elim
  | app | proj => constructor <;> rintro ⟨_, _, E⟩ <;> cases E
  | forallE | forallSorted => exact ⟨fun _ => ⟨_, _, .refl⟩, fun _ => ⟨_, _, .refl⟩⟩
  | lam | lamSorted | lamCommon | etaBodyL | etaLams => exact (sort_not_lam hΓ he Ee).elim
  | etaBodyR => exact (sort_not_lam hΓ hf Ef).elim
  | structFields hi hx hp hfields => exact (sort_not_constructor hΓ he hi hx hp hfields Ee).elim
  | compute Ra Rb HC ih =>
    have W : Ctx.LiftN 0 0 Γ Γ := .zero []
    obtain ⟨e', HE, EE⟩ := proofErase_scoped_compute_descend hstep hΓ hΓ W he EΔ
      (by simpa only [ProofShape.liftN_zero, Ee] using Ra)
    obtain ⟨f', HF, EF⟩ := proofErase_scoped_compute_descend hstep hΓ hΓ W hf EΔ
      (by simpa only [ProofShape.liftN_zero, Ef] using Rb)
    simp only [ProofShape.liftN_zero] at EE EF
    have IH := ih hΓ HE.hasType.2 HF.hasType.2 EΔ EE EF
    constructor
    · rintro ⟨A, B, E⟩
      obtain ⟨A', B', R⟩ := IH.1 ((E ▸ Ra).forallE_head hhead)
      exact ⟨A', B', Rb.trans R⟩
    · rintro ⟨A, B, E⟩
      obtain ⟨A', B', R⟩ := IH.2 ((E ▸ Rb).forallE_head hhead)
      exact ⟨A', B', Ra.trans R⟩
  | symm H ih => exact (ih hΓ hf he EΔ Ef Ee).symm

/-- A scoped comparison of sort-typed terms with a displayed erased Pi exposes
a Pi by computation on the other side. The computation uses exactly `Step`,
including at all nested contexts; no larger reduction relation is introduced. -/
theorem proofErase_scoped_pi_exposure
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (hΓ : OnCtx Γ (env.IsType univs))
    (he : env.HasType univs Γ e (.sort u)) (hf : env.HasType univs Γ f (.sort v))
    (H : ScopedCompare Step (proofEraseCtx Γ) mode (proofErase Γ e) (proofErase Γ f))
    (E : proofErase Γ e = .forallE A B) :
    ∃ A' B', ScopedCompute Step (proofEraseCtx Γ) (proofErase Γ f) (.forallE A' B') :=
  (pi_exposure_pair hstep hhead H hΓ he hf rfl rfl rfl).1 ⟨A, B, E⟩

end Lean4Lean.VEnv.Strengthening
