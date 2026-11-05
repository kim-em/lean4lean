import Lean4Lean.Theory.Typing.Strengthening.ProofErasureControlWorlds

/-! # Computational function demands in every exact context extension

A function demand remains usable after an exact interpreted renaming. This
supplies the caller's fresh-argument world without assuming arbitrary native
substitution or normalization of lambda annotations.
-/
namespace Lean4Lean.VEnv.Strengthening.RigidFunctionObservation
open _root_.Lean4Lean Params ProofShape
open AtomicControl (Atom ControlType ControlTyping)
open PureObservation (Ob)
variable [Params] [Atom]

/-- Context-indexed computational realizability. The argument has its ordinary
control type; no native certificate for it is requested. -/
def WorldComputes (Step : List ProofShape → ProofShape → ProofShape → Prop)
    (target : ControlType → ProofShape) (Δ : List ProofShape) (e : ProofShape) (t : ControlType) : Ob → Prop
  | .pi => ScopedCompute Step Δ e (target t)
  | .sort => False
  | .app keys o => match t with
    | .arrow A B => ∀ {Δ' τ}, ContextRenaming Δ Δ' τ → ∀ a,
        ControlTyping Δ' a A →
        (∀ key ∈ keys, WorldComputes Step target Δ' a A key) →
        WorldComputes Step target Δ' (.app (e.subst τ) a) B o
    | _ => False
termination_by o => sizeOf o

/-- Exact renamings preserve every demand when primitives rename and canonical
outputs are closed. No substitution theorem for general images is used. -/
theorem WorldComputes.rename
    (hstep : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextRenaming Δ Δ' τ → Step Δ' (a.subst τ) (b.subst τ))
    (hclosed : ∀ t τ, (target t).subst τ = target t)
    (H : WorldComputes Step target Δ e t o) (W : ContextRenaming Δ Δ' σ) :
    WorldComputes Step target Δ' (e.subst σ) t o := by
  cases o with
  | sort => simp only [WorldComputes] at H
  | pi =>
    simp only [WorldComputes] at H ⊢
    simpa only [hclosed] using (ScopedCompute.rename hstep H W)
  | app keys o =>
    cases t with
    | atom | sort => simp only [WorldComputes] at H
    | arrow A B =>
      simp only [WorldComputes] at H ⊢
      intro Δ'' τ W' a HA ha
      simpa only [ProofShape.subst_subst] using H (W.compose W') a HA ha

/-- Beta predecessors preserve every context-indexed demand. -/
theorem WorldComputes.beta_back (R : BetaRed e e') (H : WorldComputes Step target Δ e' t o) :
    WorldComputes Step target Δ e t o := by
  cases o with
  | sort => simp only [WorldComputes] at H
  | pi =>
    simp only [WorldComputes] at H ⊢
    exact (ScopedCompute.beta R).trans H
  | app keys o =>
    cases t with
    | atom | sort => simp only [WorldComputes] at H
    | arrow A B =>
      simp only [WorldComputes] at H ⊢
      intro Δ' τ W a HA ha
      exact WorldComputes.beta_back (.app R.subst .refl) (H W a HA ha)
termination_by sizeOf o

/-- The typed observer has a context-indexed computational interpretation.
Ordinary substitution interprets beta bodies; exact renaming alone moves
already supplied computational evidence to a later world. -/
theorem Obs.world_computes
    (hstep : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextRenaming Δ Δ' τ → Step Δ' (a.subst τ) (b.subst τ))
    (hclosed : ∀ t τ, (target t).subst τ = target t)
    (HC : target .atom = .const c [])
    (HF : ∀ {Δ}, ControlTyping Δ (.const r []) (.arrow (.arrow .atom .atom) (.sort v)) →
      WorldComputes Step target Δ (.const r []) (.arrow (.arrow .atom .atom) (.sort v)) (.app [.app [.pi] .pi] .pi))
    (H : Obs c r v Ω S e t o) (W : ContextSubstitution Ω Δ σ)
    (hσ : ∀ i t key, S i t key → WorldComputes Step target Δ (σ i) t key) :
    WorldComputes Step target Δ (e.subst σ) t o := by
  induction H generalizing Δ σ with
  | var _ _ h => exact hσ _ _ _ h
  | terminal => simp only [ProofShape.subst, WorldComputes, HC]; exact .refl
  | rigid HT => exact HF (HT.subst W)
  | app HT Hf Ha ihf iha =>
    have HR := ihf W hσ
    simp only [WorldComputes] at HR
    have R := HR ContextRenaming.identity _ ((HT.argument Hf.typing).subst W) (fun key hk => iha key hk W hσ)
    simpa only [ProofShape.subst_id, ProofShape.subst] using R
  | @lam Ω L b A B keys S o HT HK HB ih =>
    simp only [WorldComputes]
    intro Δ' τ W' a HA ha
    have WW : ContextSubstitution Ω Δ' (σ.comp τ) :=
      ContextSubstitution.compose_world W W'.interpretation
    have WB : ContextSubstitution (L :: Ω) Δ' ((σ.comp τ).cons a) :=
      HT.lambda_substitution WW HA
    have HR := ih WB (fun i t key hi => by
      cases i with
      | zero => obtain ⟨rfl, hk⟩ := hi; exact ha key hk
      | succ i => exact (hσ i t key hi).rename hstep hclosed W')
    have E : (b.subst (σ.comp τ).lift).inst a = b.subst ((σ.comp τ).cons a) := by
      simp only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN, ProofShape.subst_subst]
      congr 1
      funext i
      cases i with
      | zero => rfl
      | succ i => simp only [Subst.comp, Subst.lift, Subst.one, Subst.cons,
          ProofShape.lift_subst_cons, ProofShape.subst_id]
    have R := WorldComputes.beta_back (E ▸ (BetaRed.beta (A := L.subst (σ.comp τ)))) HR
    simpa only [ProofShape.subst_subst, ProofShape.subst, Subst.comp_lift] using R

end Lean4Lean.VEnv.Strengthening.RigidFunctionObservation
