import Lean4Lean.Theory.Typing.Strengthening.ProofErasureSortedEtaCoreApplication
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEtaSpineCleanup

/-! # Constant-spine cleanup with full-core eta histories

Proper prefixes expose their constants by beta. Actual non-function typing
excludes a whole eta origin at inspected constructor majors.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private erase_app_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
open private subst_shift from Lean4Lean.Theory.Typing.Strengthening.ProofErasureStagedAnnotationChecking
variable [Params] {D : Definitions}

/-- Every paired constant spine either beta-exposes its exact constant and
universes with paired arguments, or is a single outer eta origin. Eta wrappers
on proper prefixes are consumed using actual application typing, including
proof inputs. Whole-spine eta is deliberately retained in the second outcome. -/
theorem sorted_eta_core_constant_spine_cleanup (hs : D.Sound env univs)
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (hA : env.HasType univs Γ₀ A (.sort u))
    (hf : env.HasType univs Γ₀ f (.forallE A B)) (hn : ¬ IsProof Γ₀ f)
    (V : AmbientVariant (EtaCoreDomains D (proofErase Γ₀ A) (proofErase Γ₀ f))
      (SortedEtaAtom u (EtaCoreOrigin D (proofErase Γ₀ A) (proofErase Γ₀ f))) n
      (ProofShape.mkApps (.const c ls) args) b)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (Ee : proofErase Γ e = ProofShape.mkApps (.const c ls) args)
    (W : ContextRenaming (proofEraseCtx Γ₀) (proofEraseCtx Γ) (fun i => .bvar (i+n))) :
    (∃ args', ProofShape.BetaRed b (ProofShape.mkApps (.const c ls) args') ∧
      List.Forall₂ (AmbientVariant (EtaCoreDomains D (proofErase Γ₀ A) (proofErase Γ₀ f))
        (SortedEtaAtom u (EtaCoreOrigin D (proofErase Γ₀ A) (proofErase Γ₀ f))) n) args args') ∨
    (∃ C g, EtaCoreOrigin D (proofErase Γ₀ A) (proofErase Γ₀ f) C g ∧
      ProofShape.mkApps (.const c ls) args = g.liftN n ∧ b = (sortedEta u C g).liftN n) := by
  induction args using List.snoc_induction generalizing b Γ e T with
  | nil =>
    cases V with
    | refl => exact .inl ⟨[], .refl, .nil⟩
    | origin HO => exact .inr (sorted_eta_origin_constant_spine HO)
  | snoc args x ih =>
    rw [ProofShape.mkApps_snoc] at V Ee
    cases V with
    | refl => exact .inl ⟨args ++ [x], by rw [ProofShape.mkApps_snoc]; exact .refl,
        List.Forall₂.rfl (fun _ _ => AmbientVariant.refl)⟩
    | origin HO =>
      apply Or.inr
      exact sorted_eta_origin_constant_spine (by simpa only [ProofShape.mkApps_snoc] using HO)
    | app VF VX =>
      obtain ⟨eF, eX, rfl, _, EF, _⟩ := erase_app_inv Ee
      obtain ⟨_, _, hF, _⟩ := ht.app_inv henv hΓ
      rcases ih VF hΓ hF EF W with ⟨args', RB, VA⟩ | ⟨C, g, HG, EG, EB⟩
      · refine .inl ⟨args' ++ [_], ?_, VA.append' (.cons VX .nil)⟩
        rw [ProofShape.mkApps_snoc]
        exact .app RB .refl
      · refine .inl ⟨args ++ [_], ?_,
          (List.Forall₂.rfl (fun _ _ => AmbientVariant.refl)).append' (.cons VX .nil)⟩
        rw [ProofShape.mkApps_snoc, EG, EB]
        exact sorted_eta_core_right_application_cleanup hs hΓ₀ hA hf hn HG VX hΓ ht
          (by simpa only [EG] using Ee) W

/-- Supplying a further argument exposes even an outer eta wrapper. The result
has the original constant and universe list and pointwise paired arguments.
This is an unconditional prefix-cleanup result for the actual typed application. -/
theorem sorted_eta_core_applied_constant_spine_cleanup (hs : D.Sound env univs)
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (hA : env.HasType univs Γ₀ A (.sort u))
    (hf : env.HasType univs Γ₀ f (.forallE A B)) (hn : ¬ IsProof Γ₀ f)
    (VF : AmbientVariant (EtaCoreDomains D (proofErase Γ₀ A) (proofErase Γ₀ f))
      (SortedEtaAtom u (EtaCoreOrigin D (proofErase Γ₀ A) (proofErase Γ₀ f))) n
      (ProofShape.mkApps (.const c ls) args) g)
    (VX : AmbientVariant (EtaCoreDomains D (proofErase Γ₀ A) (proofErase Γ₀ f))
      (SortedEtaAtom u (EtaCoreOrigin D (proofErase Γ₀ A) (proofErase Γ₀ f))) n x y)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (Ee : proofErase Γ e = .app (ProofShape.mkApps (.const c ls) args) x)
    (W : ContextRenaming (proofEraseCtx Γ₀) (proofEraseCtx Γ) (fun i => .bvar (i+n))) :
    ∃ args', ProofShape.BetaRed (.app g y) (ProofShape.mkApps (.const c ls) (args' ++ [y])) ∧
      List.Forall₂ (AmbientVariant (EtaCoreDomains D (proofErase Γ₀ A) (proofErase Γ₀ f))
        (SortedEtaAtom u (EtaCoreOrigin D (proofErase Γ₀ A) (proofErase Γ₀ f))) n) (args ++ [x]) (args' ++ [y]) := by
  obtain ⟨eF, eX, rfl, _, EF, _⟩ := erase_app_inv Ee
  obtain ⟨_, _, hF, _⟩ := ht.app_inv henv hΓ
  rcases sorted_eta_core_constant_spine_cleanup hs hΓ₀ hA hf hn VF hΓ hF EF W with
    ⟨args', RG, VA⟩ | ⟨C, g₀, HG, EG, EB⟩
  · refine ⟨args', ?_, VA.append' (.cons VX .nil)⟩
    rw [ProofShape.mkApps_snoc]
    exact .app RG .refl
  · refine ⟨args, ?_, (List.Forall₂.rfl (fun _ _ => AmbientVariant.refl)).append' (.cons VX .nil)⟩
    rw [ProofShape.mkApps_snoc, EG, EB]
    exact sorted_eta_core_right_application_cleanup hs hΓ₀ hA hf hn HG VX hΓ ht
      (by simpa only [EG] using Ee) W

/-- A constant spine that cannot have a Pi type exposes the same head and
universes after beta cleanup. This applies to an inspected iota major using
its actual redex typing, without a separate family-exposure certificate. -/
theorem sorted_eta_core_nonfunction_spine_cleanup (hs : D.Sound env univs)
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (hA : env.HasType univs Γ₀ A (.sort u))
    (hf : env.HasType univs Γ₀ f (.forallE A B)) (hn : ¬ IsProof Γ₀ f)
    (V : AmbientVariant (EtaCoreDomains D (proofErase Γ₀ A) (proofErase Γ₀ f))
      (SortedEtaAtom u (EtaCoreOrigin D (proofErase Γ₀ A) (proofErase Γ₀ f))) n
      (ProofShape.mkApps (.const c ls) args) b)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (hpi : ∀ C E, ¬ env.HasType univs Γ e (.forallE C E))
    (Ee : proofErase Γ e = ProofShape.mkApps (.const c ls) args)
    (W : ContextRenaming (proofEraseCtx Γ₀) (proofEraseCtx Γ) (fun i => .bvar (i+n))) :
    ∃ args', ProofShape.BetaRed b (ProofShape.mkApps (.const c ls) args') ∧
      List.Forall₂ (AmbientVariant (EtaCoreDomains D (proofErase Γ₀ A) (proofErase Γ₀ f))
        (SortedEtaAtom u (EtaCoreOrigin D (proofErase Γ₀ A) (proofErase Γ₀ f))) n) args args' := by
  rcases sorted_eta_core_constant_spine_cleanup hs hΓ₀ hA hf hn V hΓ ht Ee W with H | ⟨C, g, HG, EG, _⟩
  · exact H
  · have hne : ¬ IsProof Γ e := by
      intro hp
      have H := congrArg ProofShape.constHead ((proofErase_eq_proof.2 hp).symm.trans Ee)
      simp only [ProofShape.constHead, ProofShape.constHead_mkApps] at H
      cases H
    obtain ⟨g₀, HE, Eg⟩ := proofErase_scoped_compute_realize (erased_level_core_descent hs)
      hΓ₀ hf rfl rfl (HG.2.scoped (fun H => .base H))
    obtain ⟨X, Y, hPi, _⟩ := proofErase_interpreted_function_carrier hΓ₀ hA HE.hasType.2
      W.interpretation hΓ ht hne (by simpa only [subst_shift, Eg] using Ee.trans EG)
    exact (hpi X Y hPi).elim

end Lean4Lean.VEnv.Strengthening
