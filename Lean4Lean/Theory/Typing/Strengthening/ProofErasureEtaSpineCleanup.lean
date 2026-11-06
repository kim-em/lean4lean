import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEtaApplicationCleanup

/-! # Exposing constant spines hidden by protected eta wrappers

Beta removes eta wrappers on proper function prefixes. The whole paired term
may still be an eta wrapper; that outcome is recorded explicitly. Once the
paired spine is applied to another argument, its whole wrapper is removed too.
Exact constants and universes survive, and arguments keep their paired origins.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private erase_app_inv beta_eq from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta

/-- A protected eta atom at a constant spine can only be the short-to-long
orientation. Its exact ambient origin is retained for later application. -/
theorem sorted_eta_origin_constant_spine
    (H : LiftedOrigin (SortedEtaAtom u EtaGuard) n (ProofShape.mkApps (.const c ls) args) b) :
    ∃ A f, EtaGuard A f ∧ ProofShape.mkApps (.const c ls) args = f.liftN n ∧
      b = (sortedEta u A f).liftN n := by
  obtain ⟨a, b₀, H, EA, EB⟩ := H
  cases H with
  | etaL H =>
    have E := congrArg ProofShape.constHead EA
    simp only [ProofShape.constHead_mkApps, sortedEta, ProofShape.liftN, ProofShape.constHead] at E
    cases E
  | @etaR A _ H => exact ⟨A, a, H, EA, EB⟩

open private subst_shift from Lean4Lean.Theory.Typing.Strengthening.ProofErasureStagedAnnotationChecking
variable [Params]

/-- Every paired constant spine either beta-exposes its exact constant and
universes with paired arguments, or is a single outer eta origin. Eta wrappers
on proper prefixes are consumed using actual application typing, including
proof inputs. Whole-spine eta is deliberately retained in the second outcome. -/
theorem sorted_eta_constant_spine_cleanup
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (hA : env.HasType univs Γ₀ A (.sort u))
    (hf : env.HasType univs Γ₀ f (.forallE A B)) (hn : ¬ IsProof Γ₀ f)
    (V : AmbientVariant (EtaBetaDomains (proofErase Γ₀ A) (proofErase Γ₀ f))
      (SortedEtaAtom u (EtaBetaOrigin (proofErase Γ₀ A) (proofErase Γ₀ f))) n
      (ProofShape.mkApps (.const c ls) args) b)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (Ee : proofErase Γ e = ProofShape.mkApps (.const c ls) args)
    (W : ContextRenaming (proofEraseCtx Γ₀) (proofEraseCtx Γ) (fun i => .bvar (i+n))) :
    (∃ args', ProofShape.BetaRed b (ProofShape.mkApps (.const c ls) args') ∧
      List.Forall₂ (AmbientVariant (EtaBetaDomains (proofErase Γ₀ A) (proofErase Γ₀ f))
        (SortedEtaAtom u (EtaBetaOrigin (proofErase Γ₀ A) (proofErase Γ₀ f))) n) args args') ∨
    (∃ C g, EtaBetaOrigin (proofErase Γ₀ A) (proofErase Γ₀ f) C g ∧
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
        exact sorted_eta_right_application_cleanup hΓ₀ hA hf hn HG VX hΓ ht
          (by simpa only [EG] using Ee) W

/-- Supplying a further argument exposes even an outer eta wrapper. The result
has the original constant and universe list and pointwise paired arguments.
This is an unconditional prefix-cleanup result for the actual typed application. -/
theorem sorted_eta_applied_constant_spine_cleanup
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (hA : env.HasType univs Γ₀ A (.sort u))
    (hf : env.HasType univs Γ₀ f (.forallE A B)) (hn : ¬ IsProof Γ₀ f)
    (VF : AmbientVariant (EtaBetaDomains (proofErase Γ₀ A) (proofErase Γ₀ f))
      (SortedEtaAtom u (EtaBetaOrigin (proofErase Γ₀ A) (proofErase Γ₀ f))) n
      (ProofShape.mkApps (.const c ls) args) g)
    (VX : AmbientVariant (EtaBetaDomains (proofErase Γ₀ A) (proofErase Γ₀ f))
      (SortedEtaAtom u (EtaBetaOrigin (proofErase Γ₀ A) (proofErase Γ₀ f))) n x y)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (Ee : proofErase Γ e = .app (ProofShape.mkApps (.const c ls) args) x)
    (W : ContextRenaming (proofEraseCtx Γ₀) (proofEraseCtx Γ) (fun i => .bvar (i+n))) :
    ∃ args', ProofShape.BetaRed (.app g y) (ProofShape.mkApps (.const c ls) (args' ++ [y])) ∧
      List.Forall₂ (AmbientVariant (EtaBetaDomains (proofErase Γ₀ A) (proofErase Γ₀ f))
        (SortedEtaAtom u (EtaBetaOrigin (proofErase Γ₀ A) (proofErase Γ₀ f))) n) (args ++ [x]) (args' ++ [y]) := by
  obtain ⟨eF, eX, rfl, _, EF, _⟩ := erase_app_inv Ee
  obtain ⟨_, _, hF, _⟩ := ht.app_inv henv hΓ
  rcases sorted_eta_constant_spine_cleanup hΓ₀ hA hf hn VF hΓ hF EF W with
    ⟨args', RG, VA⟩ | ⟨C, g₀, HG, EG, EB⟩
  · refine ⟨args', ?_, VA.append' (.cons VX .nil)⟩
    rw [ProofShape.mkApps_snoc]
    exact .app RG .refl
  · refine ⟨args, ?_, (List.Forall₂.rfl (fun _ _ => AmbientVariant.refl)).append' (.cons VX .nil)⟩
    rw [ProofShape.mkApps_snoc, EG, EB]
    exact sorted_eta_right_application_cleanup hΓ₀ hA hf hn HG VX hΓ ht
      (by simpa only [EG] using Ee) W

/-- A spine typed at a rigid family cannot be the short side of a whole-function
eta origin. Thus every paired spine at such a carrier beta-exposes its exact
constant and universes, with all argument relations retained. -/
theorem sorted_eta_rigid_family_spine_cleanup
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (hA : env.HasType univs Γ₀ A (.sort u))
    (hf : env.HasType univs Γ₀ f (.forallE A B)) (hn : ¬ IsProof Γ₀ f)
    (V : AmbientVariant (EtaBetaDomains (proofErase Γ₀ A) (proofErase Γ₀ f))
      (SortedEtaAtom u (EtaBetaOrigin (proofErase Γ₀ A) (proofErase Γ₀ f))) n
      (ProofShape.mkApps (.const c ls) args) b)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ e (VExpr.mkApps (.const family levels) params))
    (hr : env.Rigid family)
    (Ee : proofErase Γ e = ProofShape.mkApps (.const c ls) args)
    (W : ContextRenaming (proofEraseCtx Γ₀) (proofEraseCtx Γ) (fun i => .bvar (i+n))) :
    ∃ args', ProofShape.BetaRed b (ProofShape.mkApps (.const c ls) args') ∧
      List.Forall₂ (AmbientVariant (EtaBetaDomains (proofErase Γ₀ A) (proofErase Γ₀ f))
        (SortedEtaAtom u (EtaBetaOrigin (proofErase Γ₀ A) (proofErase Γ₀ f))) n) args args' := by
  rcases sorted_eta_constant_spine_cleanup hΓ₀ hA hf hn V hΓ ht Ee W with H | ⟨C, g, HG, EG, _⟩
  · exact H
  · have hne : ¬ IsProof Γ e := by
      intro hp
      have H := congrArg ProofShape.constHead ((proofErase_eq_proof.2 hp).symm.trans Ee)
      simp only [ProofShape.constHead, ProofShape.constHead_mkApps] at H
      cases H
    obtain ⟨g₀, RG, Eg⟩ := proofErase_beta_replay hΓ₀ hf HG.2
    have hg := (beta_eq hΓ₀ hf RG).hasType.2
    obtain ⟨X, Y, hPi, _⟩ := proofErase_interpreted_function_carrier hΓ₀ hA hg
      W.interpretation hΓ ht hne (by simpa only [subst_shift, Eg] using Ee.trans EG)
    obtain ⟨_, hFamily⟩ := ht.isType henv hΓ
    exact (IsDefEqU.rigidApp_forallE_inv henv hΓ hr hFamily (ht.uniqU henv hΓ hPi)).elim

/-- Projection on a paired saturated constructor simulates after beta cleanup
of eta wrappers in its prefixes. The original family typing excludes an outer
function wrapper; selection retains the corresponding paired field. -/
theorem sorted_eta_projection_spine_cleanup
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (hA : env.HasType univs Γ₀ A (.sort u))
    (hf : env.HasType univs Γ₀ f (.forallE A B)) (hn : ¬ IsProof Γ₀ f)
    (hi : env.projections s info)
    (hlen : args.length = info.nparams + info.numFields)
    (hget : args[info.nparams + i]? = some field)
    (V : AmbientVariant (EtaBetaDomains (proofErase Γ₀ A) (proofErase Γ₀ f))
      (SortedEtaAtom u (EtaBetaOrigin (proofErase Γ₀ A) (proofErase Γ₀ f))) n
      (ProofShape.mkApps (.const info.ctorName ls) args) b)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ e (VExpr.mkApps (.const s levels) params))
    (Ee : proofErase Γ e = ProofShape.mkApps (.const info.ctorName ls) args)
    (W : ContextRenaming (proofEraseCtx Γ₀) (proofEraseCtx Γ) (fun i => .bvar (i+n))) :
    ∃ field', Compute (ErasedLevelCore D) (.proj s i b) field' ∧
      AmbientVariant (EtaBetaDomains (proofErase Γ₀ A) (proofErase Γ₀ f))
        (SortedEtaAtom u (EtaBetaOrigin (proofErase Γ₀ A) (proofErase Γ₀ f))) n field field' := by
  obtain ⟨args', RB, HA⟩ := sorted_eta_rigid_family_spine_cleanup hΓ₀ hA hf hn V hΓ ht
    (henv.projectionRigid hi) Ee W
  obtain ⟨hj, HE⟩ := List.getElem?_eq_some_iff.1 hget
  have hj' : info.nparams + i < args'.length := by rw [← HA.length_eq]; exact hj
  refine ⟨args'[info.nparams + i]'hj', ?_, ?_⟩
  · exact (Compute.proj (.beta RB)).trans (.base (.inl (.inl (.inl
      (.projIota hi (HA.length_eq.symm.trans hlen) (List.getElem?_eq_getElem hj'))))))
  · rw [← HE]
    exact HA.getElem_of _ hj hj'

end Lean4Lean.VEnv.Strengthening
