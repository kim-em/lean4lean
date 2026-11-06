import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqSpineInstantiation

/-! # Composable target agreement for application frames

An actual typed endpoint substitution is paired with the target substitutions
on either side. Their agreement is semantic, not syntactic factorization.
Consumption and context conversion supply these witnesses; they compose and
lift under retained binders. Guarded computation is never substituted.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private typed_comp
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureStablePrimitives
variable [Params]

private theorem paired_of_lookup (hΓ : OnCtx Γ (env.IsType univs))
    (H : ∀ {i A}, Lookup Γ i A → env.IsDefEq univs Δ (σ i) (σ' i) (A.subst σ)) :
    Ctx.SubstEq env univs Δ σ σ' Γ := by
  induction Γ generalizing σ σ' with
  | nil => exact .nil
  | cons A Γ ih =>
    obtain ⟨hΓ, u, hA⟩ := hΓ
    refine .cons (ih hΓ ?_) hA ?_
    · intro i B hl
      simpa only [VExpr.lift_subst, VExpr.Subst.tail] using H (Lookup.succ hl)
    · simpa only [VExpr.lift_subst, VExpr.Subst.head] using H Lookup.zero

private theorem paired_trans (hΔ : OnCtx Δ (env.IsType univs))
    (H : Ctx.SubstEq env univs Δ σ₁ σ₂ Γ) (K : Ctx.SubstEq env univs Δ σ₂ σ₃ Γ) :
    Ctx.SubstEq env univs Δ σ₁ σ₃ Γ := by
  apply paired_of_lookup H.wf
  intro i A hl
  exact ((H.lookup hl).toU.trans henv hΔ (K.lookup hl).toU).of_l henv hΔ (H.lookup hl).hasType.1

private theorem paired_pullback (hΓ' : OnCtx Γ' (env.IsType univs))
    (hΔ : OnCtx Δ (env.IsType univs))
    (W : Ctx.SubstEq env univs Γ' ρ ρ Γ) (H : Ctx.SubstEq env univs Δ σ σ' Γ') :
    Ctx.SubstEq env univs Δ (ρ.comp σ) (ρ.comp σ') Γ := by
  apply paired_of_lookup W.wf
  intro i A hl
  simpa only [VExpr.Subst.comp, VExpr.subst_subst] using
    (W.lookup hl).hasType.1.substDF henv.orderedStrong hΓ' hΔ H

/-- A concrete application-frame substitution together with agreement between
its incoming target assignment and its outgoing one. The actual map and its
raw erasure are retained. Agreement is data to derive from argument ancestry;
ordinary context interpretation alone does not imply it. -/
structure EqSpecializationFrame (Γ Γ' Δ : List VExpr)
    (σ σ' ρ : VExpr.Subst) (τ : ProofShape.Subst) : Prop where
  target : Ctx.SubstEq env univs Δ σ' σ' Γ'
  actual : Ctx.SubstEq env univs Γ' ρ ρ Γ
  erase : ErasedSubstAgreement Γ Γ' ρ τ
  agree : Ctx.SubstEq env univs Δ σ (ρ.comp σ') Γ

/-- Forget target agreement to obtain the actual raw context interpretation
required by the concrete continuation frame. -/
theorem EqSpecializationFrame.interpretation
    (H : EqSpecializationFrame Γ Γ' Δ σ σ' ρ τ) :
    ContextSubstitution (proofEraseCtx Γ) (proofEraseCtx Γ') τ :=
  ContextSubstitution.of_typed H.target.wf H.actual H.erase

/-- The two ways through a frame agree on every actually typed source term. -/
theorem EqSpecializationFrame.term
    (hΔ : OnCtx Δ (env.IsType univs))
    (H : EqSpecializationFrame Γ Γ' Δ σ σ' ρ τ)
    (he : env.HasType univs Γ e T) :
    env.IsDefEq univs Δ (e.subst σ) ((e.subst ρ).subst σ') (T.subst σ) := by
  simpa only [VExpr.subst_subst] using he.substDF henv.orderedStrong H.actual.wf hΔ H.agree

/-- Application-frame agreement composes through the actual intermediate
realization. The resulting raw substitution is the literal endpoint composite;
no computation history is transported through either map. -/
theorem EqSpecializationFrame.compose
    (hΔ : OnCtx Δ (env.IsType univs))
    (H : EqSpecializationFrame Γ Γ' Δ σ σ' ρ τ)
    (K : EqSpecializationFrame Γ' Γ'' Δ σ' σ'' ρ' τ') :
    EqSpecializationFrame Γ Γ'' Δ σ σ'' (ρ.comp ρ') (τ.comp τ') := by
  refine ⟨K.target, typed_comp K.target.wf H.actual K.actual, ?_, ?_⟩
  · intro i A hl hn
    exact (proofErase_subst_with K.target.wf K.actual (H.actual.lookup hl).hasType.1 K.erase).trans
      (congrArg (·.subst τ') (H.erase hl hn))
  · have HH := paired_trans hΔ H.agree (paired_pullback H.target.wf hΔ H.actual K.agree)
    have EC : (ρ.comp ρ').comp σ'' = ρ.comp (ρ'.comp σ'') := by
      funext i
      exact VExpr.subst_subst
    simpa only [EC] using HH

/-- A consumed actual binder supplies a frame whenever its chosen target
image agrees with the actual argument's specialization. This is the same
ancestry equality already derived by shared-completion eta supply. -/
theorem EqSpecializationFrame.inst
    (W : Ctx.SubstEq env univs Δ σ σ Γ)
    (hA : env.HasType univs Γ A (.sort u)) (hx : env.HasType univs Γ x A)
    (Hxy : env.IsDefEq univs Δ y (x.subst σ) (A.subst σ)) :
    EqSpecializationFrame (A :: Γ) Γ Δ (σ.cons y) σ (VExpr.Subst.one x)
      (ProofShape.Subst.one (proofErase Γ x)) := by
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨W.wf, u, hA⟩
  refine ⟨W, Ctx.InstN.zero.substEq hΓA hx, erasedSubstAgreement_one hΓA hx, ?_⟩
  have EC : (VExpr.Subst.one x).comp σ = σ.cons (x.subst σ) := by
    funext i; cases i <;> rfl
  rw [EC]
  exact .cons W hA Hxy

/-- Computing the actual argument produces a consumption frame automatically:
the original target image remains the original argument's specialization.
The result retains the actual computed argument and its exact erasure. -/
theorem EqSpecializationFrame.computed_inst
    (hsource : ErasedScopedPrimitiveDescent Source)
    (hΔ : OnCtx Δ (env.IsType univs))
    (W : Ctx.SubstEq env univs Δ σ σ Γ)
    (hA : env.HasType univs Γ A (.sort u)) (hx : env.HasType univs Γ x A)
    (RX : ScopedCompute Source (proofEraseCtx Γ) (proofErase Γ x) rawX) :
    ∃ x', env.IsDefEq univs Γ x x' A ∧ proofErase Γ x' = rawX ∧
      EqSpecializationFrame (A :: Γ) Γ Δ (σ.cons (x.subst σ)) σ (VExpr.Subst.one x')
        (ProofShape.Subst.one rawX) := by
  obtain ⟨x', HX, EX⟩ := proofErase_scoped_compute_realize hsource W.wf hx rfl rfl RX
  exact ⟨x', HX, EX, by simpa only [EX] using
    EqSpecializationFrame.inst W hA HX.hasType.2 (HX.subst henv.orderedStrong W hΔ)⟩

/-- Source context conversion is an identity frame retaining the same chosen
target assignment. It includes a retained lambda's changed annotation. -/
theorem EqSpecializationFrame.of_conversion
    (hΔ : OnCtx Δ (env.IsType univs))
    (W : Ctx.SubstEq env univs Δ σ σ Γ) (C : IsDefEqCtx env univs [] Γ Γ') :
    EqSpecializationFrame Γ Γ' Δ σ σ VExpr.Subst.id ProofShape.Subst.id := by
  have WT := substEq_source_convert hΔ C W
  refine ⟨WT, substEq_source_convert WT.wf (C.symm henv.ordered)
    (Ctx.SubstEq.id henv.ordered WT.wf), ?_, W⟩
  intro i A hl hn
  have hn' : ¬ IsProof Γ' (.bvar i) := mt (isProof_defeqCtx C).2 hn
  simp only [VExpr.Subst.id, proofErase, if_neg hn', ProofShape.Subst.id]

/-- Lift a frame beneath a retained binder while keeping the chosen target
image of that binder. The target-domain conversion is derived from the frame's
term agreement; no extra equality between the two domains is assumed. -/
theorem EqSpecializationFrame.under_binder
    (hΔ : OnCtx Δ (env.IsType univs))
    (H : EqSpecializationFrame Γ Γ' Δ σ σ' ρ τ)
    (hA : env.HasType univs Γ A (.sort u))
    (hy : env.HasType univs Δ y (A.subst σ)) :
    EqSpecializationFrame (A :: Γ) (A.subst ρ :: Γ') Δ
      (σ.cons y) (σ'.cons y) ρ.lift τ.lift := by
  have HA := H.term hΔ hA
  have hy' : env.HasType univs Δ y ((A.subst ρ).subst σ') := HA.defeq hy
  refine ⟨.cons H.target (hA.subst henv.orderedStrong H.actual H.target.wf) hy',
    H.actual.lift henv.ordered hA, ErasedSubstAgreement.lift H.target.wf H.actual hA H.erase, ?_⟩
  have EC : ρ.lift.comp (σ'.cons y) = (ρ.comp σ').cons y := by
    funext i
    cases i with
    | zero => rfl
    | succ i => simp only [VExpr.Subst.comp, VExpr.Subst.lift, VExpr.Subst.cons, VExpr.lift_subst_cons]
  rw [EC]
  exact .cons H.agree hA hy

/-- An agreeing application frame preserves the original Eq completion and
supplies the new actual source typing and exact raw argument vector. Guard
readout can subsequently be performed in this new scope. -/
theorem EqPrefixSpecializationAt.frame
    (hΔ : OnCtx Δ (env.IsType univs))
    (H : EqPrefixSpecializationAt Γ Δ v w v' w' original pre σ pending)
    (W : EqSpecializationFrame Γ Γ' Δ σ σ' ρ τ)
    (hf : env.HasType univs Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre) F) :
    EqPrefixSpecializationAt Γ' Δ v w v' w' original (pre.map (·.subst ρ)) σ' pending ∧
      env.HasType univs Γ' (VExpr.mkApps (.const ``Eq.rec [v',w']) (pre.map (·.subst ρ))) (F.subst ρ) ∧
      (pre.map (·.subst ρ)).map (proofErase Γ') = (pre.map (proofErase Γ)).map (·.subst τ) := by
  have HP : List.Forall₂ (env.IsDefEqU univs Δ)
      (pre.map (·.subst σ)) ((pre.map (·.subst ρ)).map (·.subst σ')) := by
    apply List.forall₂_of_getElem (by simp only [List.length_map])
    intro i hi hi'
    have hi₀ : i < pre.length := by simpa only [List.length_map] using hi
    obtain ⟨Te, he⟩ := (mkApps_arguments_wf henv W.actual.wf ⟨_, hf⟩).2 pre[i] (List.getElem_mem hi₀)
    simpa only [List.getElem_map] using (W.term hΔ he).toU
  have HR := H.2.2.flip.imp (fun _ _ R => IsDefEqU.symm R)
  have Hrefl := HR.trans (fun _ _ _ H K => H.trans henv hΔ K) H.2.2
  have Hpending : List.Forall₂ (env.IsDefEqU univs Δ) pending pending := by
    simpa only [List.drop_left] using Lean4Lean.List.forall₂_drop Hrefl (pre.map (·.subst σ)).length
  refine ⟨⟨W.target, H.2.1, H.2.2.trans (fun _ _ _ H K => H.trans henv hΔ K) (HP.append' Hpending)⟩, ?_, ?_⟩
  · simpa only [VExpr.subst_mkApps, VExpr.subst] using hf.subst henv.orderedStrong W.actual W.target.wf
  · simp only [List.map_map]
    apply List.map_congr_left
    intro e he
    obtain ⟨Te, ht⟩ := (mkApps_arguments_wf henv W.actual.wf ⟨_, hf⟩).2 e he
    exact proofErase_subst_with W.target.wf W.actual ht W.erase

/-- Shared whole-spine supply produces both the fresh-body specialization
and its matching computed consumption frame. The chosen target image is the
next actual argument's specialization, derived by taking the prefix. This
supplies frame agreement without an extra image-compatibility hypothesis. -/
theorem EqPrefixSpecializationAt.eta_supply_frame
    (hsource : ErasedScopedPrimitiveDescent Source)
    (hΔ : OnCtx Δ (env.IsType univs))
    (H : EqPrefixSpecializationAt Γ Δ v w v' w' original (pre ++ x :: rest) σ pending)
    (ht : env.HasType univs Δ (VExpr.mkApps (.const ``Eq.rec [v,w]) original) T)
    (hwhole : env.HasType univs Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) (pre ++ x :: rest)) F)
    (hA : env.HasType univs Γ A (.sort u))
    (hf : env.HasType univs Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre) (.forallE A B))
    (RX : ScopedCompute Source (proofEraseCtx Γ) (proofErase Γ x) rawX) :
    EqPrefixSpecializationAt (A :: Γ) Δ v w v' w' original
        (pre.map VExpr.lift ++ [VExpr.bvar 0]) (σ.cons (x.subst σ))
        (rest.map (·.subst σ) ++ pending) ∧
      ∃ x', env.IsDefEq univs Γ x x' A ∧ proofErase Γ x' = rawX ∧
        EqSpecializationFrame (A :: Γ) Γ Δ (σ.cons (x.subst σ)) σ (VExpr.Subst.one x')
          (ProofShape.Subst.one rawX) := by
  have HP : EqPrefixSpecializationAt Γ Δ v w v' w' original pre σ
      ((x.subst σ) :: (rest.map (·.subst σ) ++ pending)) := by
    simpa only [List.take_left, List.drop_left, List.map_cons, List.cons_append] using H.take pre.length
  refine ⟨HP.eta hΔ ht hA hf, ?_⟩
  have hsplit : env.HasType univs Γ
      (VExpr.mkApps (.app (VExpr.mkApps (.const ``Eq.rec [v',w']) pre) x) rest) F := by
    simpa only [VExpr.mkApps_append, VExpr.mkApps_cons] using hwhole
  obtain ⟨Tx, hfx⟩ := VExpr.WF.of_mkApps henv H.1.wf ⟨_, hsplit⟩
  have hfx : env.HasType univs Γ
      (.app (VExpr.mkApps (.const ``Eq.rec [v',w']) pre) x) Tx := hfx
  obtain ⟨_, _, hf₀, hx₀⟩ := hfx.app_inv henv H.1.wf
  exact EqSpecializationFrame.computed_inst hsource hΔ H.1 hA
    (argument_at_displayed_domain H.1.wf hf₀ hf hx₀) RX

/-- Read the later short-prefix cut after an agreeing endpoint frame, including
a composite or binder-lifted frame. The actual target realization, new whole
spine typing, nonproof status and exact raw component vector are all derived
from the frame. Arbitrary continuation interpretations still need their
agreement witness; this theorem does not infer one from raw typing alone. -/
theorem CountedLaterEtaBodyCut.eq_or_eta_after_frame
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hRec : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hΔ : OnCtx Δ (env.IsType univs))
    (HP : EqPrefixSpecializationAt Γ Δ v w v' w' [α,a,M,minor,b] pre σ pending)
    (W : EqSpecializationFrame Γ Γ' Δ σ σ' ρ τ)
    (ht : env.HasType univs Δ (eqRecBeforeMajor v w α a M minor b) T)
    (hf : env.HasType univs Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre) F)
    (hn : ¬ IsProof Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre))
    (hlen : arity ≤ 4)
    (HO : TypedEtaOrigin (proofEraseCtx Γ') rawA
      (ProofShape.mkApps (.const ``Eq.rec [v',w'])
        (((pre.map (proofErase Γ)).map (·.subst τ)).take arity)) u)
    (H : CountedLaterEtaBodyCut D n (proofEraseCtx Γ') rawA
      (ProofShape.mkApps (.const ``Eq.rec [v',w'])
        (((pre.map (proofErase Γ)).map (·.subst τ)).take arity)) u args out ct cost)
    (HE : CarrierExposure out) :
    env.IsDefEq univs Δ a b α ∨
      CountedLaterEtaBodyCut D n (proofEraseCtx Γ') rawA
        (ProofShape.mkApps (.const ``Eq.rec [v',w'])
          (((pre.map (proofErase Γ)).map (·.subst τ)).take arity))
        u args out ct cost (EqEtaRemainingRoot D) := by
  obtain ⟨HS, hf', EP⟩ := HP.frame hΔ W hf
  have hn' : ¬ IsProof Γ' (VExpr.mkApps (.const ``Eq.rec [v',w']) (pre.map (·.subst ρ))) := by
    intro hp
    apply hn ((isProof_subst W.target.wf W.actual hf).1 ?_)
    simpa only [VExpr.subst_mkApps, VExpr.subst] using hp
  rw [← EP] at HO H ⊢
  exact H.eq_or_eta_of_completion heq hs hreg hoff hRec W.target.wf hΔ HS ht hf' hn' hlen HO HE

end Lean4Lean.VEnv.Strengthening
