import Lean4Lean.Theory.Typing.Strengthening.ProofErasureRecoveredEqSpecialization

/-! # Preserve a typed Eq completion through source-prefix computation

Reify component computations before specializing. Their semantic equalities
survive actual substitution even when the raw guarded computations do not.
The singleton root is likewise lowered before its semantic family readout.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private nonproof_spine_head
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureRecoveredEqComputedPrefix
open private erased_carrier_recovered_singleton_rule_descent
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitiveRuleDescent
open private ProofShape.liftN_const_inv
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureComparison
open private erase_const_inv isProof_congr
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
variable [Params]

/-- Replaying a pointwise argument history retains pointwise semantic
equalities, including proof arguments at dependent domains. The reconstructed
whole spine remains at the original assigned type. -/
theorem proofErase_scoped_spine_arguments_descend
    (hsource : ErasedScopedPrimitiveDescent Source)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.LiftN count offset Γ Γ')
    (hf : env.IsDefEqU univs Γ f g)
    (ht : env.HasType univs Γ (VExpr.mkApps f args) T)
    (HA : List.Forall₂ (ScopedCompute Source (proofEraseCtx Γ'))
      ((args.map (proofErase Γ)).map (·.liftN count offset)) raw) :
    ∃ args', List.Forall₂ (env.IsDefEqU univs Γ) args args' ∧
      ((args'.map (proofErase Γ)).map (·.liftN count offset)) = raw ∧
      env.IsDefEq univs Γ (VExpr.mkApps f args) (VExpr.mkApps g args') T := by
  induction args generalizing f g raw with
  | nil => cases HA; exact ⟨[], .nil, rfl, hf.of_l henv hΓ ht⟩
  | cons x xs ih =>
    cases HA with
    | cons RX RXS =>
      obtain ⟨Tapp, happ⟩ := VExpr.WF.of_mkApps henv.orderedStrong hΓ
        (show VExpr.WF env univs Γ (VExpr.mkApps (.app f x) xs) from ⟨_, ht⟩)
      have happ : env.HasType univs Γ (.app f x) Tapp := happ
      obtain ⟨A, B, hft, hx⟩ := happ.app_inv henv hΓ
      obtain ⟨x', HX, EX⟩ := proofErase_scoped_compute_descend hsource hΓ hΓ' W hx rfl RX
      have HF := IsDefEq.appDF (hf.of_l henv hΓ hft) HX
      obtain ⟨xs', HS, ES, HE⟩ := ih HF.toU ht RXS
      exact ⟨x' :: xs', .cons HX.toU HS, by simp only [List.map_cons, EX, ES], HE⟩

/-- A singleton on any computed initial segment of a source Eq prefix forces
the equation of its original typed completion in another context. Ambient
binder descent precedes source specialization; head universes and every
supplied argument may compute. No raw guard or computation is substituted. -/
theorem proofErase_recovered_singleton_eq_computed_prefix_specialize
    (heq : env.HasCanonicalEq)
    (hsource : ErasedScopedPrimitiveDescent Source)
    (hstep : ErasedScopedPrimitiveCertificateDescent Step Step)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.LiftN count offset Γ Γ')
    (hf : env.HasType univs Γ (VExpr.mkApps (.const ``Eq.rec [v,w]) pre) F)
    (hn : ¬ IsProof Γ (VExpr.mkApps (.const ``Eq.rec [v,w]) pre))
    (hΔ : OnCtx Δ (env.IsType univs))
    (ht : env.HasType univs Δ (eqRecBeforeMajor v w α a M m b) T)
    (WS : Ctx.SubstEq env univs Δ σ σ Γ)
    (Eargs : pre.map (·.subst σ) ++ pending = [α,a,M,m,b])
    (HA : List.Forall₂ (ScopedCompute Source (proofEraseCtx Γ'))
      ((pre.map (proofErase Γ)).map (·.liftN count offset)) raw)
    (RL : ScopedCompute Source (proofEraseCtx Γ')
      (.const ``Eq.rec [v,w]) (.const ``Eq.rec [v',w']))
    (H : CarrierRecoveredSingletonPrimitive Step (proofEraseCtx Γ')
      (ProofShape.mkApps (.const ``Eq.rec [v',w']) (raw.take arity)) out) :
    env.IsDefEq univs Δ a b α := by
  obtain ⟨Tc, hc⟩ := VExpr.WF.of_mkApps henv.orderedStrong hΓ ⟨_, hf⟩
  have EC : proofErase Γ (.const ``Eq.rec [v,w]) = .const ``Eq.rec [v,w] :=
    if_neg (nonproof_spine_head hΓ hf hn)
  obtain ⟨c', HC, EC'⟩ := proofErase_scoped_compute_descend hsource hΓ hΓ' W hc rfl
    (by simpa only [EC, ProofShape.liftN] using RL)
  obtain rfl := erase_const_inv (ProofShape.liftN_const_inv EC')
  obtain ⟨pre', HP, EP, HE⟩ := proofErase_scoped_spine_arguments_descend
    hsource hΓ hΓ' W HC.toU hf HA
  have hnew := HE.hasType.2
  have hnnew : ¬ IsProof Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) pre') :=
    fun hp => hn ((isProof_congr hΓ HE).2 hp)
  have hsplit : env.HasType univs Γ
      (VExpr.mkApps (VExpr.mkApps (.const ``Eq.rec [v',w']) (pre'.take arity)) (pre'.drop arity)) F := by
    rw [← VExpr.mkApps_append, List.take_append_drop]; exact hnew
  obtain ⟨Tp, hp⟩ := VExpr.WF.of_mkApps henv.orderedStrong hΓ ⟨_, hsplit⟩
  have hnp : ¬ IsProof Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) (pre'.take arity)) :=
    nonproof_spine_head hΓ hsplit (by simpa only [← VExpr.mkApps_append, List.take_append_drop] using hnnew)
  have H' : CarrierRecoveredSingletonPrimitive Step (proofEraseCtx Γ')
      ((proofErase Γ (VExpr.mkApps (.const ``Eq.rec [v',w']) (pre'.take arity))).liftN count offset) out := by
    rw [proofErase_const_spine hΓ hp hnp, ProofShape.liftN_mkApps]
    simpa only [← EP, List.map_take, ProofShape.liftN] using H
  obtain ⟨_, _, HG, _⟩ := erased_carrier_recovered_singleton_rule_descent heq hstep
    hΓ hΓ' W hp H'
  rw [proofErase_const_spine hΓ hp hnp] at HG
  have HCΔ := HC.subst henv WS hΔ
  simp only [VExpr.subst] at HCΔ
  have HT := IsDefEqU.mkApps_congr_left henv hΔ HCΔ.toU (show
    VExpr.WF env univs Δ (VExpr.mkApps (.const ``Eq.rec [v,w]) [α,a,M,m,b]) from ⟨_, ht⟩)
  have ht' := (HT.of_l henv hΔ ht).hasType.2
  have HPΔ : List.Forall₂ (env.IsDefEqU univs Δ) (pre.map (·.subst σ)) (pre'.map (·.subst σ)) := by
    have map_subst {as bs} (H : List.Forall₂ (env.IsDefEqU univs Γ) as bs) :
        List.Forall₂ (env.IsDefEqU univs Δ) (as.map (·.subst σ)) (bs.map (·.subst σ)) := by
      induction H with
      | nil => exact .nil
      | cons H _ ih =>
        obtain ⟨_, H⟩ := H
        exact .cons (H.subst henv WS hΔ).toU ih
    exact map_subst HP
  have HPend : List.Forall₂ (env.IsDefEqU univs Δ) pending pending := by
    apply List.Forall₂.rfl
    intro e he
    apply (mkApps_arguments_wf henv hΔ (show
      VExpr.WF env univs Δ (VExpr.mkApps (.const ``Eq.rec [v,w]) [α,a,M,m,b]) from ⟨_, ht⟩)).2 e
    rw [← Eargs]
    exact List.mem_append_right _ he
  apply proofErase_recovered_singleton_eq_prefix_specialize_congr heq hstep.descent
    hΓ ⟨_, hp⟩ hΔ ht' WS (pending := (pre'.drop arity).map (·.subst σ) ++ pending) _ HG.2
  rw [← List.append_assoc, ← List.map_append, List.take_append_drop, ← Eargs]
  exact HPΔ.append' HPend

/-- A singleton on any prefix of a computed fresh eta body reads the original
lower equation. Computation may change all old arguments and the head levels;
the fresh argument is included in the same component history. This treats
the first singleton root, not arbitrary subsequent nested eta computation. -/
theorem proofErase_recovered_singleton_eq_computed_fresh_eta_descend
    (heq : env.HasCanonicalEq)
    (hsource : ErasedScopedPrimitiveDescent Source)
    (hstep : ErasedScopedPrimitiveCertificateDescent Step Step)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.LiftN count offset Γ Γ')
    (hA : env.HasType univs Γ A (.sort u))
    (hf : env.HasType univs Γ (VExpr.mkApps (.const ``Eq.rec [v,w]) pre) (.forallE A B))
    (hn : ¬ IsProof Γ (VExpr.mkApps (.const ``Eq.rec [v,w]) pre))
    (hx : env.HasType univs Γ x A)
    (ht : env.HasType univs Γ (eqRecBeforeMajor v w α a M m b) T)
    (Eargs : pre ++ x :: pending = [α,a,M,m,b])
    (HA : List.Forall₂ (ScopedCompute Source (proofEraseCtx (A.liftN count offset :: Γ')))
      ((((pre.map (proofErase Γ)).map (·.liftN count offset)).map (·.liftN 1)) ++ [etaArgument u]) raw)
    (RL : ScopedCompute Source (proofEraseCtx (A.liftN count offset :: Γ'))
      (.const ``Eq.rec [v,w]) (.const ``Eq.rec [v',w']))
    (H : CarrierRecoveredSingletonPrimitive Step (proofEraseCtx (A.liftN count offset :: Γ'))
      (ProofShape.mkApps (.const ``Eq.rec [v',w']) (raw.take arity)) out) :
    env.IsDefEq univs Γ a b α := by
  let fresh := pre.map VExpr.lift ++ [.bvar 0]
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  have hΓA' : OnCtx (A.liftN count offset :: Γ') (env.IsType univs) :=
    ⟨hΓ', u, hA.weakN henv W⟩
  have EE : VExpr.mkApps (.const ``Eq.rec [v,w]) fresh =
      .app (VExpr.mkApps (.const ``Eq.rec [v,w]) pre).lift (.bvar 0) := by
    simp only [fresh, VExpr.mkApps_append, VExpr.mkApps_cons, VExpr.mkApps_nil,
      VExpr.lift, VExpr.liftN_mkApps, VExpr.liftN]
  have hfw : env.HasType univs (A :: Γ)
      (VExpr.mkApps (.const ``Eq.rec [v,w]) pre).lift
      (.forallE A.lift (B.liftN 1 1)) := hf.weak henv
  have hbody : env.HasType univs (A :: Γ) (VExpr.mkApps (.const ``Eq.rec [v,w]) fresh) B := by
    rw [EE]
    simpa only [VExpr.inst_liftN_bvar] using hfw.app (HasType.bvar .zero)
  have EB := proofErase_eta_body hΓ hA hf hn
  rw [← EE] at EB
  have hnb : ¬ IsProof (A :: Γ) (VExpr.mkApps (.const ``Eq.rec [v,w]) fresh) := by
    intro hp
    rw [proofErase_eq_proof.2 hp] at EB
    cases EB
  have Epre : (pre.map VExpr.lift).map (proofErase (A :: Γ)) =
      (pre.map (proofErase Γ)).map (·.liftN 1) := by
    simp only [List.map_map]
    apply List.map_congr_left
    intro e he
    obtain ⟨Te, ht⟩ := (mkApps_arguments_wf henv hΓ ⟨_, hf⟩).2 e he
    exact proofErase_liftN hΓ hΓA Ctx.LiftN.one ht
  have Evector : ((fresh.map (proofErase (A :: Γ))).map (·.liftN count (offset+1))) =
      ((((pre.map (proofErase Γ)).map (·.liftN count offset)).map (·.liftN 1)) ++ [etaArgument u]) := by
    simp only [fresh, List.map_append, Epre, List.map_cons, List.map_nil,
      proofErase_fresh_argument hΓ hA, etaArgument_liftN, List.map_map, Function.comp_def]
    congr 1
    apply List.map_congr_left
    intro e _
    exact (ProofShape.liftN_comm _ count 1 offset 0 (Nat.zero_le _)).symm
  have WS : Ctx.SubstEq env univs Γ (VExpr.Subst.id.cons x) (VExpr.Subst.id.cons x) (A :: Γ) :=
    .cons (Ctx.SubstEq.id henv.ordered hΓ) hA (by
      change env.HasType univs Γ x (A.subst VExpr.Subst.id)
      simpa only [VExpr.subst_id] using hx)
  apply proofErase_recovered_singleton_eq_computed_prefix_specialize heq hsource hstep
    hΓA hΓA' W.succ hbody hnb hΓ ht WS (pending := pending) _ (Evector.symm ▸ HA) RL H
  have Ezero : VExpr.Subst.id.cons x 0 = x := rfl
  simpa only [fresh, List.map_append, List.map_map, Function.comp_def,
    VExpr.lift_subst_cons, VExpr.subst_id, List.map_id_fun', id,
    List.map_cons, List.map_nil, VExpr.subst, Ezero, List.append_assoc,
    List.cons_append, List.nil_append] using Eargs

end Lean4Lean.VEnv.Strengthening
