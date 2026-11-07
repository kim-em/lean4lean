import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertZeroEvidence

/-! # Typed identity comparison returns the actual argument

The proof-marker eta shortcut is impossible for a sort-typed target body.
Ordinary and sorted lambda rules instead expose the identity variable in their
recorded context. At stage zero those paths give an ordinary-core body return,
which can be instantiated without transporting a guarded comparison.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private erase_lam_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
variable [Params] {D : Definitions}

/-- A typed identity terminal exposes its bound variable in one of its two
recorded contexts. Sort typing excludes the raw proof-marker eta counterexample;
no comparison or computation is transported across lambda annotations. -/
theorem InferredLambdaTerminal.identity_body_return
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (HD : ControlTyping (C :: Δ) d (.sort u))
    (H : InferredLambdaTerminal (PiInertStage D n) Δ A (.bvar 0) C d) :
    ScopedCompute (PiInertStage D n) (A :: Δ) d (.bvar 0) ∨
      ScopedCompute (PiInertStage D n) (C :: Δ) d (.bvar 0) := by
  rcases H.body_cases with ⟨_, E⟩ | HL | HR | HE
  · exact .inl (E ▸ .refl)
  · exact .inl HL.pi_inert_bvar_exposure
  · exact .inr HR.pi_inert_bvar_exposure
  · rcases HE with HE | HE
    · obtain ⟨_, _, E, _⟩ := HE.shape
      cases E
    · obtain ⟨_, arg, E, Harg⟩ := HE.shape
      have EB := (ProofShape.lam.inj E).2
      have RB : ProofShape.BetaRed d arg := by
        rw [EB]
        simpa only [ProofShape.liftN, liftVar, Nat.zero_lt_succ, ↓reduceIte,
          ProofShape.inst_eq_subst, ProofShape.Subst.liftN, ProofShape.subst,
          ProofShape.Subst.one, ProofShape.Subst.cons] using
          (ProofShape.BetaRed.beta (A := A.liftN 1) (b := .bvar 0) (a := arg))
      rcases Harg with rfl | rfl
      · exact .inr (.beta RB)
      · have hdsc : ErasedScopedPrimitiveDescent (PiInertStage D n) :=
          fun hΓ hΓ' W ht HR => erased_static_structure_eta_expansion_stage_descent heq hs n
            hΓ hΓ' W ht HR.1
        exact ((HD.compute hdsc (.beta RB)).ne_proof rfl).elim

/-- At stage zero the recorded identity-body path gives an ordinary-core
return. Both scope witnesses are explicit; only the path's actual scope is
used for replay, and the resulting core path is context independent. -/
theorem InferredLambdaTerminal.identity_body_core_return
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (HA : TypedSource (A :: Δ) d) (HD : ControlTyping (C :: Δ) d (.sort u))
    (H : InferredLambdaTerminal (PiInertStage D 0) Δ A (.bvar 0) C d) :
    Compute (ErasedLevelCore D) d (.bvar 0) := by
  have HC : TypedSource (C :: Δ) d := by
    obtain ⟨Γ, e, hΓ, EΓ, ht, Ee⟩ := HD
    exact ⟨Γ, e, _, hΓ, EΓ, ht, Ee⟩
  have J : ComputeJoin (ErasedLevelCore D) d (.bvar 0) := by
    rcases H.identity_body_return heq hs HD with R | R
    · exact R.pi_inert_zero_core_join heq hs hc HA
    · exact R.pi_inert_zero_core_join heq hs hc HC
  obtain ⟨out, RD, RV⟩ := J
  have E := (RV.in_pi_inert_stage (n := 0) (Δ := [])).pi_inert_bvar_fixed
  exact E ▸ RD

private theorem lambda_sort_body
    (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ (.lam A b) (.forallE C (.sort u))) :
    ∃ w, env.HasType univs Γ A (.sort w) ∧ env.IsDefEqU univs Γ A C ∧
      env.HasType univs (A :: Γ) b (.sort u) := by
  obtain ⟨⟨w, hA⟩, B, hb⟩ := ht.lam_inv henv hΓ
  have HPi := (HasType.lam hA hb).uniqU henv hΓ ht
  obtain ⟨⟨_, HAC⟩, _, HB⟩ := HPi.forallE_inv henv hΓ
  exact ⟨w, hA, HAC.toU, HB.defeq hb⟩

/-- Inferred comparison with a type-valued identity exposes a target lambda
whose body returns to the bound variable in ordinary core. Both actual lambda
domains and target body typings are recovered; the target's original assigned
type is arbitrary. Annotation conversion is used only for ordinary typing. -/
theorem pi_inert_zero_identity_lambda_cut
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort w))
    (hzero : env.HasType univs (A :: Γ) (.bvar 0) (.sort u))
    (hg : env.HasType univs Γ g G)
    (H : ComputedJointCompare (PiInertStage D 0) (proofEraseCtx Γ) false
      (proofErase Γ (.lam A (.bvar 0))) (proofErase Γ g)) :
    env.HasType univs Γ g (.forallE A (.sort u)) ∧
      ∃ C d z, env.HasType univs Γ C (.sort z) ∧ env.IsDefEqU univs Γ C A ∧
        env.HasType univs (C :: Γ) d (.sort u) ∧
        ScopedCompute (PiInertStage D 0) (proofEraseCtx Γ)
          (proofErase Γ g) (proofErase Γ (.lam C d)) ∧
        Compute (ErasedLevelCore D) (proofErase (C :: Γ) d) (.bvar 0) := by
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, w, hA⟩
  have hid := HasType.lam hA hzero
  have hni := not_isProof_function_to_sort hΓ hid
  have EID : proofErase Γ (.lam A (.bvar 0)) = .lam (proofErase Γ A) (.bvar 0) := by
    rw [show proofErase Γ (.lam A (.bvar 0)) =
      .lam (proofErase Γ A) (proofErase (A :: Γ) (.bvar 0)) from if_neg hni,
      show proofErase (A :: Γ) (.bvar 0) = .bvar 0 from if_neg (not_isProof_of_sort hΓA hzero)]
  have HR := H
  rw [EID] at HR
  obtain ⟨rawA, rawb, rawC, rawd, RL, RR, HT⟩ := HR.pi_inert_lambda_cut
  obtain ⟨_, E, _⟩ := RL.pi_inert_identity_lam
  cases E
  have hng : ¬ IsProof Γ g := by
    intro hp
    have R := RR
    rw [proofErase_eq_proof.2 hp] at R
    cases R.pi_inert_proof_fixed
  have hdsc : ErasedScopedPrimitiveDescent (PiInertStage D 0) :=
    fun hΓ hΓ' W ht HR => erased_static_structure_eta_expansion_stage_descent heq hs 0
      hΓ hΓ' W ht HR.1
  have HIG := (proofErase_computed_joint_compare_reflect hdsc hΓ hid hg H).2 rfl hni hng
  have hgPi := (HIG.of_l henv hΓ hid).hasType.2
  obtain ⟨f', Hf, Ef⟩ := proofErase_scoped_compute_realize hdsc hΓ hid rfl EID RL
  obtain ⟨A', b', rfl, _, EA', _⟩ := erase_lam_inv Ef
  obtain ⟨g', Hg, Eg⟩ := proofErase_scoped_compute_realize hdsc hΓ hgPi rfl rfl RR
  obtain ⟨C, d, rfl, _, EC, Ed⟩ := erase_lam_inv Eg
  obtain ⟨w', hA', HA', _⟩ := lambda_sort_body hΓ Hf.hasType.2
  obtain ⟨z, hC, HC, hd⟩ := lambda_sort_body hΓ Hg.hasType.2
  have HAC := (HA'.trans henv hΓ HC.symm).of_l henv hΓ hA'
  have hΓA' : OnCtx (A' :: Γ) (env.IsType univs) := ⟨hΓ, w', hA'⟩
  have hΓC : OnCtx (C :: Γ) (env.IsType univs) := ⟨hΓ, z, hC⟩
  have W : IsDefEqCtx env univs Γ (C :: Γ) (A' :: Γ) := .succ .zero HAC.symm
  have hdA := hd.defeqDFC henv W
  have Hleft : TypedSource (rawA :: proofEraseCtx Γ) rawd :=
    ⟨A' :: Γ, d, .sort u, hΓA', by simp only [proofEraseCtx, EA'], hdA,
      (proofErase_defeqCtx hΓC W hd).symm.trans Ed⟩
  have Hright : ControlTyping (rawC :: proofEraseCtx Γ) rawd (.sort u) :=
    ⟨C :: Γ, d, hΓC, by simp only [proofEraseCtx, EC], hd, Ed⟩
  have RB := HT.identity_body_core_return heq hs hc Hleft Hright
  exact ⟨hgPi, C, d, z, hC, HC, hd, by simpa only [Eg] using RR, Ed ▸ RB⟩

/-- A function inferred-equal to a type-valued identity has an ordinary-core
application join with every actual argument. The target lambda's annotation
may differ and is discarded only by beta after the argument is retyped there. -/
theorem pi_inert_zero_identity_application_core_join
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort w))
    (hzero : env.HasType univs (A :: Γ) (.bvar 0) (.sort u))
    (hg : env.HasType univs Γ g G) (hy : env.HasType univs Γ y A)
    (H : ComputedJointCompare (PiInertStage D 0) (proofEraseCtx Γ) false
      (proofErase Γ (.lam A (.bvar 0))) (proofErase Γ g)) :
    env.HasType univs Γ g (.forallE A (.sort u)) ∧
      ComputeJoin (ErasedLevelCore D) (proofErase Γ (.app g y)) (proofErase Γ y) := by
  obtain ⟨hgPi, C, d, z, hC, HC, hd, RG, RD⟩ :=
    pi_inert_zero_identity_lambda_cut heq hs hc hΓ hA hzero hg H
  have hyC := (HC.of_r henv hΓ hA).symm.defeq hy
  have htarget := HasType.lam hC hd
  have hleft := hgPi.app hy
  have hright := htarget.app hyC
  have JG := RG.pi_inert_zero_core_join heq hs hc ⟨Γ, g, _, hΓ, rfl, hgPi, rfl⟩
  have EL : proofErase Γ (.app g y) = .app (proofErase Γ g) (proofErase Γ y) :=
    if_neg (not_isProof_of_sort hΓ hleft)
  have ER : proofErase Γ (.app (.lam C d) y) =
      .app (proofErase Γ (.lam C d)) (proofErase Γ y) :=
    if_neg (not_isProof_of_sort hΓ hright)
  have EF : proofErase Γ (.lam C d) =
      .lam (proofErase Γ C) (proofErase (C :: Γ) d) :=
    if_neg (not_isProof_function_to_sort hΓ htarget)
  have JA : ComputeJoin (ErasedLevelCore D) (proofErase Γ (.app g y))
      (proofErase Γ (.app (.lam C d) y)) := by
    rw [EL, ER]
    exact JG.app .refl
  have RB : Compute (ErasedLevelCore D) (proofErase Γ (.app (.lam C d) y))
      (proofErase Γ y) := by
    rw [ER, EF]
    apply Compute.trans (.app (.lam .refl RD) .refl)
    apply ProofShape.Compute.beta
    simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN, ProofShape.subst,
      ProofShape.Subst.one, ProofShape.Subst.cons] using
      (ProofShape.BetaRed.beta (A := proofErase Γ C) (b := .bvar 0) (a := proofErase Γ y))
  exact ⟨hgPi, JA.trans_typed hc hΓ hright (.of_compute RB)⟩

/-- The identity application join supplies every future typed substitution
and all core residuals. Thus this function-comparison branch consumes a complete
argument-carrier history by carrier_prefix, without a guarded substitution law
or a new comparison child for the target body. -/
theorem pi_inert_zero_identity_application_evidence
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort w))
    (hzero : env.HasType univs (A :: Γ) (.bvar 0) (.sort u))
    (hg : env.HasType univs Γ g G) (hy : env.HasType univs Γ y A)
    (H : ComputedJointCompare (PiInertStage D 0) (proofEraseCtx Γ) false
      (proofErase Γ (.lam A (.bvar 0))) (proofErase Γ g)) :
    PiInertEvidence D stage .compute (proofEraseCtx Γ)
      (proofErase Γ (.app g y)) (proofErase Γ y) := by
  obtain ⟨hgPi, J⟩ := pi_inert_zero_identity_application_core_join heq hs hc hΓ hA hzero hg hy H
  have hyu : env.HasType univs Γ y (.sort u) := by
    simpa only [VExpr.inst, VExpr.instVar_zero] using hzero.instN henv Ctx.InstN.zero hy
  exact .of_core_join hc ⟨Γ, _, _, hΓ, rfl, hgPi.app hy, rfl⟩
    ⟨Γ, y, _, hΓ, rfl, hyu, rfl⟩ J

/-- In the identity-frame application case, the framed source argument
supplies the missing sort typing of the identity body. The completed argument
child then transfers to the target application at the same stage. No body
history, argument equality, or generic application-closure premise is added. -/
theorem RigidSortFrames.compared_identity_application_history
    (HX : RigidSortFrames family (proofEraseCtx Γ) (proofErase Γ x))
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort w))
    (hx : env.HasType univs Γ x A) (hg : env.HasType univs Γ g G)
    (hy : env.HasType univs Γ y A)
    (H : ComputedJointCompare (PiInertStage D 0) (proofEraseCtx Γ) false
      (proofErase Γ (.lam A (.bvar 0))) (proofErase Γ g))
    (HY : PiInertCarrierHistory D stage (proofEraseCtx Γ) (proofErase Γ y) left right) :
    PiInertCarrierHistory D stage (proofEraseCtx Γ) (proofErase Γ (.app g y)) left right := by
  obtain ⟨u, hxu⟩ := HX.original_sort hΓ hx
  have HA := (hx.uniqU henv hΓ hxu).of_l henv hΓ hA
  have hzero : env.HasType univs (A :: Γ) (.bvar 0) (.sort u) :=
    (HA.weak henv).defeq (.bvar .zero)
  exact PiInertCarrierHistory.carrier_prefix
    (pi_inert_zero_identity_application_evidence heq hs hc hΓ hA hzero hg hy H) HY

end Lean4Lean.VEnv.Strengthening
