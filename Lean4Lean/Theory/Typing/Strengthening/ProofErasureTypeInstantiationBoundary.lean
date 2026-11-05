import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypeBetaResidual
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCallerEtaAnnotation
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedRawBetaJoin

/-! # Type computations require a join after arbitrary instantiation

A generic function has a fresh converted domain. Eta exposes that domain inside
a neutral type caller declared below the fresh variable. Supplying an old
constant lambda makes the initial type live below that variable, but leaves it
in the computed annotation. Exact computation transport is impossible by descent.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private ProofShape.liftN_app_inv ProofShape.liftN_lam_inv ProofShape.liftN_forallE_inv
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypedReplay
open private not_proof_at_positive_type from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedUnitBoundary
variable [Params]

/-- A descending computation from a lower typed source cannot put an inserted
variable in the domain annotation of its final literal function argument. -/
theorem compute_no_inserted_call_lambda_domain
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.LiftN n k Γ Γ') (ht : env.HasType univs Γ e T)
    (hj : k ≤ j) (hj' : j < k+n) :
    ¬ ScopedCompute Step (proofEraseCtx Γ') ((proofErase Γ e).liftN n k)
      (.app f (.lam (.app g (.bvar j)) b)) := by
  intro R
  obtain ⟨e', _, EE⟩ := proofErase_scoped_compute_descend hstep hΓ hΓ' W ht rfl R
  obtain ⟨_, arg, _, _, Earg⟩ := ProofShape.liftN_app_inv EE
  obtain ⟨A, _, _, EA, _⟩ := ProofShape.liftN_lam_inv Earg
  obtain ⟨_, a, _, _, Ea⟩ := ProofShape.liftN_app_inv EA
  cases a <;> simp only [ProofShape.liftN] at Ea <;> try cases Ea
  simp only [liftVar] at hj hj'
  split at hj <;> simp_all <;> omega

/-- Even sort-typed body computations do not transport as exact forward
paths under arbitrary typed instantiation. A generic eta guard copies a fresh
converted domain into a type caller whose declaration is older. Both beta-fork
outputs nevertheless have an explicit common reduct by unit eta, so this
refutes exact substitution transport and even a pure-beta residual square
against any descending target computation. The source computation needs only
stage one. TypeInstantiationJoin and strengthening
are not refuted: the displayed common reduct uses structure computation. The
argument explicitly lacks native recovery at the cut domain, so this does not
refute the restricted certified-cut route. The body is literally the generic
application of an ordinarily typed family head. That head cannot natively recover
any Pi with its converted domain, irrespective of the selected codomain,
for any descending primitive language. The argument domain is explicitly a
nonempty literal Pi telescope. Thus ordinary family typing cannot replace the exact native-head premise of generic telescope
reification, even for a single argument. -/
theorem static_structure_generic_family_domain_instantiation_beta_residual_failure
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hz : info.numFields = 0)
    (hS : env.HasType univs [] (.const family []) (.sort (.succ u))) :
    ∃ Γ Q g x B out,
      OnCtx Γ (env.IsType univs) ∧ env.HasType univs Γ x Q ∧
      env.HasType univs Γ g (.forallE Q (.sort (.succ .zero))) ∧
      (∃ A, Q = .forallE A (.sort (.succ .zero))) ∧
      B = .app g.lift (.bvar 0) ∧
      (∀ Step, ErasedScopedPrimitiveDescent Step → ∀ selected,
        ¬ ScopedTypeRecovery Step (proofEraseCtx Γ) (proofErase Γ g)
          (.forallE (proofErase Γ Q) selected)) ∧
      env.HasType univs (Q :: Γ) B (.sort (.succ .zero)) ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionStage D 1) (proofEraseCtx (Q :: Γ))
        (proofErase (Q :: Γ) B) out ∧
      (¬ ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ (B.inst x)) (out.inst (proofErase Γ x))) ∧
      (∀ Step, ErasedScopedPrimitiveDescent Step →
        ¬ ScopedCompute Step (proofEraseCtx Γ)
          (proofErase Γ (B.inst x)) (out.inst (proofErase Γ x))) ∧
      (∀ Step, ErasedScopedPrimitiveDescent Step →
        ¬ ∃ shared, ScopedCompute Step (proofEraseCtx Γ)
            (proofErase Γ (B.inst x)) shared ∧
          ProofShape.BetaRed (out.inst (proofErase Γ x)) shared) ∧
      (¬ ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ x) (proofErase Γ Q)) ∧
      ∃ shared, ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
          (proofErase Γ (B.inst x)) shared ∧
        ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
          (out.inst (proofErase Γ x)) shared := by
  let S := VExpr.const family []
  let K := VExpr.forallE S (.sort (.succ .zero))
  let Γ₀ := [K, S]
  have hK : env.HasType univs [] K (.sort (.imax (.succ u) (.succ (.succ .zero)))) :=
    .forallE hS (.sort (by trivial))
  have hΓ₀ : OnCtx Γ₀ (env.IsType univs) := ⟨⟨trivial, _, hS⟩, _, hK.weak0 henv.ordered⟩
  let L₀ := VExpr.app (.bvar 0) (.bvar 1)
  have hL₀ : env.HasType univs Γ₀ L₀ (.sort (.succ .zero)) :=
    .app (show env.HasType univs Γ₀ (.bvar 0) K from .bvar .zero) (.bvar (.succ .zero))
  let Q₀ := VExpr.forallE L₀ (.sort (.succ .zero))
  let H₀ := VExpr.forallE Q₀ (.sort (.succ .zero))
  have hQ₀ : env.HasType univs Γ₀ Q₀
      (.sort (.imax (.succ .zero) (.succ (.succ .zero)))) := .forallE hL₀ (.sort (by trivial))
  have hH₀ : env.HasType univs Γ₀ H₀
      (.sort (.imax (.imax (.succ .zero) (.succ (.succ .zero))) (.succ (.succ .zero)))) :=
    .forallE hQ₀ (.sort (by trivial))
  let Δ := H₀ :: Γ₀
  have hΔ : OnCtx Δ (env.IsType univs) := ⟨hΓ₀, _, hH₀⟩
  let q₀ := VExpr.lam L₀.lift (.sort .zero)
  have hq₀ : env.HasType univs Δ q₀ Q₀.lift :=
    .lam (hL₀.weakN henv Ctx.LiftN.one) (.sort (by trivial))
  have hf₀ : env.HasType univs Δ (.bvar 0) (.forallE Q₀.lift (.sort (.succ .zero))) := .bvar .zero
  let call₀ := VExpr.app (.bvar 0) q₀
  have hc₀ : env.HasType univs Δ call₀ (.sort (.succ .zero)) := .app hf₀ hq₀
  let Γ := S :: Δ
  have hΓ : OnCtx Γ (env.IsType univs) := ⟨hΔ, _, hS.weak0 henv.ordered⟩
  let A := VExpr.app (.bvar 2) (.bvar 0)
  let L := L₀.liftN 2
  let Q := VExpr.forallE A (.sort (.succ .zero))
  let x := q₀.lift
  have hKΓ : env.HasType univs Γ (.bvar 2) K := .bvar (.succ (.succ .zero))
  have hy : env.HasType univs Γ (.bvar 0) S := .bvar .zero
  have hz₀ : env.HasType univs Γ (.bvar 3) S := .bvar (.succ (.succ (.succ .zero)))
  have hA : env.HasType univs Γ A (.sort (.succ .zero)) := .app hKΓ hy
  have hL : env.HasType univs Γ L (.sort (.succ .zero)) := .app hKΓ hz₀
  have HE : env.IsDefEq univs Γ A L (.sort (.succ .zero)) :=
    IsDefEq.appDF hKΓ (IsDefEq.unitLike hi (params := []) hp.symm hx hz hy hz₀)
  have HQ : env.IsDefEq univs Γ Q (.forallE L (.sort (.succ .zero)))
      (.sort (.imax (.succ .zero) (.succ (.succ .zero)))) :=
    IsDefEq.forallEDF HE (HasType.sort (by trivial))
  have hxQ : env.HasType univs Γ x Q := HQ.symm.defeq (hq₀.weakN henv Ctx.LiftN.one)
  have hQ := HQ.hasType.1
  have hΓQ : OnCtx (Q :: Γ) (env.IsType univs) := ⟨hΓ, _, hQ⟩
  have hf : env.HasType univs Γ (.bvar 1) (.forallE (.forallE L (.sort (.succ .zero)))
      (.sort (.succ .zero))) := .bvar (.succ .zero)
  have hfQ : env.HasType univs Γ (.bvar 1) (.forallE Q (.sort (.succ .zero))) :=
    (IsDefEq.forallEDF HQ.symm (HasType.sort (by trivial))).defeq hf
  have hg : env.HasType univs (Q :: Γ) (.bvar 0) Q.lift := .bvar .zero
  have hgL := (HQ.weakN henv Ctx.LiftN.one).defeq hg
  let B := VExpr.app (.bvar 2) (.bvar 0)
  have hB : env.HasType univs (Q :: Γ) B (.sort (.succ .zero)) :=
    .app (hf.weakN henv Ctx.LiftN.one) hgL
  have ES (Γ' : List VExpr) (hΓ' : OnCtx Γ' (env.IsType univs)) (v : VLevel) (hv : v.WF univs) :
      proofErase Γ' (.sort v) = .sort v := if_neg (not_isProof_of_sort hΓ' (HasType.sort hv))
  have EK : proofErase Γ (.bvar 2) = .bvar 2 := if_neg (not_isProof_function_to_sort hΓ hKΓ)
  have EY : proofErase Γ (.bvar 0) = .bvar 0 :=
    if_neg (not_proof_at_positive_type hΓ (hS.weak0 henv.ordered) hy)
  have EZ : proofErase Γ (.bvar 3) = .bvar 3 :=
    if_neg (not_proof_at_positive_type hΓ (hS.weak0 henv.ordered) hz₀)
  have EA : proofErase Γ A = .app (.bvar 2) (.bvar 0) := by
    rw [show proofErase Γ A = .app _ _ from if_neg (not_isProof_of_sort hΓ hA), EK, EY]
  have EL : proofErase Γ L = .app (.bvar 2) (.bvar 3) := by
    rw [show proofErase Γ L = .app _ _ from if_neg (not_isProof_of_sort hΓ hL)]
    change ProofShape.app (proofErase Γ (.bvar 2)) (proofErase Γ (.bvar 3)) = _
    rw [EK, EZ]
  have EQ : proofErase Γ Q = .forallE (.app (.bvar 2) (.bvar 0)) (.sort (.succ .zero)) := by
    rw [show proofErase Γ Q = .forallE _ _ from if_neg (not_isProof_of_sort hΓ hQ), EA,
      ES (A :: Γ) ⟨hΓ, _, hA⟩ _ (by trivial)]
  have Ex : proofErase Γ x = .lam (.app (.bvar 2) (.bvar 3)) (.sort .zero) := by
    rw [show proofErase Γ x = .lam _ _ from if_neg (not_isProof_function_to_sort hΓ hxQ)]
    change ProofShape.lam (proofErase Γ L) (proofErase (L :: Γ) (.sort .zero)) = _
    rw [EL, ES (L :: Γ) ⟨hΓ, _, hL⟩ _ (by trivial)]
  have EB : proofErase (Q :: Γ) B = .app (.bvar 2) (.bvar 0) := by
    rw [show proofErase (Q :: Γ) B = .app _ _ from if_neg (not_isProof_of_sort hΓQ hB)]
    change ProofShape.app (proofErase (Q :: Γ) (.bvar 2)) (proofErase (Q :: Γ) (.bvar 0)) = _
    rw [show proofErase (Q :: Γ) (.bvar 2) = .bvar 2 from
      if_neg (not_isProof_function_to_sort hΓQ (hf.weakN henv Ctx.LiftN.one)),
      show proofErase (Q :: Γ) (.bvar 0) = .bvar 0 from
      if_neg (not_isProof_function_to_sort hΓQ hg)]
  have RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D 0)
      (proofErase Γ Q :: proofEraseCtx Γ) (.bvar 0)
      ((proofErase Γ Q).liftN 1) := .bvar
  rw [EQ] at RN
  have SA := DomainSort.of_typed hΓQ (hA.weakN henv Ctx.LiftN.one)
  rw [proofErase_liftN hΓ hΓQ Ctx.LiftN.one hA, EA, proofEraseCtx, EQ] at SA
  have RE : ScopedCompute (ErasedStaticStructureEtaExpansionStage D 1) _ _ _ :=
    .base (.inr (.inr (.inr (.inr (.inl (.intro RN SA))))))
  have RE' : ScopedCompute (ErasedStaticStructureEtaExpansionStage D 1) (proofEraseCtx (Q :: Γ))
      (.bvar 0) (.lam (.app (.bvar 3) (.bvar 1)) (.app (.bvar 1) (.bvar 0))) := by
    simpa only [proofEraseCtx, EQ, etaArgument, show ¬ VLevel.succ .zero ≈ .zero from by
      intro E; have H := congrFun E []; simp [VLevel.eval] at H,
      ↓reduceIte, ProofShape.liftN, liftVar, Nat.not_lt_zero, Nat.reduceAdd] using RE
  let out := ProofShape.app (.bvar 2) (.lam (.app (.bvar 3) (.bvar 1)) (.app (.bvar 1) (.bvar 0)))
  have RB : ScopedCompute (ErasedStaticStructureEtaExpansionStage D 1) (proofEraseCtx (Q :: Γ))
      (proofErase (Q :: Γ) B) out := by rw [EB]; exact .app .refl RE'
  have EI : proofErase Γ (B.inst x) = .app (.bvar 1) (proofErase Γ x) := by
    rw [proofErase_instN hΓQ hxQ Ctx.InstN.zero hB, EB]
    simp [ProofShape.inst, ProofShape.liftN_zero]
  have Rβ : ProofShape.BetaRed (out.inst (proofErase Γ x))
      (.app (.bvar 1) (.lam (.app (.bvar 2) (.bvar 0)) (.sort .zero))) := by
    rw [Ex]
    exact .app .refl (.lam .refl .beta)
  have ESc : proofErase Γ S = .const family [] :=
    if_neg (not_isProof_of_sort hΓ (hS.weak0 henv.ordered))
  have RY := proofErase_scoped_lookup_recovery (Step := ErasedStaticStructureEtaExpansionUnion D)
    hΓ (show Lookup Γ 0 S from .zero)
    (not_proof_at_positive_type hΓ (hS.weak0 henv.ordered) hy) ScopedCompute.refl
  have RZ := proofErase_scoped_lookup_recovery (Step := ErasedStaticStructureEtaExpansionUnion D)
    hΓ (show Lookup Γ 3 S from .succ (.succ (.succ .zero)))
    (not_proof_at_positive_type hΓ (hS.weak0 henv.ordered) hz₀) ScopedCompute.refl
  rw [EY, ESc] at RY
  rw [EZ, ESc] at RZ
  have UY : NativeUnitExpansion (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (.bvar 0) (.const info.ctorName []) := .intro hi hx hz (ps := []) hp.symm RY
  have UZ : NativeUnitExpansion (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (.bvar 3) (.const info.ctorName []) := .intro hi hx hz (ps := []) hp.symm RZ
  have CY := ScopedCompute.base (erased_static_structure_eta_expansion_union_structure UY.maskedStructure)
  have CZ := ScopedCompute.base (erased_static_structure_eta_expansion_union_structure UZ.maskedStructure)
  have HnoNormal {Step} (hstep : ErasedScopedPrimitiveDescent Step) :
      ¬ ScopedCompute Step (proofEraseCtx Γ) (proofErase Γ (B.inst x))
        (.app (.bvar 1) (.lam (.app (.bvar 2) (.bvar 0)) (.sort .zero))) := by
    intro R
    have EN := proofErase_liftN hΔ hΓ Ctx.LiftN.one hc₀
    change proofErase Γ (B.inst x) = _ at EN
    rw [EN] at R
    exact compute_no_inserted_call_lambda_domain hstep
      hΔ hΓ Ctx.LiftN.one hc₀ (j := 0) (by decide) (by decide) R
  have Hno {Step} (hstep : ErasedScopedPrimitiveDescent Step) :
      ¬ ScopedCompute Step (proofEraseCtx Γ)
        (proofErase Γ (B.inst x)) (out.inst (proofErase Γ x)) :=
    fun R => HnoNormal hstep (R.trans (.beta Rβ))
  have HnoBeta {Step} (hstep : ErasedScopedPrimitiveDescent Step) :
      ¬ ∃ shared, ScopedCompute Step (proofEraseCtx Γ)
          (proofErase Γ (B.inst x)) shared ∧
        ProofShape.BetaRed (out.inst (proofErase Γ x)) shared := by
    rintro ⟨shared, RL, RR⟩
    obtain ⟨last, RN, RS⟩ := Rβ.raw_confluent RR
    have Hnormal : NormalSyntax (fun _ _ => False)
        (.app (.bvar 1) (.lam (.app (.bvar 2) (.bvar 0)) (.sort .zero))) := by
      simp [NormalSyntax]
    obtain rfl := RN.fixed_of_normal Hnormal
    exact HnoNormal hstep (RL.trans (.beta RS))
  have HnoNative : ¬ ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D)
      (proofEraseCtx Γ) (proofErase Γ x) (proofErase Γ Q) := by
    intro R
    have EW := proofErase_liftN hΔ hΓ Ctx.LiftN.one hq₀
    change proofErase Γ x = _ at EW
    rw [EW, EQ] at R
    obtain ⟨C, _, EC⟩ := proofErase_scoped_typeRecovery_descend
      (erased_static_structure_eta_expansion_union_descent heq hs)
      hΔ hΓ Ctx.LiftN.one hq₀ rfl R
    obtain ⟨F, _, _, EF, _⟩ := ProofShape.liftN_forallE_inv EC
    obtain ⟨_, arg, _, _, Earg⟩ := ProofShape.liftN_app_inv EF
    cases arg <;> simp [ProofShape.liftN, liftVar] at Earg
  have HnoHead {Step} (hstep : ErasedScopedPrimitiveDescent Step) (selected) :
      ¬ ScopedTypeRecovery Step (proofEraseCtx Γ) (proofErase Γ (.bvar 1))
        (.forallE (proofErase Γ Q) selected) := by
    intro R
    have EW := proofErase_liftN hΔ hΓ Ctx.LiftN.one hf₀
    change proofErase Γ (.bvar 1) = _ at EW
    rw [EW, EQ] at R
    obtain ⟨C, _, EC⟩ := proofErase_scoped_typeRecovery_descend
      hstep hΔ hΓ Ctx.LiftN.one hf₀ rfl R
    obtain ⟨F, _, _, EF, _⟩ := ProofShape.liftN_forallE_inv EC
    obtain ⟨A', _, _, EA', _⟩ := ProofShape.liftN_forallE_inv EF
    obtain ⟨_, arg, _, _, Earg⟩ := ProofShape.liftN_app_inv EA'
    cases arg <;> simp [ProofShape.liftN, liftVar] at Earg
  refine ⟨Γ, Q, .bvar 1, x, B, out, hΓ, hxQ, hfQ, ⟨A, rfl⟩, rfl, fun _ => HnoHead, hB, RB,
    Hno (erased_static_structure_eta_expansion_union_descent heq hs), fun _ => Hno,
    fun _ => HnoBeta, HnoNative, ?_⟩
  refine ⟨.app (.bvar 1) (.lam (.app (.bvar 2) (.const info.ctorName [])) (.sort .zero)), ?_, ?_⟩
  · rw [EI, Ex]
    exact .app .refl (.lam (.app .refl CZ) .refl)
  · exact (ScopedCompute.beta Rβ).trans (.app .refl (.lam (.app .refl CY) .refl))

/-- The domain obstruction in the stronger boundary also excludes recovery
of the whole assigned Pi. This retains the earlier generic-family interface. -/
theorem static_structure_generic_family_instantiation_beta_residual_failure
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hz : info.numFields = 0)
    (hS : env.HasType univs [] (.const family []) (.sort (.succ u))) :
    ∃ Γ Q g x B out,
      OnCtx Γ (env.IsType univs) ∧ env.HasType univs Γ x Q ∧
      env.HasType univs Γ g (.forallE Q (.sort (.succ .zero))) ∧
      B = .app g.lift (.bvar 0) ∧
      (∀ Step, ErasedScopedPrimitiveDescent Step →
        ¬ ScopedTypeRecovery Step (proofEraseCtx Γ) (proofErase Γ g)
          (proofErase Γ (.forallE Q (.sort (.succ .zero))))) ∧
      env.HasType univs (Q :: Γ) B (.sort (.succ .zero)) ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionStage D 1) (proofEraseCtx (Q :: Γ))
        (proofErase (Q :: Γ) B) out ∧
      (¬ ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ (B.inst x)) (out.inst (proofErase Γ x))) ∧
      (∀ Step, ErasedScopedPrimitiveDescent Step →
        ¬ ScopedCompute Step (proofEraseCtx Γ)
          (proofErase Γ (B.inst x)) (out.inst (proofErase Γ x))) ∧
      (∀ Step, ErasedScopedPrimitiveDescent Step →
        ¬ ∃ shared, ScopedCompute Step (proofEraseCtx Γ)
            (proofErase Γ (B.inst x)) shared ∧
          ProofShape.BetaRed (out.inst (proofErase Γ x)) shared) ∧
      (¬ ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ x) (proofErase Γ Q)) ∧
      ∃ shared, ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
          (proofErase Γ (B.inst x)) shared ∧
        ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
          (out.inst (proofErase Γ x)) shared := by
  obtain ⟨Γ, Q, g, x, B, out, hΓ, hxQ, hg, _, Ebody, Hdomain, hB, RB,
    Hno, Hall, Hbeta, Hnative, Hjoin⟩ :=
    static_structure_generic_family_domain_instantiation_beta_residual_failure heq hs hi hp hx hz hS
  refine ⟨Γ, Q, g, x, B, out, hΓ, hxQ, hg, Ebody, ?_, hB, RB,
    Hno, Hall, Hbeta, Hnative, Hjoin⟩
  intro Step hstep RN
  obtain ⟨_, hPi⟩ := hg.isType henv hΓ
  rw [show proofErase Γ (.forallE Q (.sort (.succ .zero))) = .forallE _ _ from
    if_neg (not_isProof_of_sort hΓ hPi)] at RN
  exact Hdomain Step hstep _ RN

/-- The generic-family boundary also refutes unrestricted type instantiation.
This preserves the original interface and its explicit full-computation join. -/
theorem static_structure_type_instantiation_beta_residual_failure
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hz : info.numFields = 0)
    (hS : env.HasType univs [] (.const family []) (.sort (.succ u))) :
    ∃ Γ Q x B out,
      OnCtx Γ (env.IsType univs) ∧ env.HasType univs Γ x Q ∧
      env.HasType univs (Q :: Γ) B (.sort (.succ .zero)) ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionStage D 1) (proofEraseCtx (Q :: Γ))
        (proofErase (Q :: Γ) B) out ∧
      (¬ ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ (B.inst x)) (out.inst (proofErase Γ x))) ∧
      (∀ Step, ErasedScopedPrimitiveDescent Step →
        ¬ ScopedCompute Step (proofEraseCtx Γ)
          (proofErase Γ (B.inst x)) (out.inst (proofErase Γ x))) ∧
      (∀ Step, ErasedScopedPrimitiveDescent Step →
        ¬ ∃ shared, ScopedCompute Step (proofEraseCtx Γ)
            (proofErase Γ (B.inst x)) shared ∧
          ProofShape.BetaRed (out.inst (proofErase Γ x)) shared) ∧
      (¬ ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ x) (proofErase Γ Q)) ∧
      ∃ shared, ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
          (proofErase Γ (B.inst x)) shared ∧
        ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
          (out.inst (proofErase Γ x)) shared := by
  obtain ⟨Γ, Q, g, x, B, out, hΓ, hxQ, _, _, _, hB, RB, Hno, Hall, Hbeta, Hnative, Hjoin⟩ :=
    static_structure_generic_family_instantiation_beta_residual_failure heq hs hi hp hx hz hS
  exact ⟨Γ, Q, x, B, out, hΓ, hxQ, hB, RB, Hno, Hall, Hbeta, Hnative, Hjoin⟩

/-- The original exact-instantiation boundary follows from the stronger
pure-beta-residual obstruction. This preserves the earlier interface, including
its explicit full-computation common reduct. -/
theorem static_structure_type_instantiation_exact_failure
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hz : info.numFields = 0)
    (hS : env.HasType univs [] (.const family []) (.sort (.succ u))) :
    ∃ Γ Q x B out,
      OnCtx Γ (env.IsType univs) ∧ env.HasType univs Γ x Q ∧
      env.HasType univs (Q :: Γ) B (.sort (.succ .zero)) ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx (Q :: Γ))
        (proofErase (Q :: Γ) B) out ∧
      (¬ ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ (B.inst x)) (out.inst (proofErase Γ x))) ∧
      (∀ Step, ErasedScopedPrimitiveDescent Step →
        ¬ ScopedCompute Step (proofEraseCtx Γ)
          (proofErase Γ (B.inst x)) (out.inst (proofErase Γ x))) ∧
      ∃ shared, ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
          (proofErase Γ (B.inst x)) shared ∧
        ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
          (out.inst (proofErase Γ x)) shared := by
  obtain ⟨Γ, Q, x, B, out, hΓ, hxQ, hB, RB, Hno, Hall, _, _, Hjoin⟩ :=
    static_structure_type_instantiation_beta_residual_failure heq hs hi hp hx hz hS
  exact ⟨Γ, Q, x, B, out, hΓ, hxQ, hB, RB.mono (fun H => ⟨1, H⟩), Hno, Hall, Hjoin⟩

/-- An ordinarily typed type-valued root beta fork need not have a pure-beta
residual on its computed branch, even if its other branch may use any primitive
language satisfying binder descent. Both branches do have a full-union common
reduct. Thus unrestricted type/beta strip is not an available premise for proving
native output histories. A proof must restrict the beta branch or allow non-beta
computation in the residual; the underlying witness has an uncertified argument. The computed branch already exists at stage one. The example assumes a closed
positive empty structure, as in the original instantiation boundary. -/
theorem static_structure_type_beta_strip_failure
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hz : info.numFields = 0)
    (hS : env.HasType univs [] (.const family []) (.sort (.succ u))) :
    ∃ Γ T left right, OnCtx Γ (env.IsType univs) ∧
      env.HasType univs Γ T (.sort (.succ .zero)) ∧
      ProofShape.BetaRed (proofErase Γ T) left ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionStage D 1) (proofEraseCtx Γ)
        (proofErase Γ T) right ∧
      (∀ Step, ErasedScopedPrimitiveDescent Step →
        ¬ ∃ shared, ScopedCompute Step (proofEraseCtx Γ) left shared ∧
          ProofShape.BetaRed right shared) ∧
      ∃ shared, ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
          left shared ∧
        ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) right shared := by
  obtain ⟨Γ, Q, x, B, out, hΓ, hxQ, hB, RB, _, _, Hno, _, Hjoin⟩ :=
    static_structure_type_instantiation_beta_residual_failure heq hs hi hp hx hz hS
  obtain ⟨_, hQ⟩ := hxQ.isType henv hΓ
  obtain ⟨ht, _, RR⟩ := type_instantiation_compute_peak hΓ hQ hB hxQ RB
  exact ⟨Γ, .app (.lam Q B) x, _, _, hΓ, ht,
    proofErase_beta_forward hΓ ht .beta, RR, Hno, Hjoin⟩

end Lean4Lean.VEnv.Strengthening
