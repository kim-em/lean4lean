import Lean4Lean.Theory.Typing.Strengthening.ProofErasureNativeGuardMaterialization

/-! # Materialize native guards using only typed computation simulation

Every conversion in a native recovery certificate has a typed source when the
recovered expression does. Replay supplies that source, including for converted
intermediate types. This permits stage simulation restricted to realizable terms.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private erase_app_inv erase_proj_inv erase_lam_inv erase_forallE_inv
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
variable [Params]

/-- Typed root simulation extends to compatible paths. Source descent supplies
an actual typed representative at each transitive intermediate; subterms and
binder scopes are obtained by inversion of the actual source typing. -/
theorem scoped_compute_simulate_typed
    (hstep : ErasedScopedPrimitiveDescent Source)
    (hsim : ∀ {Δ a b}, TypedSource Δ a → Source Δ a b → ScopedCompute Target Δ a b)
    (R : ScopedCompute Source Δ a b) (HT : TypedSource Δ a) :
    ScopedCompute Target Δ a b := by
  induction R with
  | base H => exact hsim HT H
  | beta H => exact .beta H
  | trans R₁ _ ih₁ ih₂ =>
    obtain ⟨Γ, e, T, hΓ, EΓ, ht, Ee⟩ := HT
    obtain ⟨e', HE, EE⟩ := proofErase_scoped_compute_realize hstep hΓ ht EΓ Ee R₁
    exact (ih₁ ⟨Γ, e, T, hΓ, EΓ, ht, Ee⟩).trans
      (ih₂ ⟨Γ, e', T, hΓ, EΓ, HE.hasType.2, EE⟩)
  | app _ _ ihf iha =>
    obtain ⟨Γ, e, T, hΓ, EΓ, ht, Ee⟩ := HT
    obtain ⟨f, a, rfl, _, Ef, Ea⟩ := erase_app_inv Ee
    obtain ⟨_, _, hf, ha⟩ := ht.app_inv henv hΓ
    exact .app (ihf ⟨Γ, f, _, hΓ, EΓ, hf, Ef⟩) (iha ⟨Γ, a, _, hΓ, EΓ, ha, Ea⟩)
  | proj _ ih =>
    obtain ⟨Γ, e, T, hΓ, EΓ, ht, Ee⟩ := HT
    obtain ⟨m, rfl, _, Em⟩ := erase_proj_inv Ee
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ := ht.proj_inv henv hΓ
    exact .proj (ih ⟨Γ, m, _, hΓ, EΓ, hm.hasType.2, Em⟩)
  | lam _ _ ihA ihb =>
    obtain ⟨Γ, e, T, hΓ, EΓ, ht, Ee⟩ := HT
    obtain ⟨A, b, rfl, _, EA, Eb⟩ := erase_lam_inv Ee
    obtain ⟨⟨u, hA⟩, _, hb⟩ := ht.lam_inv henv hΓ
    exact .lam (ihA ⟨Γ, A, _, hΓ, EΓ, hA, EA⟩)
      (ihb ⟨A :: Γ, b, _, ⟨hΓ, u, hA⟩,
        by simp only [proofEraseCtx, EA, EΓ], hb, Eb⟩)
  | forallE _ _ ihA ihB =>
    obtain ⟨Γ, e, T, hΓ, EΓ, ht, Ee⟩ := HT
    obtain ⟨A, B, rfl, _, EA, EB⟩ := erase_forallE_inv Ee
    obtain ⟨⟨u, hA⟩, _, hB⟩ := ht.forallE_inv henv
    exact .forallE (ihA ⟨Γ, A, _, hΓ, EΓ, hA, EA⟩)
      (ihB ⟨A :: Γ, B, _, ⟨hΓ, u, hA⟩,
        by simp only [proofEraseCtx, EA, EΓ], hB, EB⟩)

/-- A typed native certificate has a forward beta-cover with base recovery at
its exact selected type. Only computations with typed sources need simulate;
replay supplies the sort-typed source of each conversion in the certificate.
No assigned-type coverage or stability of recovery under beta is assumed. -/
theorem native_guard_materialize_typed
    (hstep : ErasedScopedPrimitiveDescent Source)
    (hcompute : ∀ {Δ a b}, TypedSource Δ a → ScopedCompute Source Δ a b →
      ScopedCompute Target Δ a b)
    (hid : ∀ {Δ a A}, ScopedTypeRecovery (fun _ => Base) Δ a A →
      ScopedCompute Target Δ a (.app (.lam A (.bvar 0)) a))
    (R : ScopedTypeRecovery Source Δ e T) (HT : TypedSource Δ e) :
    ∃ covered, ScopedCompute Target Δ e covered ∧ BetaRed covered e ∧
      ScopedTypeRecovery (fun _ => Base) Δ covered T := by
  induction R with
  | bvar => exact ⟨_, .refl, .refl, .bvar⟩
  | sort h => exact ⟨_, .refl, .refl, .sort h⟩
  | const hc hw hl => exact ⟨_, .refl, .refl, .const hc hw hl⟩
  | app _ ih =>
    obtain ⟨Γ, e, T, hΓ, EΓ, ht, Ee⟩ := HT
    obtain ⟨f, a, rfl, _, Ef, _⟩ := erase_app_inv Ee
    obtain ⟨_, _, hf, _⟩ := ht.app_inv henv hΓ
    obtain ⟨f', RF, BF, NF⟩ := ih ⟨Γ, f, _, hΓ, EΓ, hf, Ef⟩
    exact ⟨_, .app RF .refl, .app BF .refl, .app NF⟩
  | lam _ ih =>
    obtain ⟨Γ, e, T, hΓ, EΓ, ht, Ee⟩ := HT
    obtain ⟨A, b, rfl, _, EA, Eb⟩ := erase_lam_inv Ee
    obtain ⟨⟨u, hA⟩, _, hb⟩ := ht.lam_inv henv hΓ
    obtain ⟨b', RB, BB, NB⟩ := ih ⟨A :: Γ, b, _, ⟨hΓ, u, hA⟩,
      by simp only [proofEraseCtx, EA, EΓ], hb, Eb⟩
    exact ⟨_, .lam .refl RB, .lam .refl BB, .lam NB⟩
  | forallE _ _ ihA ihB =>
    obtain ⟨Γ, e, T, hΓ, EΓ, ht, Ee⟩ := HT
    obtain ⟨A, B, rfl, _, EA, EB⟩ := erase_forallE_inv Ee
    obtain ⟨⟨u, hA⟩, _, hB⟩ := ht.forallE_inv henv
    obtain ⟨A', RA, BA, NA⟩ := ihA ⟨Γ, A, _, hΓ, EΓ, hA, EA⟩
    obtain ⟨B', RB, BB, NB⟩ := ihB ⟨A :: Γ, B, _, ⟨hΓ, u, hA⟩,
      by simp only [proofEraseCtx, EA, EΓ], hB, EB⟩
    have NB' := base_recovery_backward_oracle NB (Δ' := A' :: _) (fun i => by
      cases i with
      | zero => exact BA.liftN
      | succ i => exact .refl)
    exact ⟨_, .forallE RA RB, .forallE BA BB, .forallE NA NB'⟩
  | proj hi HP hj hl _ ih =>
    obtain ⟨Γ, e, T, hΓ, EΓ, ht, Ee⟩ := HT
    obtain ⟨m, rfl, _, Em⟩ := erase_proj_inv Ee
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ := ht.proj_inv henv hΓ
    obtain ⟨m', RM, BM, NM⟩ := ih ⟨Γ, m, _, hΓ, EΓ, hm.hasType.2, Em⟩
    exact ⟨_, .proj RM, .proj BM,
      (ScopedTypeRecovery.proj hi HP hj hl NM).convert
        (.beta (projectionType_beta (Lean4Lean.List.Forall₂.rfl (fun _ _ => .refl)) BM))⟩
  | @convert Δ e A B RN RC ih =>
    obtain ⟨covered, Rcover, Bcover, Ncover⟩ := ih HT
    obtain ⟨Γ, actual, T, hΓ, EΓ, ht, Ee⟩ := HT
    obtain ⟨actualA, heA, EA⟩ := proofErase_scoped_typeRecovery_replay hstep hΓ ht
      (by simpa only [EΓ, Ee] using RN)
    obtain ⟨u, hA⟩ := heA.isType henv hΓ
    have RC' := hcompute ⟨Γ, actualA, _, hΓ, EΓ, hA, EA⟩ RC
    have NN : ScopedTypeRecovery (fun _ => Base) Δ (.app (.lam B (.bvar 0)) covered) B := by
      have H : ScopedTypeRecovery (fun _ => Base) Δ
          (.app (.lam B (.bvar 0)) covered) ((B.liftN 1).inst covered) := .app (.lam .bvar)
      simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN, ProofShape.Subst.one,
        ProofShape.lift_subst_cons, ProofShape.subst_id] using H
    have RB : BetaRed (.app (.lam B (.bvar 0)) covered) covered := by
      simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN, ProofShape.subst,
        ProofShape.Subst.one, ProofShape.Subst.cons] using
        (BetaRed.beta (A := B) (b := .bvar 0) (a := covered))
    exact ⟨_, Rcover.trans ((hid Ncover).trans (.app (.lam RC' .refl) .refl)),
      RB.trans Bcover, NN⟩

/-- If typed Source computations already simulate in stage one, every typed Source native
guard can be materialized at stage zero by a stage-one forward path. This is a
conditional simulation tool, not a claim that all higher stages have collapsed. -/
theorem first_stage_native_guard_materialize_typed
    (hstep : ErasedScopedPrimitiveDescent Source)
    (hcompute : ∀ {Δ a b}, TypedSource Δ a → ScopedCompute Source Δ a b →
      ScopedCompute (ErasedStaticStructureEtaExpansionStage D 1) Δ a b)
    (R : ScopedTypeRecovery Source Δ e T) (HT : TypedSource Δ e) :
    ∃ covered, ScopedCompute (ErasedStaticStructureEtaExpansionStage D 1) Δ e covered ∧
      BetaRed covered e ∧ ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D 0) Δ covered T := by
  exact native_guard_materialize_typed hstep hcompute
    (Base := fun a b => ErasedStaticStructureEtaExpansionStage D 0 [] a b)
    (fun H => .base (.inr (.inr (.inr (.inl (.intro H)))))) R HT

/-- Native identity introduces no new stage beyond simulation of the guard's
computations: materialize the source, expand at stage zero, then beta-contract
the cover inside the resulting identity application. -/
theorem first_stage_native_identity_simulation_typed
    (hstep : ErasedScopedPrimitiveDescent Source)
    (hcompute : ∀ {Δ a b}, TypedSource Δ a → ScopedCompute Source Δ a b →
      ScopedCompute (ErasedStaticStructureEtaExpansionStage D 1) Δ a b)
    (R : NativeIdentityExpansion Source Δ a b) (HT : TypedSource Δ a) :
    ScopedCompute (ErasedStaticStructureEtaExpansionStage D 1) Δ a b := by
  cases R with
  | intro RN =>
    obtain ⟨covered, RC, BC, NC⟩ := first_stage_native_guard_materialize_typed hstep hcompute RN HT
    exact RC.trans ((ScopedCompute.base (.inr (.inr (.inr (.inl (.intro NC)))))).trans
      (.beta (.app .refl BC)))

/-- Function eta likewise needs no additional stage once guard computations
simulate in stage one. The selected domain is exact and the original source is
restored inside the eta body by beta; no guard transfer across beta is used. -/
theorem first_stage_native_eta_simulation_typed
    (hstep : ErasedScopedPrimitiveDescent Source)
    (hcompute : ∀ {Δ a b}, TypedSource Δ a → ScopedCompute Source Δ a b →
      ScopedCompute (ErasedStaticStructureEtaExpansionStage D 1) Δ a b)
    (R : NativeEtaExpansion Source Δ a b) (HT : TypedSource Δ a) :
    ScopedCompute (ErasedStaticStructureEtaExpansionStage D 1) Δ a b := by
  cases R with
  | intro RN SD =>
    obtain ⟨covered, RC, BC, NC⟩ := first_stage_native_guard_materialize_typed hstep hcompute RN HT
    exact RC.trans ((ScopedCompute.base (.inr (.inr (.inr (.inr (.inl (.intro NC SD))))))).trans
      (.beta (.lam .refl (.app BC.liftN .refl))))

/-- Masked structure eta can also use a materialized stage-zero guard. Beta
cleanup restores the original major in every retained field, while erased
proof fields and the complete parameter spine remain unchanged. -/
theorem first_stage_native_structure_simulation_typed
    (hstep : ErasedScopedPrimitiveDescent Source)
    (hcompute : ∀ {Δ a b}, TypedSource Δ a → ScopedCompute Source Δ a b →
      ScopedCompute (ErasedStaticStructureEtaExpansionStage D 1) Δ a b)
    (R : NativeMaskedStructureExpansion Source Δ a b) (HT : TypedSource Δ a) :
    ScopedCompute (ErasedStaticStructureEtaExpansionStage D 1) Δ a b := by
  cases R with
  | intro hi hx ha hp RN =>
    obtain ⟨covered, RC, BC, NC⟩ := first_stage_native_guard_materialize_typed hstep hcompute RN HT
    exact RC.trans ((ScopedCompute.base (.inr (.inr (.inr (.inr (.inr (.intro hi hx ha hp NC))))))).trans
      (nativeStructureOutput_compute (Lean4Lean.List.Forall₂.rfl (fun _ _ => .refl)) (.beta BC)))

end Lean4Lean.VEnv.Strengthening
