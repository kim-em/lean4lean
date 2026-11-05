import Lean4Lean.Theory.Typing.Strengthening.ProofErasureConstructorRounds
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureWrapperPivotTransport

/-! # Constructor family histories through administrative frames

Identity frames store the family ancestry of their annotation at creation.
Their arguments may subsequently lose exact recovery at that annotation.
Actual structure expansion can consume the whole framed major and establish
a fresh constructor state, using the frame's history for its selected guard.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params] {D : PureObservation.Definitions}

/-- Any registered guard of a source computing to a monomorphic constructor
has that constructor's family and empty universe instance. The intervening
whole computation is unrestricted and need not preserve native recovery. -/
theorem computed_constructor_registered_guard_shape
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (hi : env.projections r info) (hx : info.nindices = 0)
    (hlen : images.length = info.nparams + info.numFields)
    (R : ScopedCompute Step (proofEraseCtx Γ) (proofErase Γ e)
      (ProofShape.mkApps (.const info.ctorName []) images))
    (hi' : env.projections r' info')
    (RN : ScopedTypeRecovery Step (proofEraseCtx Γ) (proofErase Γ e)
      (ProofShape.mkApps (.const r' ls) ps)) : r' = r ∧ ls = [] := by
  obtain ⟨A, heA, EA⟩ := proofErase_scoped_typeRecovery_replay hstep hΓ ht RN
  obtain ⟨args, rfl, _⟩ := proofErase_const_spine_inv EA
  obtain ⟨e', HE, Ee'⟩ := proofErase_scoped_compute_realize hstep hΓ heA rfl rfl R
  have RB := computed_constructor_image_native (Target := Step) hstep hΓ hi hx hlen heA R
  rw [← Ee'] at RB
  obtain ⟨B, heB, EB⟩ := proofErase_scoped_typeRecovery_replay hstep hΓ HE.hasType.2 RB
  obtain ⟨args', rfl, _⟩ := proofErase_const_spine_inv EB
  obtain ⟨_, hA⟩ := HE.hasType.2.isType henv hΓ
  obtain ⟨E, HL, _⟩ := henv.headInversion.rigid_rigid hΓ
    (henv.projectionRigid hi') (henv.projectionRigid hi)
    ((HE.hasType.2.uniqU henv hΓ heB).typeChain henv hΓ hA)
  cases HL
  exact ⟨E, rfl⟩

/-- A constructor payload, possibly inside nested constant and identity
frames. Identity annotations keep their own forward family ancestry; ordinary
argument typing suffices after the original native guard has disappeared. -/
inductive ConstructorFrameHistory (D : PureObservation.Definitions) (Γ : List VExpr)
    (r : Name) (info : VProjectionInfo) (origin : ProofShape) : ProofShape → Prop where
  | payload : ConstructorFamilyState D Γ r info origin e →
      ConstructorFrameHistory D Γ r info origin e
  | constant : ConstructorFrameHistory D Γ r info origin e →
      ConstructorFrameHistory D Γ r info origin (constantExpansion e)
  | identity : ConstructorFrameHistory D Γ r info origin e → WrapperTypeWitness Γ e A →
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) origin A →
      ConstructorFrameHistory D Γ r info origin (.app (.lam A (.bvar 0)) e)

/-- Every frame source is retained. -/
theorem ConstructorFrameHistory.ne_proof
    (H : ConstructorFrameHistory D Γ r info origin e) : e ≠ .proof := by
  cases H with
  | payload H =>
    obtain ⟨_, _, _, _, _, _, E, _, _⟩ := H
    intro EP
    have HC := congrArg ProofShape.constHead (E.symm.trans EP)
    simp only [constHead_mkApps, ProofShape.constHead] at HC
    cases HC
  | constant | identity => exact ProofShape.noConfusion

/-- Every stored frame has an ordinary typing witness at some assignment. -/
theorem ConstructorFrameHistory.witness
    (hΓ : OnCtx Γ (env.IsType univs))
    (H : ConstructorFrameHistory D Γ r info origin e) : ∃ T, WrapperTypeWitness Γ e T := by
  induction H with
  | payload H =>
    obtain ⟨e, T, _, _, ht, Ee, _⟩ := H
    exact ⟨proofErase Γ T, e, T, ht, Ee, rfl⟩
  | constant H ih =>
    obtain ⟨T, HT⟩ := ih
    exact ⟨T, HT.constant hΓ H.ne_proof⟩
  | identity H HT _ _ => exact ⟨_, HT.identity hΓ H.ne_proof⟩

/-- Removing literal administrative frames beta-exposes a constructor with
its original family ancestry. No native guard is needed for contraction. -/
theorem ConstructorFrameHistory.readout
    (H : ConstructorFrameHistory D Γ r info origin e) :
    ∃ target, BetaRed e target ∧ ConstructorFamilyState D Γ r info origin target := by
  induction H with
  | payload H => exact ⟨_, .refl, H⟩
  | constant _ ih =>
    obtain ⟨target, R, H⟩ := ih
    exact ⟨target, (constantExpansion_beta _).trans R, H⟩
  | @identity e A _ _ _ ih =>
    obtain ⟨target, R, H⟩ := ih
    have RB : BetaRed (.app (.lam A (.bvar 0)) e) e := by
      simpa only [ProofShape.inst, instVar, Nat.lt_irrefl, ↓reduceIte, Nat.sub_self,
        ProofShape.liftN_zero] using (BetaRed.beta (A := A) (b := .bvar 0) (a := e))
    exact ⟨target, RB.trans R, H⟩

/-- Every native selection from a framed constructor follows the fixed
family origin. Identity selections read the stored annotation history rather
than asking the current argument to recover the old annotation again. -/
theorem ConstructorFrameHistory.native_origin
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hi : env.projections r info)
    (hp : info.nparams = 1) (hx : info.nindices = 0)
    (HH : ComputedStructureFamilyHeader D r info [])
    (H : ConstructorFrameHistory D Γ r info origin e)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) e out) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) origin out := by
  induction H generalizing out with
  | payload H => exact H.native_origin heq hs hΓ hi hp hx HH RN
  | constant H ih =>
    obtain ⟨_, e, T, ht, rfl, _⟩ := H.witness hΓ
    have hn : ¬ IsProof Γ e := fun h => H.ne_proof (proofErase_eq_proof.2 h)
    exact ih ((static_structure_constant_expansion_native_iff heq hs hΓ ht hn).1 RN)
  | identity H HT RO _ =>
    obtain ⟨e, A, ht, rfl, rfl⟩ := HT
    have hn : ¬ IsProof Γ e := fun h => H.ne_proof (proofErase_eq_proof.2 h)
    rw [← proofErase_nativeIdentityExpansion hΓ ht hn] at RN
    exact RO.trans (static_structure_identity_native_origin heq hs hΓ ht RN)

/-- Structure expansion consumes a whole framed constructor. Typed beta
readout fixes the selected guard's family, and the stored native history gives
the new parameter's ancestry. All projected fields refer to the whole frame. -/
theorem ConstructorFrameHistory.expand
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hi : env.projections r info)
    (hp : info.nparams = 1) (hx : info.nindices = 0)
    (HH : ComputedStructureFamilyHeader D r info [])
    (H : ConstructorFrameHistory D Γ r info origin source)
    (RE : NativeMaskedStructureExpansion (ErasedStaticStructureEtaExpansionUnion D)
      (proofEraseCtx Γ) source target) :
    ConstructorFamilyState D Γ r info origin target := by
  obtain ⟨_, e, T, ht, Ee, _⟩ := H.witness hΓ
  obtain ⟨major, RB, _, _, p, fields, _, _, Es, hf, _⟩ := H.readout
  have R : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ e) (ProofShape.mkApps (.const info.ctorName []) (p :: fields)) :=
    Ee ▸ Es ▸ ScopedCompute.beta RB
  have hstep : ErasedScopedPrimitiveDescent (ErasedStaticStructureEtaExpansionUnion D) :=
    erased_static_structure_eta_expansion_union_descent heq hs
  have RC : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) source target :=
    .base (erased_static_structure_eta_expansion_union_structure RE)
  obtain ⟨e', HE, Ee'⟩ := proofErase_scoped_compute_realize hstep hΓ ht rfl Ee RC
  cases RE with
  | @intro r' info' ls _ ps hi' hx' ha hps RN =>
    obtain ⟨rfl, rfl⟩ := computed_constructor_registered_guard_shape hstep hΓ ht hi hx
      (by simp [hp, hf, Nat.add_comm]) R hi' (Ee ▸ RN)
    cases henv.ordered.projections_unique hi hi'
    have hps' : ps.length = 1 := hps.trans hp
    cases ps with
    | nil => simp at hps'
    | cons q qs =>
      have Eq : qs = [] := by cases qs <;> simp_all
      subst qs
      exact ⟨e', T, q, (List.range info.numFields).map (nativeStructureField r' info [] source),
        HE.hasType.2, Ee', rfl, by simp, H.native_origin heq hs hΓ hi hp hx HH RN⟩

end Lean4Lean.VEnv.Strengthening
