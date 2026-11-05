import Lean4Lean.Theory.Typing.Strengthening.ProofErasureNativeGroundDemand
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureConstructorFrames
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureLambdaDomainNative

/-! # Data-type ancestry below temporary control binders

A complete type history stays in its original context while control variables
are introduced, substituted and removed. Its current realization has positive
sort typing. Recursive ground demands extend this invariant to arbitrary
higher-order control types with genuinely dependent intermediate codomains.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open ProofShape.PiOriginObservation (FixedTail)
open private subst_bvar_liftN from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRenaming
open private inst_interpretation from Lean4Lean.Theory.Typing.Strengthening.ProofErasureRecursivePiObservation
variable [Params] {D : PureObservation.Definitions}

/-- A positive type computed from a fixed lower origin, together with its
lifted raw image and current sort witness. The original type may be a rigid
family application; no Pi shape, closedness or normalization is required. -/
def LowerTypeHistory (D : PureObservation.Definitions) (Γ : List VExpr)
    (origin : ProofShape) (n : Nat) (Δ : List ProofShape) (out : ProofShape) : Prop :=
  ∃ A u, env.HasType univs Γ A (.sort u) ∧ ¬ u ≈ .zero ∧
    (proofErase Γ A).liftN n = out ∧ DomainSort Δ out u ∧
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      origin (proofErase Γ A)

/-- Every historical ground type supplies the positive sort witness needed
to retain demanded control variables under function eta. -/
theorem LowerTypeHistory.sort_witness (H : LowerTypeHistory D Γ origin n Δ out) :
    ∃ u, ¬ u ≈ .zero ∧ DomainSort Δ out u := by
  obtain ⟨_, u, _, hu, _, SD, _⟩ := H
  exact ⟨u, hu, SD⟩

/-- Arbitrary ordinary substitution of temporary controls fixes the lower
type history. Neither argument images nor their types need native recovery. -/
theorem LowerTypeHistory.substitute
    (H : LowerTypeHistory D Γ origin n Δ out)
    (W : ContextSubstitution Δ Δ' σ) (HT : FixedTail n m σ) :
    LowerTypeHistory D Γ origin m Δ' (out.subst σ) := by
  obtain ⟨A, u, hA, hu, rfl, SD, R⟩ := H
  exact ⟨A, u, hA, hu, (HT.payload _).symm, W.sort SD, R⟩

/-- An arbitrary typed temporary binder lifts the history without changing
its original type or path. The temporary binder itself need not have a history. -/
theorem LowerTypeHistory.lift
    (H : LowerTypeHistory D Γ origin n Δ out) (SD : DomainSort Δ A u) :
    LowerTypeHistory D Γ origin (n+1) (A :: Δ) (out.liftN 1) := by
  have HT : FixedTail n (n+1) (fun i => .bvar (i+1)) := by intro i; simp [Nat.add_right_comm]
  have R := H.substitute SD.weak_interpretation HT
  have E : out.subst (fun i => .bvar (i+1)) = out.liftN 1 := by
    simpa only [liftVar, Nat.not_lt_zero, ↓reduceIte, Nat.add_comm] using
      (subst_bvar_liftN (n := 1) (k := 0) out)
  exact E ▸ R

/-- Full computation under a temporary prefix descends to the original
context and extends its history. This is arbitrary type computation, including
native guards, changed binder annotations and subsequent beta contractions. -/
theorem LowerTypeHistory.compute
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (H : LowerTypeHistory D Γ origin n (proofEraseCtx Γ') source)
    (hΓ' : OnCtx Γ' (env.IsType univs)) (W : Ctx.LiftN n 0 Γ Γ')
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ') source out) :
    LowerTypeHistory D Γ origin n (proofEraseCtx Γ') out := by
  obtain ⟨A, u, hA, hu, rfl, SD, RO⟩ := H
  obtain ⟨A', HA', RA', EA'⟩ := proofErase_scoped_compute_certificate_descend
    (erased_static_structure_eta_expansion_union_certificate_descent heq hs)
    hΓ hΓ' W hA rfl R
  exact ⟨A', u, HA'.hasType.2, hu, EA',
    SD.scoped_compute (erased_static_structure_eta_expansion_union_descent heq hs) R, RO.trans RA'⟩

/-- A typed positive source starts its own lower history without a native
certificate or a computed-header condition. -/
theorem LowerTypeHistory.refl
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (hu : ¬ u ≈ .zero) :
    LowerTypeHistory D Γ (proofErase Γ A) 0 (proofEraseCtx Γ) (proofErase Γ A) :=
  ⟨A, u, hA, hu, ProofShape.liftN_zero _, ⟨Γ, A, hΓ, rfl, hA, rfl⟩, .refl⟩

/-- Native recovery of a retained typed term supplies a positive historical
type whenever the selected output has a forward path from the given origin. -/
theorem LowerTypeHistory.of_native
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D)
      (proofEraseCtx Γ) (proofErase Γ e) out)
    (RO : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) origin out) :
    LowerTypeHistory D Γ origin 0 (proofEraseCtx Γ) out := by
  obtain ⟨A, heA, rfl⟩ := proofErase_scoped_typeRecovery_replay
    (erased_static_structure_eta_expansion_union_descent heq hs) hΓ ht RN
  obtain ⟨u, hA⟩ := heA.isType henv hΓ
  have hu := retained_type_level_ne_zero hΓ heA hA
    (fun hp => RN.ne_proof (proofErase_eq_proof.2 hp))
  exact ⟨A, u, hA, hu, ProofShape.liftN_zero _, ⟨Γ, A, hΓ, rfl, hA, rfl⟩, RO⟩

/-- Every native output of a historical constructor frame supplies the new
ground invariant directly. No extra positivity or native-stability premise
is imposed on the current payload or the frame's stored annotation. -/
theorem ConstructorFrameHistory.lower_type_history
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hi : env.projections r info)
    (hp : info.nparams = 1) (hx : info.nindices = 0)
    (HH : ComputedStructureFamilyHeader D r info [])
    (H : ConstructorFrameHistory D Γ r info origin source)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) source out) :
    LowerTypeHistory D Γ origin 0 (proofEraseCtx Γ) out := by
  obtain ⟨_, e, T, ht, Ee, _⟩ := H.witness hΓ
  exact LowerTypeHistory.of_native heq hs hΓ ht (Ee ▸ RN)
    (H.native_origin heq hs hΓ hi hp hx HH RN)

/-- Higher-order type demands whose data results have a lower forward type
history. Intermediate function codomains remain dependent on control binders. -/
abbrev LowerTypeDemand (D : PureObservation.Definitions) (Γ : List VExpr)
    (origin : ProofShape) := NativeGroundDemand (LowerTypeHistory D Γ origin)

/-- Ordinary substitution preserves every higher-order demand, fixing only
the original tail of the context. This includes removal of temporary controls. -/
theorem LowerTypeDemand.substitute
    (H : LowerTypeDemand D Γ origin o n Δ T)
    (W : ContextSubstitution Δ Δ' σ) (HT : FixedTail n m σ) :
    LowerTypeDemand D Γ origin o m Δ' (T.subst σ) :=
  H.subst (fun W HT H => H.substitute W HT) W HT

/-- Complete computation of higher-order annotations preserves their lower
data-type ancestry, including changes to their dependent binder contexts. -/
theorem LowerTypeDemand.compute_type
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (H : LowerTypeDemand D Γ origin o n (proofEraseCtx Γ') (proofErase Γ' T))
    (hΓ' : OnCtx Γ' (env.IsType univs)) (W : Ctx.LiftN n 0 Γ Γ')
    (hT : env.HasType univs Γ' T (.sort u))
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ')
      (proofErase Γ' T) out) : LowerTypeDemand D Γ origin o n (proofEraseCtx Γ') out :=
  H.compute heq hs (fun W HT H => H.substitute W HT)
    (fun hΓ' W _ H R => H.compute heq hs hΓ hΓ' W R) hΓ' W hT R

/-- A historical data type supplies both sides of an identity control arrow.
This constructs the higher-order demand from actual ordinary sort typing,
rather than assuming a demand for the complete function annotation. -/
theorem LowerTypeHistory.identity_type
    (H : LowerTypeHistory D Γ origin n Δ A) :
    LowerTypeDemand D Γ origin (.app [.pi] .pi) n Δ (.forallE A (A.liftN 1)) := by
  obtain ⟨u, hu, SD⟩ := H.sort_witness
  obtain ⟨Γ', A₀, hΓ', rfl, hA₀, rfl⟩ := SD
  have hΓA : OnCtx (A₀ :: Γ') (env.IsType univs) := ⟨hΓ', u, hA₀⟩
  have hB := hA₀.weakN henv (Ctx.LiftN.one (A := A₀))
  have hPi := HasType.forallE hA₀ hB
  have EP : proofErase Γ' (.forallE A₀ A₀.lift) =
      .forallE (proofErase Γ' A₀) ((proofErase Γ' A₀).liftN 1) := by
    rw [show proofErase Γ' (.forallE A₀ A₀.lift) = .forallE _ _ from
      if_neg (not_isProof_of_sort hΓ' hPi), proofErase_liftN hΓ' hΓA Ctx.LiftN.one hA₀]
  have SD : DomainSort (proofEraseCtx Γ') (proofErase Γ' A₀) u := ⟨Γ', A₀, hΓ', rfl, hA₀, rfl⟩
  simp only [LowerTypeDemand, NativeGroundDemand]
  refine ⟨.imax u u, (fun E => hu (VLevel.imax_self.symm.trans E)),
    ProofShape.IndexedControlObservation.Obs.payload ⟨Γ', _, hΓ', rfl, hPi, EP⟩ ?_⟩
  refine ⟨?_, ?_⟩
  · intro key hk
    obtain rfl := List.mem_singleton.1 hk
    simpa only [NativeGroundDemand] using H
  · simpa only [NativeGroundDemand] using H.lift SD

/-- A complete computation of an identity arrow to a literal Pi retains its
historical result type after arbitrary ordinary substitution for the exposed
argument. Written domains can change and intermediate types can be wrapped;
no native certificate for the supplied argument is needed. -/
theorem computed_identity_type_result_history
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (H : LowerTypeHistory D Γ origin 0 (proofEraseCtx Γ) (proofErase Γ A))
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (.forallE A A.lift)) (.forallE X Y))
    (W : ContextSubstitution (X :: proofEraseCtx Γ) (proofEraseCtx Γ) σ)
    (HT : FixedTail 1 0 σ) :
    LowerTypeHistory D Γ origin 0 (proofEraseCtx Γ) (Y.subst σ) := by
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  have hPi := HasType.forallE hA (hA.weakN henv (Ctx.LiftN.one (A := A)))
  have EP : proofErase Γ (.forallE A A.lift) =
      .forallE (proofErase Γ A) ((proofErase Γ A).liftN 1) := by
    rw [show proofErase Γ (.forallE A A.lift) = .forallE _ _ from
      if_neg (not_isProof_of_sort hΓ hPi), proofErase_liftN hΓ hΓA Ctx.LiftN.one hA]
  have HD : LowerTypeDemand D Γ origin (.app [.pi] .pi) 0 (proofEraseCtx Γ)
      (proofErase Γ (.forallE A A.lift)) := EP ▸ H.identity_type
  have HF := HD.compute_type heq hs hΓ hΓ (Ctx.LiftN.zero []) hPi R
  have HB : LowerTypeHistory D Γ origin 1 (X :: proofEraseCtx Γ) Y := by
    simpa only [LowerTypeDemand, NativeGroundDemand] using HF.function_parts.2
  exact HB.substitute W HT

/-- The exposed argument can be any ordinarily typed term at the new domain.
Its concrete substitution supplies the interpretation automatically; exact
native recovery at either the original or computed domain is unnecessary. -/
theorem computed_identity_type_inst_history
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (H : LowerTypeHistory D Γ origin 0 (proofEraseCtx Γ) (proofErase Γ A))
    (hx : env.HasType univs Γ x C)
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (.forallE A A.lift)) (.forallE (proofErase Γ C) Y)) :
    LowerTypeHistory D Γ origin 0 (proofEraseCtx Γ) (Y.inst (proofErase Γ x)) := by
  obtain ⟨v, hC⟩ := hx.isType henv hΓ
  have hΓC : OnCtx (C :: Γ) (env.IsType univs) := ⟨hΓ, v, hC⟩
  have W : ContextSubstitution (proofErase Γ C :: proofEraseCtx Γ) (proofEraseCtx Γ)
      (ProofShape.Subst.one (proofErase Γ x)) := by
    exact inst_interpretation hΓC (Ctx.InstN.zero (Γ₀ := Γ) (e₀ := x) (A₀ := C)) hx
  have HT : FixedTail 1 0 (ProofShape.Subst.one (proofErase Γ x)) := by intro i; simp [ProofShape.Subst.one, ProofShape.Subst.cons, ProofShape.Subst.id, Nat.add_comm]
  simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using
    computed_identity_type_result_history heq hs hΓ hA H R W HT

end Lean4Lean.VEnv.Strengthening
