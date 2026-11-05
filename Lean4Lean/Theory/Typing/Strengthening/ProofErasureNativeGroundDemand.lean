import Lean4Lean.Theory.Typing.Strengthening.ProofErasureIndexedControlTransport

/-! # Recursive native-type demands with data-valued ground cases

The ground predicate can describe arbitrary retained data types, including
rigid families. Higher-order demands still observe actual dependent Pi types.
Ordinary substitution and complete type computation preserve every recursive
demand when they preserve the ground predicate; no native image premise occurs.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open PureObservation (Ob)
open ProofShape.IndexedControlObservation
open ProofShape.PiOriginObservation (FixedTail)
variable [Params]

/-- A ground term demand uses its given type predicate directly. Function
demands observe input and dependent result demands through complete typed Pi
computations. The ground predicate need not itself have Pi shape. -/
def NativeGroundDemand (P : Nat → List ProofShape → ProofShape → Prop) :
    Ob → Nat → List ProofShape → ProofShape → Prop
  | .pi, n, Δ, T => P n Δ T
  | .sort, _, _, _ => False
  | .app keys result, n, Δ, T => ∃ u, ¬ u ≈ .zero ∧
      Obs (fun m Θ A B =>
        (∀ key ∈ keys, NativeGroundDemand P key m Θ A) ∧
        NativeGroundDemand P result (m+1) (A :: Θ) B)
        n Δ (fun _ _ _ => False) T (.sort u) .pi
termination_by o => sizeOf o

/-- Ground witnesses supply positive sort typing; function demands derive
it from their typed Pi observation. -/
theorem NativeGroundDemand.sort_witness
    (hP : ∀ {n Δ T}, P n Δ T → ∃ u, ¬ u ≈ .zero ∧ DomainSort Δ T u)
    (H : NativeGroundDemand P o n Δ T) : ∃ u, ¬ u ≈ .zero ∧ DomainSort Δ T u := by
  cases o with
  | pi => simp only [NativeGroundDemand] at H; exact hP H
  | sort => simp only [NativeGroundDemand] at H
  | app keys result =>
    simp only [NativeGroundDemand] at H
    obtain ⟨u, hu, H⟩ := H
    exact ⟨u, hu, H.typing⟩

/-- Any sort witness for a demanded input excludes Prop, so eta retains
the fresh argument whenever it must supply a nonempty control demand. -/
theorem NativeGroundDemand.sort_ne_zero
    (hP : ∀ {n Δ T}, P n Δ T → ∃ u, ¬ u ≈ .zero ∧ DomainSort Δ T u)
    (H : NativeGroundDemand P o n Δ T)
    (SD : DomainSort Δ T u) : ¬ u ≈ .zero := by
  obtain ⟨v, hv, SV⟩ := H.sort_witness hP
  obtain ⟨Γ, A, hΓ, rfl, hA, EA⟩ := SD
  have SV' : DomainSort (proofEraseCtx Γ) ((proofErase Γ A).liftN 0) v := by
    simpa only [ProofShape.liftN_zero, EA] using SV
  have hAv := SV'.descend hΓ hΓ (Ctx.LiftN.zero []) hA
  have E := (hA.uniqU henv hΓ hAv).sort_inv henv hΓ
  exact fun hu => hv (E.symm.trans hu)

/-- Ordinary typed substitution transports every recursive demand. Images
need no exact native type; the only ground-specific premise is its stated
substitution law. The original variables are fixed by FixedTail. -/
theorem NativeGroundDemand.subst (hP : ∀ {n m Δ Δ' T σ}, ContextSubstitution Δ Δ' σ → FixedTail n m σ →
      P n Δ T → P m Δ' (T.subst σ))
    (H : NativeGroundDemand P o n Δ T) (W : ContextSubstitution Δ Δ' σ)
    (HT : FixedTail n m σ) : NativeGroundDemand P o m Δ' (T.subst σ) := by
  cases o with
  | pi => simp only [NativeGroundDemand] at H ⊢; exact hP W HT H
  | sort => simp only [NativeGroundDemand] at H
  | app keys result =>
    simp only [NativeGroundDemand] at H ⊢
    obtain ⟨u, hu, H⟩ := H
    refine ⟨u, hu, H.rename ?_ W HT (fun _ _ _ h => h.elim)⟩
    intro n m Δ Δ' A B σ W HT HP
    exact ⟨fun key hk => (HP.1 key hk).subst hP W HT,
      HP.2.subst hP W.cons HT.lift⟩
termination_by sizeOf o

/-- A literal Pi exposes exactly the recursive input and result demands. -/
theorem NativeGroundDemand.function_parts
    (H : NativeGroundDemand P (.app keys result) n Δ (.forallE A B)) :
    (∀ key ∈ keys, NativeGroundDemand P key n Δ A) ∧
      NativeGroundDemand P result (n+1) (A :: Δ) B := by
  simp only [NativeGroundDemand] at H
  obtain ⟨_, _, H⟩ := H
  exact H.literal_pi_payload

/-- Function demands exclude a registered data-family guard even though
ground demands may now describe such a family. -/
theorem NativeGroundDemand.function_not_primitiveHead
    (H : NativeGroundDemand P (.app keys result) n Δ T) : ¬ PrimitiveHead T := by
  simp only [NativeGroundDemand] at H
  obtain ⟨_, _, H⟩ := H
  exact H.not_primitiveHead

/-- Computation preserves all recursive type demands when the ground predicate
preserves complete typed computation. Dependent result observations move to
the computed binder by ordinary context substitution, without joining forks. -/
theorem NativeGroundDemand.compute
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hP : ∀ {n m Δ Δ' T σ}, ContextSubstitution Δ Δ' σ → FixedTail n m σ →
      P n Δ T → P m Δ' (T.subst σ))
    (hcomp : ∀ {Γ' n T u out}, OnCtx Γ' (env.IsType univs) → Ctx.LiftN n 0 Γ Γ' →
      env.HasType univs Γ' T (.sort u) → P n (proofEraseCtx Γ') (proofErase Γ' T) →
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ')
        (proofErase Γ' T) out → P n (proofEraseCtx Γ') out)
    (H : NativeGroundDemand P o n (proofEraseCtx Γ') (proofErase Γ' T))
    (hΓ' : OnCtx Γ' (env.IsType univs)) (W : Ctx.LiftN n 0 Γ Γ')
    (hT : env.HasType univs Γ' T (.sort u))
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ')
      (proofErase Γ' T) out) : NativeGroundDemand P o n (proofEraseCtx Γ') out := by
  cases o with
  | sort => simp only [NativeGroundDemand] at H
  | pi => simp only [NativeGroundDemand] at H ⊢; exact hcomp hΓ' W hT H R
  | app keys result =>
    simp only [NativeGroundDemand] at H ⊢
    obtain ⟨v, hv, H⟩ := H
    have hsub : PayloadSubstitution (fun m Θ A B =>
        (∀ key ∈ keys, NativeGroundDemand P key m Θ A) ∧
        NativeGroundDemand P result (m+1) (A :: Θ) B) := by
      intro n m Δ Δ' A B σ W HT HP
      exact ⟨fun key hk => (HP.1 key hk).subst hP W HT,
        HP.2.subst hP W.cons HT.lift⟩
    refine ⟨v, hv, proofErase_scoped_compute_indexedControlObservation hsub
      (erased_static_structure_eta_expansion_union_descent heq hs)
      (erased_static_structure_union_indexedControlObservation heq hs hsub)
      ?_ R hΓ' W hT rfl rfl (fun _ _ _ h => h.elim) H⟩
    intro Γ₀ m A B v w X Y hΓ₀ W₀ hA hB HP RA RB
    have hΓA : OnCtx (A :: Γ₀) (env.IsType univs) := ⟨hΓ₀, v, hA⟩
    have W₁ : Ctx.LiftN (m+1) 0 Γ (A :: Γ₀) := W₀.comp (by omega) (by omega) Ctx.LiftN.one
    have HB := HP.2.compute heq hs hP hcomp hΓA W₁ hB RB
    obtain ⟨A', HA', EA'⟩ := proofErase_scoped_compute_realize
      (erased_static_structure_eta_expansion_union_descent heq hs) hΓ₀ hA rfl rfl RA
    have HC : IsDefEqCtx env univs [] (A :: Γ₀) (A' :: Γ₀) := .succ (.refl hΓ₀) HA'
    have WC : ContextSubstitution (proofEraseCtx (A :: Γ₀))
        (X :: proofEraseCtx Γ₀) ProofShape.Subst.id := by
      intro Γ₁ hΓ₁ EΓ₁
      simpa only [proofEraseCtx, EA'] using control_context_substitution HC hΓ₁ EΓ₁
    have HT : FixedTail (m+1) (m+1) ProofShape.Subst.id := by intro i; rfl
    refine ⟨fun key hk => (HP.1 key hk).compute heq hs hP hcomp hΓ₀ W₀ hA RA, ?_⟩
    simpa only [ProofShape.subst_id] using HB.subst hP WC HT
termination_by sizeOf o

end Lean4Lean.VEnv.Strengthening
