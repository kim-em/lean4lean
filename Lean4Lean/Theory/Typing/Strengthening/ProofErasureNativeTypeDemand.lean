import Lean4Lean.Theory.Typing.Strengthening.ProofErasureIndexedControlTransport

/-! # Recursive computational type observations for lambda control demands

A payload demand observes a Pi's marked domain. A function demand observes its
input domains and dependent result type recursively. The surrounding type
computation uses typed control observations, so its ordinary substitution law
does not require native recovery of substituted arguments.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open PureObservation (Ob)
open ProofShape.IndexedControlObservation
open ProofShape.PiOriginObservation (FixedTail)
variable [Params]

/-- A finite term demand interpreted as a computational observation of its
native type. Functional results live in the actual dependent binder context.
The observed type has a nonzero universe, as required by retained term
demands. Only the base payload predicate fixes original domain information. -/
def NativeTypeDemand (P : Nat → List ProofShape → ProofShape → ProofShape → Prop) :
    Ob → Nat → List ProofShape → ProofShape → Prop
  | .pi, n, Δ, T => ∃ u, ¬ u ≈ .zero ∧ Obs P n Δ (fun _ _ _ => False) T (.sort u) .pi
  | .sort, _, _, _ => False
  | .app keys result, n, Δ, T => ∃ u, ¬ u ≈ .zero ∧
      Obs (fun m Θ A B =>
        (∀ key ∈ keys, NativeTypeDemand P key m Θ A) ∧
        NativeTypeDemand P result (m+1) (A :: Θ) B)
        n Δ (fun _ _ _ => False) T (.sort u) .pi
termination_by o => sizeOf o

/-- Every demanded type has a sort witness inequivalent to Prop. This keeps
fresh variables retained whenever a control function actually demands them. -/
theorem NativeTypeDemand.sort_witness (H : NativeTypeDemand P o n Δ T) :
    ∃ u, ¬ u ≈ .zero ∧ DomainSort Δ T u := by
  cases o with
  | pi =>
    simp only [NativeTypeDemand] at H
    obtain ⟨u, hu, H⟩ := H
    exact ⟨u, hu, H.typing⟩
  | sort => simp only [NativeTypeDemand] at H
  | app keys result =>
    simp only [NativeTypeDemand] at H
    obtain ⟨u, hu, H⟩ := H
    exact ⟨u, hu, H.typing⟩

/-- No demanded native type can have an opaque constant or projection head. -/
theorem NativeTypeDemand.not_primitiveHead (H : NativeTypeDemand P o n Δ T) :
    ¬ PrimitiveHead T := by
  cases o with
  | sort => simp only [NativeTypeDemand] at H
  | pi | app =>
    simp only [NativeTypeDemand] at H
    obtain ⟨_, _, H⟩ := H
    exact H.not_primitiveHead

/-- Any sort witness for a demanded input excludes Prop, so eta retains
the fresh argument whenever it must supply a nonempty control demand. -/
theorem NativeTypeDemand.sort_ne_zero (H : NativeTypeDemand P o n Δ T)
    (SD : DomainSort Δ T u) : ¬ u ≈ .zero := by
  obtain ⟨v, hv, SV⟩ := H.sort_witness
  obtain ⟨Γ, A, hΓ, rfl, hA, EA⟩ := SD
  have SV' : DomainSort (proofEraseCtx Γ) ((proofErase Γ A).liftN 0) v := by
    simpa only [ProofShape.liftN_zero, EA] using SV
  have hAv := SV'.descend hΓ hΓ (Ctx.LiftN.zero []) hA
  have E := (hA.uniqU henv hΓ hAv).sort_inv henv hΓ
  exact fun hu => hv (E.symm.trans hu)

/-- Ordinary typed substitution transports every recursive demand. Images
need no exact native type; the only payload-specific premise is its stated
substitution law. The original variables are fixed by FixedTail. -/
theorem NativeTypeDemand.subst (hP : PayloadSubstitution P)
    (H : NativeTypeDemand P o n Δ T) (W : ContextSubstitution Δ Δ' σ)
    (HT : FixedTail n m σ) : NativeTypeDemand P o m Δ' (T.subst σ) := by
  cases o with
  | pi =>
    simp only [NativeTypeDemand] at H ⊢
    obtain ⟨u, hu, H⟩ := H
    exact ⟨u, hu, H.rename hP W HT (fun _ _ _ h => h.elim)⟩
  | sort => simp only [NativeTypeDemand] at H
  | app keys result =>
    simp only [NativeTypeDemand] at H ⊢
    obtain ⟨u, hu, H⟩ := H
    refine ⟨u, hu, H.rename ?_ W HT (fun _ _ _ h => h.elim)⟩
    intro n m Δ Δ' A B σ W HT HP
    exact ⟨fun key hk => (HP.1 key hk).subst hP W HT,
      HP.2.subst hP W.cons HT.lift⟩
termination_by sizeOf o

/-- A literal Pi exposes exactly the recursive input and result demands. -/
theorem NativeTypeDemand.function_parts
    (H : NativeTypeDemand P (.app keys result) n Δ (.forallE A B)) :
    (∀ key ∈ keys, NativeTypeDemand P key n Δ A) ∧
      NativeTypeDemand P result (n+1) (A :: Δ) B := by
  simp only [NativeTypeDemand] at H
  obtain ⟨_, _, H⟩ := H
  exact H.literal_pi_payload

/-- A literal Pi at a payload demand exposes the indexed base certificate. -/
theorem NativeTypeDemand.payload_parts
    (H : NativeTypeDemand P .pi n Δ (.forallE A B)) : P n Δ A B := by
  simp only [NativeTypeDemand] at H
  obtain ⟨_, _, H⟩ := H
  exact H.literal_pi_payload

/-- Computation preserves all recursive type demands when the base payload
preserves typed component computation. Dependent result observations move to
the computed binder by ordinary context substitution, without joining forks. -/
theorem NativeTypeDemand.compute
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hP : PayloadSubstitution P)
    (hcomp : IndexedPiComponentClosure (ErasedStaticStructureEtaExpansionUnion D) Γ P)
    (H : NativeTypeDemand P o n (proofEraseCtx Γ') (proofErase Γ' T))
    (hΓ' : OnCtx Γ' (env.IsType univs)) (W : Ctx.LiftN n 0 Γ Γ')
    (hT : env.HasType univs Γ' T (.sort u))
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ')
      (proofErase Γ' T) out) : NativeTypeDemand P o n (proofEraseCtx Γ') out := by
  cases o with
  | sort => simp only [NativeTypeDemand] at H
  | pi =>
    simp only [NativeTypeDemand] at H ⊢
    obtain ⟨v, hv, H⟩ := H
    exact ⟨v, hv, proofErase_scoped_compute_indexedControlObservation hP
      (erased_static_structure_eta_expansion_union_descent heq hs)
      (erased_static_structure_union_indexedControlObservation heq hs hP)
      hcomp R hΓ' W hT rfl rfl (fun _ _ _ h => h.elim) H⟩
  | app keys result =>
    simp only [NativeTypeDemand] at H ⊢
    obtain ⟨v, hv, H⟩ := H
    have hsub : PayloadSubstitution (fun m Θ A B =>
        (∀ key ∈ keys, NativeTypeDemand P key m Θ A) ∧
        NativeTypeDemand P result (m+1) (A :: Θ) B) := by
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
