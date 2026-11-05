import Lean4Lean.Theory.Typing.Strengthening.ProofErasureChainRepresentatives

/-! # Erased value histories stable under typed substitution

Histories are chains, not forward paths. They have actual typed witnesses but
can be replayed in every realization of their erased context. Typed context
substitution preserves them even when substitution invalidates exact native
guards. These laws provide value payloads for a future rigid-argument observer;
they do not themselves prove argument readout or type-fork joining.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private erase_app_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
variable [Params] {D : PureObservation.Definitions}

/-- A raw value history witnessed in a well-formed realization of its context.
The context and terms are existential witnesses, not extra caller obligations. -/
def ScopedValueChain (D : PureObservation.Definitions) (Δ : List ProofShape)
    (a b : ProofShape) : Prop :=
  ∃ Γ, OnCtx Γ (env.IsType univs) ∧ proofEraseCtx Γ = Δ ∧ ErasedValueChain D Γ a b

/-- A typed chain supplies a scoped history directly. -/
theorem ScopedValueChain.of_typed (hΓ : OnCtx Γ (env.IsType univs))
    (H : TypedComputationEq D Γ a b A) :
    ScopedValueChain D (proofEraseCtx Γ) (proofErase Γ a) (proofErase Γ b) :=
  ⟨Γ, hΓ, rfl, a, b, A, H, rfl, rfl⟩

/-- Interpret a scoped history in any well-formed realization of its context.
Context conversion transports chains; no forward native-guard transport is used. -/
theorem ScopedValueChain.realize
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (H : ScopedValueChain D Δ a b) (hΓ : OnCtx Γ (env.IsType univs))
    (EΓ : proofEraseCtx Γ = Δ) : ErasedValueChain D Γ a b := by
  obtain ⟨Γ', hΓ', EΓ', x, y, A, HC, Ex, Ey⟩ := H
  have W := proofEraseCtx_defeq hΓ' hΓ (EΓ'.trans EΓ.symm)
  refine ⟨x, y, A, HC.defeqCtx heq hs (by trivial) W, ?_, ?_⟩
  · exact (proofErase_defeqCtx hΓ' W HC.defeq.hasType.1).symm.trans Ex
  · exact (proofErase_defeqCtx hΓ' W HC.defeq.hasType.2).symm.trans Ey

/-- Replay the raw history at the actual source term and its actual assignment. -/
theorem ScopedValueChain.replay
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (H : ScopedValueChain D Δ a b) (hΓ : OnCtx Γ (env.IsType univs))
    (EΓ : proofEraseCtx Γ = Δ) (hx : env.HasType univs Γ x A) (Ex : proofErase Γ x = a) :
    ∃ y, TypedComputationEq D Γ x y A ∧ proofErase Γ y = b :=
  (H.realize heq hs hΓ EΓ).replay hΓ hx Ex

/-- The represented source and target can be exchanged. -/
theorem ScopedValueChain.symm (H : ScopedValueChain D Δ a b) : ScopedValueChain D Δ b a := by
  obtain ⟨Γ, hΓ, EΓ, H⟩ := H
  exact ⟨Γ, hΓ, EΓ, H.symm⟩

/-- Composition aligns both erased middle terms and context realizations. -/
theorem ScopedValueChain.trans
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (H : ScopedValueChain D Δ a b) (H' : ScopedValueChain D Δ b c) :
    ScopedValueChain D Δ a c := by
  obtain ⟨Γ, hΓ, EΓ, H⟩ := H
  exact ⟨Γ, hΓ, EΓ, H.trans hΓ (H'.realize heq hs hΓ EΓ)⟩

/-- Arbitrary typed context substitution preserves value histories. Unlike a
forward-path invariant, this law needs no exact native recovery of the images. -/
theorem ScopedValueChain.subst
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (H : ScopedValueChain D Δ a b) (W : ContextSubstitution Δ Δ' τ) :
    ScopedValueChain D Δ' (a.subst τ) (b.subst τ) := by
  obtain ⟨Γ, hΓ, EΓ, x, y, A, HC, Ex, Ey⟩ := H
  obtain ⟨Γ', σ, hΓ', EΓ', WS, ES⟩ := W hΓ EΓ
  refine ⟨Γ', hΓ', EΓ', x.subst σ, y.subst σ, A.subst σ,
    HC.subst heq hs hΓ' WS, ?_, ?_⟩
  · exact (proofErase_subst_with hΓ' WS HC.defeq.hasType.1 ES).trans (congrArg (·.subst τ) Ex)
  · exact (proofErase_subst_with hΓ' WS HC.defeq.hasType.2 ES).trans (congrArg (·.subst τ) Ey)

/-- Full-union computation of the current value appends to its history. -/
theorem ScopedValueChain.compute
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (H : ScopedValueChain D Δ a b)
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) Δ b c) :
    ScopedValueChain D Δ a c := by
  obtain ⟨Γ, hΓ, rfl, x, y, A, HC, Ex, rfl⟩ := H
  obtain ⟨z, HZ, Ez⟩ := TypedComputationEq.realize_compute heq hs hΓ HC.defeq.hasType.2 R
  exact ⟨Γ, hΓ, rfl, x, z, A, HC.trans HZ, Ex, Ez⟩

/-- A scoped history retains a typed source witness. -/
theorem ScopedValueChain.source (H : ScopedValueChain D Δ a b) : TypedSource Δ a := by
  obtain ⟨Γ, hΓ, EΓ, x, y, A, HC, Ex, _⟩ := H
  exact ⟨Γ, x, A, hΓ, EΓ, HC.defeq.hasType.1, Ex⟩

/-- Any typed raw source has a reflexive history. -/
theorem ScopedValueChain.refl (H : TypedSource Δ a) : ScopedValueChain D Δ a a := by
  obtain ⟨Γ, x, A, hΓ, EΓ, hx, Ex⟩ := H
  exact ⟨Γ, hΓ, EΓ, x, x, A, .refl hx, Ex, Ex⟩

/-- Raw application typing supplies separate head and argument witnesses. -/
theorem ProofShape.TypedSource.app_parts (H : TypedSource Δ (.app f a)) :
    TypedSource Δ f ∧ TypedSource Δ a := by
  obtain ⟨Γ, x, T, hΓ, EΓ, hx, Ex⟩ := H
  obtain ⟨f₀, a₀, rfl, _, Ef, Ea⟩ := erase_app_inv Ex
  obtain ⟨A, B, hf, ha⟩ := hx.app_inv henv hΓ
  exact ⟨⟨Γ, f₀, _, hΓ, EΓ, hf, Ef⟩, ⟨Γ, a₀, A, hΓ, EΓ, ha, Ea⟩⟩

/-- A typed raw spine retains typing of its head. -/
theorem ProofShape.TypedSource.mkApps_head : ∀ {args f},
    TypedSource Δ (ProofShape.mkApps f args) → TypedSource Δ f
  | [], _, H => H
  | a :: args, f, H => (TypedSource.mkApps_head (f := .app f a) (args := args) H).app_parts.1

/-- Application congruence needs only an actual source application, allowing
component histories to use different context and term representatives. -/
theorem ScopedValueChain.app
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (HF : ScopedValueChain D Δ f g) (HX : ScopedValueChain D Δ a b)
    (HT : TypedSource Δ (.app f a)) : ScopedValueChain D Δ (.app f a) (.app g b) := by
  obtain ⟨Γ, x, T, hΓ, EΓ, hx, Ex⟩ := HT
  obtain ⟨f₀, a₀, rfl, hn, Ef, Ea⟩ := erase_app_inv Ex
  obtain ⟨A, B, hf, ha⟩ := hx.app_inv henv hΓ
  obtain ⟨g₀, HCf, Eg⟩ := HF.replay heq hs hΓ EΓ hf Ef
  obtain ⟨b₀, HCa, Eb⟩ := HX.replay heq hs hΓ EΓ ha Ea
  have HC := HCf.app hΓ HCa
  have hn' := mt (isProof_congr hΓ HC.defeq).mpr hn
  refine ⟨Γ, hΓ, EΓ, .app f₀ a₀, .app g₀ b₀, _, HC, Ex, ?_⟩
  rw [show proofErase Γ (.app g₀ b₀) = .app (proofErase Γ g₀) (proofErase Γ b₀) from if_neg hn', Eg, Eb]

/-- Pointwise value histories compose along every typed raw application spine.
Proof arguments require no independent comparison of their proposition types. -/
theorem ScopedValueChain.mkApps
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) :
    ∀ {args args' f g}, ScopedValueChain D Δ f g →
      List.Forall₂ (ScopedValueChain D Δ) args args' →
      TypedSource Δ (ProofShape.mkApps f args) →
      ScopedValueChain D Δ (ProofShape.mkApps f args) (ProofShape.mkApps g args') := by
  intro args args' f g HF HA HT
  induction HA generalizing f g with
  | nil => exact HF
  | @cons a b args args' HX _ ih =>
    exact ih (HF.app heq hs HX (TypedSource.mkApps_head (f := .app f a) (args := args) HT)) HT

/-- A common raw reduct gives a value history, even when the actual endpoints
were initially typed at different assignments. No global joining premise enters. -/
theorem ScopedValueChain.of_join
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (HA : TypedSource Δ a) (HB : TypedSource Δ b)
    (RA : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) Δ a shared)
    (RB : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) Δ b shared) :
    ScopedValueChain D Δ a b :=
  ((ScopedValueChain.refl HA).compute heq hs RA).trans heq hs
    ((ScopedValueChain.refl HB).compute heq hs RB).symm

/-- A scoped history between specified same-assignment endpoints reifies as
an exact typed chain, including proof-valued endpoints. -/
theorem ScopedValueChain.at_endpoints
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (H : ScopedValueChain D (proofEraseCtx Γ) (proofErase Γ a) (proofErase Γ b))
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b A) :
    TypedComputationEq D Γ a b A := by
  obtain ⟨b', HC, Eb⟩ := H.replay heq hs hΓ rfl ha rfl
  obtain ⟨u, hA⟩ := ha.isType henv hΓ
  obtain ⟨_, HN⟩ := (proofErase_reflect hΓ HC.defeq.hasType.2 hb Eb).1 ⟨.sort u, hA⟩
  exact HC.trans (.of_erasure_eq ((HN.defeq hΓ).of_l henv hΓ HC.defeq.hasType.2) Eb)

end Lean4Lean.VEnv.Strengthening
