import Lean4Lean.Theory.Typing.Strengthening.ProofErasureWrapperPivotTransport

/-! # Recursive literal wrappers around historical marked cuts

Each state has a source, a selected pivot, and a common readout. Wrappers retain
ordinary annotation typing separately from their inner native outputs. The
pivot choice at the leaf remains the computed body at the original argument.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives

/-- Literal constant and identity frames can be nested around a marked cut.
The body representative fixes its pivot; annotations belong to their frames. -/
inductive WrappedCut where
  | cut (components : CutComponents) (body : VExpr)
  | done (value : ProofShape)
  | constant (inner : WrappedCut)
  | identity (annotation : ProofShape) (inner : WrappedCut)

/-- The uncontracted side of a wrapped historical cut. -/
def WrappedCut.source : WrappedCut → ProofShape
  | .cut s _ => s.redex
  | .done e => e
  | .constant s => constantExpansion s.source
  | .identity A s => .app (.lam A (.bvar 0)) s.source

/-- The selected pivot uses the same frames as the source. -/
noncomputable def WrappedCut.pivot [Params] (Γ : List VExpr) (x : VExpr) : WrappedCut → ProofShape
  | .cut _ d => proofErase Γ (d.inst x)
  | .done e => e
  | .constant s => constantExpansion (s.pivot Γ x)
  | .identity A s => .app (.lam A (.bvar 0)) (s.pivot Γ x)

/-- Wrapper readout discards the frames and contracts the historical leaf. -/
def WrappedCut.readout : WrappedCut → ProofShape
  | .cut s _ => s.2.1.inst s.2.2
  | .done e => e
  | .constant s | .identity _ s => s.readout

/-- A completed root is already identical to its pivot. All other roots
are applications with lambda control heads, so only expansion primitives apply. -/
theorem WrappedCut.source_root_cases [Params] (s : WrappedCut) (Γ : List VExpr) (x : VExpr) :
    s.source = s.pivot Γ x ∨ (¬ PrimitiveHead s.source) ∧ (∀ u, s.source ≠ .sort u) := by
  cases s with
  | done => exact .inl rfl
  | cut | constant | identity => exact .inr ⟨id, fun _ => ProofShape.noConfusion⟩

/-- Literal identity contraction is independent of both annotation and argument. -/
theorem raw_identity_beta (A e : ProofShape) : ProofShape.BetaRed (.app (.lam A (.bvar 0)) e) e := by
  simpa only [ProofShape.inst, instVar, Nat.lt_irrefl, ↓reduceIte, Nat.sub_self,
    ProofShape.liftN_zero] using (ProofShape.BetaRed.beta (A := A) (b := .bvar 0) (a := e))

/-- Every source beta-reduces to its marked leaf's current contractum. -/
theorem WrappedCut.beta_readout (s : WrappedCut) : ProofShape.BetaRed s.source s.readout := by
  induction s with
  | cut => exact .beta
  | done => exact .refl
  | constant s ih => exact (constantExpansion_beta _).trans ih
  | identity A s ih => exact (raw_identity_beta A s.source).trans ih

variable [Params] {D : PureObservation.Definitions}

/-- Each identity frame stores only ordinary typing of its current argument.
Its native guard is required at creation by WrappedCutStep, not renewed here. -/
inductive WrappedCut.Valid (D : PureObservation.Definitions) (Γ : List VExpr)
    (A b x : VExpr) (u : VLevel) (B : VExpr) : WrappedCut → Prop where
  | cut : CutPivotHistory D Γ A b x u B s d → Valid D Γ A b x u B (.cut s d)
  | done : WrapperTypeWitness Γ e T → e ≠ .proof → Valid D Γ A b x u B (.done e)
  | constant : Valid D Γ A b x u B s → Valid D Γ A b x u B (.constant s)
  | identity : Valid D Γ A b x u B s → WrapperTypeWitness Γ s.source C →
      Valid D Γ A b x u B (.identity C s)

/-- Valid sources remain retained after the marked cut has contracted. -/
theorem WrappedCut.Valid.source_ne_proof (H : WrappedCut.Valid D Γ A b x u B s) : s.source ≠ .proof := by
  cases H with
  | done _ hn => exact hn
  | cut | constant | identity => exact ProofShape.noConfusion

/-- A chosen cut body still gives a typed realization of the evolved redex. -/
theorem CutPivotHistory.source_witness
    (hΓ : OnCtx Γ (env.IsType univs)) (H : CutPivotHistory D Γ A b x u B s d)
    (hn : ¬ IsProof Γ (.app (.lam A b) x)) : ∃ T, WrapperTypeWitness Γ s.redex T := by
  obtain ⟨HH, Hbd, Ed⟩ := H
  obtain ⟨C, HAC, EC, _⟩ := HH.1
  obtain ⟨y, Hxy, Ey, _⟩ := HH.2.2
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, HAC.hasType.1⟩
  have HC : IsDefEqCtx env univs Γ (A :: Γ) (C :: Γ) := .succ .zero HAC
  have hdC := Hbd.hasType.2.defeqDFC henv HC
  have EdC : proofErase (C :: Γ) d = s.2.1 :=
    (proofErase_defeqCtx hΓA HC Hbd.hasType.2).symm.trans Ed
  have HE := IsDefEq.appDF (IsDefEq.lamDF HAC Hbd) Hxy
  have hnr : ¬ IsProof Γ (.app (.lam C d) y) := fun hp => hn ((isProof_congr hΓ HE).2 hp)
  have hnf := not_isProof_fn hΓ (HasType.lam HAC.hasType.2 hdC) (HAC.defeq Hxy.hasType.2) hnr
  refine ⟨_, _, _, HE.hasType.2, ?_, rfl⟩
  rw [show proofErase Γ (.app (.lam C d) y) = .app _ _ from if_neg hnr,
    show proofErase Γ (.lam C d) = .lam _ _ from if_neg hnf, EC, EdC, Ey]
  rfl

/-- The explicitly chosen pivot is retained because it is definitionally
equal to the retained original redex. -/
theorem CutPivotHistory.pivot_ne_proof
    (hΓ : OnCtx Γ (env.IsType univs)) (H : CutPivotHistory D Γ A b x u B s d)
    (hn : ¬ IsProof Γ (.app (.lam A b) x)) : proofErase Γ (d.inst x) ≠ .proof := by
  obtain ⟨_, HAC, _, _⟩ := H.1.1
  obtain ⟨_, Hxy, _, _⟩ := H.1.2.2
  have HE := (IsDefEq.appDF (IsDefEq.lamDF HAC.hasType.1 H.2.1) Hxy.hasType.1).trans
    (IsDefEq.beta H.2.1.hasType.2 Hxy.hasType.1)
  exact fun E => hn ((isProof_congr hΓ HE).2 (proofErase_eq_proof.1 E))

/-- Ordinary source witnesses are available at every current frame. -/
theorem WrappedCut.Valid.source_witness
    (hΓ : OnCtx Γ (env.IsType univs)) (H : WrappedCut.Valid D Γ A b x u B s)
    (hn : ¬ IsProof Γ (.app (.lam A b) x)) : ∃ T, WrapperTypeWitness Γ s.source T := by
  induction H with
  | cut H => exact H.source_witness hΓ hn
  | done HT _ => exact ⟨_, HT⟩
  | @constant s H ih =>
    obtain ⟨T, HT⟩ := ih
    exact ⟨T, HT.constant hΓ H.source_ne_proof⟩
  | @identity s C H HT _ => exact ⟨C, HT.identity hΓ H.source_ne_proof⟩

/-- Every selected pivot is retained, including after all frames have been removed. -/
theorem WrappedCut.Valid.pivot_ne_proof
    (hΓ : OnCtx Γ (env.IsType univs)) (H : WrappedCut.Valid D Γ A b x u B s)
    (hn : ¬ IsProof Γ (.app (.lam A b) x)) : s.pivot Γ x ≠ .proof := by
  cases H with
  | cut H => exact H.pivot_ne_proof hΓ hn
  | done _ hn => exact hn
  | constant | identity => exact ProofShape.noConfusion

/-- Complete native output transfer survives every stored wrapper, even when
the current argument no longer recovers an identity frame's annotation. -/
theorem WrappedCut.Valid.native
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (H : WrappedCut.Valid D Γ A b x u B s)
    (hn : ¬ IsProof Γ (.app (.lam A b) x))
    (HR : ¬ IsProof Γ x → ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D)
      (proofEraseCtx Γ) (proofErase Γ x) (proofErase Γ A)) :
    NativeOutputTransfer (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      s.source (s.pivot Γ x) := by
  induction H with
  | cut H => exact (H.native heq hs hΓ hn HR).1
  | done => exact fun _ RN => RN
  | @constant s H ih =>
    obtain ⟨_, HT⟩ := H.source_witness hΓ hn
    exact ih.constant heq hs hΓ HT H.source_ne_proof
  | @identity s C H HT _ =>
    exact native_output_transfer_identity heq hs hΓ HT H.source_ne_proof _

/-- The selected pivot computes to the same readout that beta exposes from
the current source. No exact native certificate for that readout is asserted. -/
theorem WrappedCut.Valid.compute_readout
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (H : WrappedCut.Valid D Γ A b x u B s)
    (hn : ¬ IsProof Γ (.app (.lam A b) x))
    (HR : ¬ IsProof Γ x → ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D)
      (proofEraseCtx Γ) (proofErase Γ x) (proofErase Γ A)) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) (s.pivot Γ x) s.readout := by
  induction H with
  | cut H => exact (H.native heq hs hΓ hn HR).2
  | done => exact .refl
  | constant _ ih => exact (ScopedCompute.beta (constantExpansion_beta _)).trans ih
  | identity _ _ ih => exact (ScopedCompute.beta (raw_identity_beta _ _)).trans ih

end Lean4Lean.VEnv.Strengthening
