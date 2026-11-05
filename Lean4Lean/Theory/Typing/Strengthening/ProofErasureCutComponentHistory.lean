import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStaticStructureBetaSquares

/-! # Historical certificates for evolving beta-cut components

The domain, body and argument retain forward paths from their original typed
sources. Body history always lives below the original binder; computations
below later binders are pulled back before being appended. No current argument
or current cut is required to retain its original exact native certificate.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params] {D : PureObservation.Definitions}

/-- An actual typed representative and a forward path to its raw erasure.
The equality records replay evidence, not a rule converting arbitrary equations
into computational paths. -/
def TypedForwardHistory (D : PureObservation.Definitions) (Γ : List VExpr)
    (source T : VExpr) (out : ProofShape) : Prop :=
  ∃ e, env.IsDefEq univs Γ source e T ∧ proofErase Γ e = out ∧
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ source) out

/-- A typed source initializes its history with the empty computation. -/
theorem TypedForwardHistory.refl (ht : env.HasType univs Γ e T) :
    TypedForwardHistory D Γ e T (proofErase Γ e) := ⟨e, ht, rfl, .refl⟩

/-- Source-typed replay appends arbitrary full-union computation to a history. -/
theorem TypedForwardHistory.append
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (H : TypedForwardHistory D Γ source T raw)
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) raw out) :
    TypedForwardHistory D Γ source T out := by
  obtain ⟨e, HE, Ee, RC⟩ := H
  obtain ⟨e', HE', Ee'⟩ := proofErase_scoped_compute_realize
    (erased_static_structure_eta_expansion_union_descent heq hs) hΓ HE.hasType.2 rfl Ee R
  exact ⟨e', HE.trans HE', Ee', RC.trans R⟩

/-- A raw cut state consists of its written domain, body and argument. -/
abbrev CutComponents := ProofShape × ProofShape × ProofShape

/-- The literal beta redex represented by a cut state. -/
def CutComponents.redex (s : CutComponents) : ProofShape := .app (.lam s.1 s.2.1) s.2.2

/-- Histories of a marked cut's three components. The body stays under A,
not under the state's possibly changed written domain. This definition demands
no native certificate of any computed component. -/
def CutComponentHistory (D : PureObservation.Definitions) (Γ : List VExpr)
    (A b x : VExpr) (u : VLevel) (B : VExpr) (s : CutComponents) : Prop :=
  TypedForwardHistory D Γ A (.sort u) s.1 ∧
    TypedForwardHistory D (A :: Γ) b B s.2.1 ∧
    TypedForwardHistory D Γ x A s.2.2

/-- All three typed original components initialize the cut history. -/
theorem CutComponentHistory.refl
    (hA : env.HasType univs Γ A (.sort u)) (hb : env.HasType univs (A :: Γ) b B)
    (hx : env.HasType univs Γ x A) :
    CutComponentHistory D Γ A b x u B (proofErase Γ A, proofErase (A :: Γ) b, proofErase Γ x) :=
  ⟨.refl hA, .refl hb, .refl hx⟩

/-- One component round may compute all three children arbitrarily. The body
uses the current domain, exactly as in the compatible computation constructor.
Root expansion or contraction of the whole marked lambda is not a component round. -/
def CutComponentRound (D : PureObservation.Definitions) (Δ : List ProofShape)
    (s t : CutComponents) : Prop :=
  ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) Δ s.1 t.1 ∧
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (s.1 :: Δ) s.2.1 t.2.1 ∧
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) Δ s.2.2 t.2.2

/-- A component round is an actual computation of the marked application. -/
theorem CutComponentRound.compute (R : CutComponentRound D Δ s t) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) Δ s.redex t.redex :=
  .app (.lam R.1 R.2.1) R.2.2

/-- A new body path below the current computed annotation appends to the
original body history by backward native context transport. Domain and argument
paths append independently, even when argument recovery has been lost. -/
theorem CutComponentHistory.advance
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (H : CutComponentHistory D Γ A b x u B s)
    (R : CutComponentRound D (proofEraseCtx Γ) s t) :
    CutComponentHistory D Γ A b x u B t := by
  obtain ⟨HD, HB, HX⟩ := H
  refine ⟨HD.append heq hs hΓ R.1, ?_, HX.append heq hs hΓ R.2.2⟩
  obtain ⟨C, HAC, EC, RA⟩ := HD
  obtain ⟨d, Hbd, Ed, RB⟩ := HB
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, HAC.hasType.1⟩
  have HC : IsDefEqCtx env univs Γ (A :: Γ) (C :: Γ) := .succ .zero HAC
  have hdC := Hbd.hasType.2.defeqDFC henv HC
  have EdC : proofErase (C :: Γ) d = s.2.1 :=
    (proofErase_defeqCtx hΓA HC Hbd.hasType.2).symm.trans Ed
  have RD : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx (C :: Γ))
      (proofErase (C :: Γ) d) t.2.1 := by
    simpa only [proofEraseCtx, EC, EdC] using R.2.1
  have RD' := proofErase_static_structure_union_compute_backward_context heq hs hΓ HAC
    (EC ▸ RA) hdC RD
  exact (show TypedForwardHistory D (A :: Γ) b B s.2.1 from ⟨d, Hbd, Ed, RB⟩).append
    heq hs hΓA (Ed ▸ RD')

/-- Arbitrarily many interleaved component rounds preserve the original
histories. This is an induction on actual finite rounds, not a renewed native
certificate assumption at each intermediate state. -/
theorem CutComponentHistory.rounds
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (H : CutComponentHistory D Γ A b x u B s)
    (R : ReflTransGen (CutComponentRound D (proofEraseCtx Γ)) s t) :
    CutComponentHistory D Γ A b x u B t := by
  induction R with
  | rfl => exact H
  | tail _ R ih => exact ih.advance heq hs hΓ R

/-- Historical paths supply the marked contraction's computational residual
from the original contractum. Only the initial retained argument needs recovery;
the current argument can have no native type at the current written domain. -/
theorem CutComponentHistory.contract
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (H : CutComponentHistory D Γ A b x u B s)
    (HR : ¬ IsProof Γ x → ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D)
      (proofEraseCtx Γ) (proofErase Γ x) (proofErase Γ A)) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (b.inst x)) (s.2.1.inst s.2.2) ∧
      ProofShape.BetaRed s.redex (s.2.1.inst s.2.2) := by
  obtain ⟨⟨_, HA, _, _⟩, ⟨_, HB, _, RB⟩, ⟨_, HX, _, RX⟩⟩ := H
  exact ⟨static_structure_body_argument_square heq hs ⟨hΓ, u, HA.hasType.1⟩
    HB.hasType.1 HX.hasType.1 HR RB RX, .beta⟩

/-- Finite component development commutes with contraction of the original
native cut at the exact final raw contractum, even after repeated binder changes
and loss of exact recovery in the argument. This theorem does not include root
expansions of the function or contractions that destroy the marked outer cut. -/
theorem native_cut_component_development
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) (hb : env.HasType univs (A :: Γ) b B)
    (hx : env.HasType univs Γ x A)
    (HR : ¬ IsProof Γ x → ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D)
      (proofEraseCtx Γ) (proofErase Γ x) (proofErase Γ A))
    (R : ReflTransGen (CutComponentRound D (proofEraseCtx Γ))
      (proofErase Γ A, proofErase (A :: Γ) b, proofErase Γ x) out) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (b.inst x)) (out.2.1.inst out.2.2) ∧
      ProofShape.BetaRed out.redex (out.2.1.inst out.2.2) :=
  ((CutComponentHistory.refl hA hb hx).rounds heq hs hΓ R).contract heq hs hΓ HR

end Lean4Lean.VEnv.Strengthening
