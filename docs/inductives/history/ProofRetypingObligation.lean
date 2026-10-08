import Lean4Lean.Theory.Typing.NativeCaptureTransport
import Lean4Lean.Theory.Typing.SplitProofFrame
import Lean4Lean.Theory.Typing.SplitTypedEmbedding

/-!
This certificate identifies the missing typing obligation in the proposed
proof-opacity bridge. Arbitrary replacement of a proof at a separately supplied
use type is equivalent to actual type-conversion coherence. In particular,
typing a canonical fresh proof variable at that use type already produces the
raw conversion, by reflection along an inhabited proof-context retraction.

This is not a counterexample to the intended calculus or a claim that opacity
cannot participate in a larger coherence proof. It shows the exact additional
theorem that an arbitrary-filled-observer interface would have to establish.
The final theorem records why an original typed source template has a different,
independently justified substitution rule.
-/
namespace Lean4Lean.VEnv.ProofRetypingObligation
open VExpr

private theorem variablePath
    (H : env.HasTypeStrong U Γ e A b) (he : e = .bvar i)
    (hl : Lookup Γ i B) : TypeConversion env U Γ B A := by
  induction H generalizing i B with
  | bvar hl' _ _ =>
    cases he
    cases hl'.uniq hl
    exact .refl
  | base _ ih => exact ih he hl
  | defeq _ hab _ _ _ _ _ ih => exact .tail (ih he hl) hab.defeq
  | _ => cases he

private theorem pathSubst
    (henv : env.Ordered) (hΓ : OnCtx Γ (env.IsType U))
    (W : Ctx.SubstEq env U Γ σ σ Δ)
    (H : TypeConversion env U Δ A B) :
    TypeConversion env U Γ (A.subst σ) (B.subst σ) := by
  induction H with
  | refl => exact .refl
  | tail _ edge ih => exact .tail ih (edge.subst henv W hΓ)

private theorem pathWeak (henv : env.Ordered)
    (H : TypeConversion env U Γ A B) :
    TypeConversion env U (P :: Γ) A.lift B.lift := by
  induction H with
  | refl => exact .refl
  | tail _ edge ih => exact .tail ih (edge.weak henv)

/-- Retyping a fresh proof variable is already an actual raw type path,
    because the inhabited proof extension has a typed retraction. -/
theorem freshProofTyping_iff_typePath
    (henv : env.Ordered) (hΓ : OnCtx Γ (env.IsType U))
    (hP : env.HasType U Γ P (.sort .zero))
    (hq : env.HasType U Γ q P) :
    env.HasType U (P :: Γ) (.bvar 0) R.lift ↔
      TypeConversion env U Γ P R := by
  constructor
  · intro H
    let F := (SplitProofFrame.refl henv hΓ).cons henv hP hq
    have hp := variablePath (H.strong henv F.targetWF).hasType'.1 rfl
      (show Lookup (P :: Γ) 0 P.lift from .zero)
    have hr := pathSubst henv hΓ F.typed hp
    change TypeConversion env U Γ
      ((P.liftN 1).subst F.retract) ((R.liftN 1).subst F.retract) at hr
    simpa only [F.leftInv] using hr
  · intro H
    exact (pathWeak (P := P) henv H).cast (.bvar .zero)

def ProofRetype (env : VEnv) (U : Nat) : Prop :=
  ∀ Γ P R q z, OnCtx Γ (env.IsType U) →
    env.HasType U Γ P (.sort .zero) → env.HasType U Γ q P →
    env.HasType U Γ z P → env.HasType U Γ q R → env.HasType U Γ z R

def ProofTypeCoherence (env : VEnv) (U : Nat) : Prop :=
  ∀ Γ P R q, OnCtx Γ (env.IsType U) →
    env.HasType U Γ P (.sort .zero) → env.HasType U Γ q P →
    env.HasType U Γ q R → TypeConversion env U Γ P R

theorem proofRetype_iff_typeCoherence (henv : env.Ordered) :
    ProofRetype env U ↔ ProofTypeCoherence env U := by
  constructor
  · intro H Γ P R q hΓ hP hq hqR
    apply (freshProofTyping_iff_typePath henv hΓ hP hq).1
    exact H (P :: Γ) P.lift R.lift q.lift (.bvar 0)
      ⟨hΓ, _, hP⟩ (hP.weak henv) (hq.weak henv) (.bvar .zero) (hqR.weak henv)
  · intro H Γ P R q z hΓ hP hq hz hqR
    exact (H Γ P R q hΓ hP hq hqR).cast hz

/-- The restricted source-template case does have an independent producer:
    substitute the ORIGINAL source variable typing, with its conversions. -/
theorem originalVariableTyping_substitutes
    (henv : env.Ordered) (hΔ : OnCtx Δ (env.IsType U))
    (hΓ : OnCtx Γ (env.IsType U))
    (W : Ctx.SubstEq env U Γ σ σ' Δ)
    (H : env.HasType U Δ (.bvar i) R) :
    env.HasType U Γ (σ' i) (R.subst σ) := by
  exact (H.substDF henv hΔ hΓ W).hasType.2

/-- The additional premise supplied structurally by a fully annotated calculus.
It is NOT established here for the production raw calculus, where obtaining it
from `IsDefEq.uniq` would use the foundation we are trying to replace. -/
def SameTermTypeCoherence (env : VEnv) (U : Nat) : Prop :=
  ∀ Γ e A B, OnCtx Γ (env.IsType U) →
    env.HasType U Γ e A → env.HasType U Γ e B → TypeConversion env U Γ A B

/-- Conditional guard reconstruction through an inhabited proof retraction.
The source typing may have been constructed after substitution: its derivation
is only weakened, never inverted or used as a recursive induction argument.

The open term must already have SOME type, and the desired open domain must
already be formed. Coherence is used on the SAME round-trip term at two types.
This checks the proposed annotated producer's algebra; it does not construct
annotated syntax, prove raw coherence, or establish whole-observation lifting. -/
theorem guardPathAlongSplit
    (henv : env.Ordered) (coherence : SameTermTypeCoherence env U)
    (F : SplitTypedEmbedding env U Γ Δ)
    (he : env.HasType U Δ e C) (hA : env.HasType U Δ A (.sort u))
    (sourceGuard : env.HasType U Γ (e.subst F.retract) (A.subst F.retract)) :
    TypeConversion env U Δ C A := by
  have roundTerm := F.roundTrip henv he
  have liftedGuard : env.HasType U Δ
      ((e.subst F.retract).lift' F.liftMap)
      ((A.subst F.retract).lift' F.liftMap) := by
    simpa only [← lift'_subst, subst_id] using
      sourceGuard.subst henv F.weakening F.targetWF
  exact .tail
    (coherence Δ _ _ _ F.targetWF roundTerm.hasType.2 liftedGuard)
    (F.roundTrip henv hA).symm

/-- The same producer under a retained dependent binder. Its source domain is
the retraction of the already formed OPEN domain, not an independently assumed
equal domain. `underBinder` supplies the context conversions without inversion. -/
theorem guardPathUnderBinder
    (henv : env.Ordered) (coherence : SameTermTypeCoherence env U)
    (F : SplitTypedEmbedding env U Γ Δ)
    (hD : env.HasType U Δ D (.sort v))
    (he : env.HasType U (D :: Δ) e C)
    (hA : env.HasType U (D :: Δ) A (.sort u))
    (sourceGuard : env.HasType U (D.subst F.retract :: Γ)
      (e.subst F.retract.lift) (A.subst F.retract.lift)) :
    TypeConversion env U (D :: Δ) C A :=
  guardPathAlongSplit henv coherence (F.underBinder henv hD) he hA sourceGuard

#print axioms freshProofTyping_iff_typePath
#print axioms proofRetype_iff_typeCoherence
#print axioms originalVariableTyping_substitutes
#print axioms guardPathAlongSplit
#print axioms guardPathUnderBinder

end Lean4Lean.VEnv.ProofRetypingObligation
