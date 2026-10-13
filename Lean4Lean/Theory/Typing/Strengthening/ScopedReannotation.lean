import Lean4Lean.Theory.Typing.Strengthening.FullScope
import Lean4Lean.Theory.Typing.Strengthening.ReannotationBarrier

/-! # Scope alone does not lower reannotation typings

The constant-body probe reduction can be performed with every eta annotation and
every intermediate term scoped. Reflecting these scoped paths is still equivalent
to the proposition front. The scope result is useful, but does not replace the
missing typing/replay argument.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params]
local notation:65 Γ " ⊢ " e " : " A:36 => HasType Params.env univs Γ e A

/-- A scoped target annotation gives a scoped reannotation path. Its function
 typing premise is still required in the context where the path is constructed. -/
theorem lambda_reannotation_scoped (h : Γ ⊢ .lam D b : .forallE A B)
    (hA : A.Skips n k) : ScopedFullReduction n k Γ (.lam D b) (.lam A b) := by
  refine .tail (.tail .rfl (.funEta h hA)) (.core (.lam .rfl ?_))
  have hb : ParRed (A :: Γ) (.app (.lam D.lift (b.liftN 1 1)) (.bvar 0))
      ((b.liftN 1 1).inst (.bvar 0)) := .beta .rfl .rfl
  simpa only [lift, liftN, inst_liftN_bvar] using hb

/-- Reannotation of the probes remains exactly domain conversion when every
introduced eta annotation is required to omit the removed binders. -/
theorem domainProbe_scoped_reduction_iff (hΓ : OnCtx Γ (Params.env.IsType univs))
    (hA : Γ ⊢ A : .sort u) (hB : Γ ⊢ B : .sort v) (hscope : B.Skips n k) :
    ScopedFullReduction n k Γ (domainProbe A) (domainProbe B) ↔ IsDefEqU env univs Γ A B := by
  constructor
  · intro H
    exact (domainProbe_reduction_iff hΓ hA hB).1 H.full
  · intro H
    have HBA := (H.of_l henv hΓ hA).symm
    have h : Γ ⊢ domainProbe A : .forallE B (.sort (.succ .zero)) :=
      (IsDefEq.lamDF HBA (HasType.sort (by trivial))).hasType.2
    exact lambda_reannotation_scoped h hscope

/-- Reflection restricted to probe paths whose eta annotations are all scoped.
The theorem below identifies its exact logical cost; it is not a smaller front. -/
def ScopedProbeReflection : Prop :=
  ∀ {Γ Q P R}, OnCtx Γ (env.IsType univs) → env.IsType univs Γ Q →
    (Γ ⊢ P : .sort .zero) → (Γ ⊢ R : .sort .zero) →
    ScopedFullReduction 1 0 (Q :: Γ) (domainProbe P.lift) (domainProbe R.lift) →
    FullReduction Γ (domainProbe P) (domainProbe R)

/-- Requiring scope at every eta annotation and intermediate term does not make
probe-path reflection smaller than proposition strengthening. -/
theorem scopedProbeReflection_iff_propositionFront : ScopedProbeReflection ↔ PropositionFront := by
  constructor
  · intro H Γ Q P R hΓ hQ hP hR HE
    have hΓ' : OnCtx (Q :: Γ) (env.IsType univs) := ⟨hΓ, hQ⟩
    have hP' : Q :: Γ ⊢ P.lift : .sort .zero := hP.weak henv
    have hR' : Q :: Γ ⊢ R.lift : .sort .zero := hR.weak henv
    exact (domainProbe_reduction_iff hΓ hP hR).1
      (H hΓ hQ hP hR ((domainProbe_scoped_reduction_iff hΓ' hP' hR' (.liftN)).2 HE))
  · intro H Γ Q P R hΓ hQ hP hR HR
    exact (probeReflection_iff_propositionFront.2 H) hΓ hQ hP hR HR.full

end Lean4Lean.VEnv.Strengthening
