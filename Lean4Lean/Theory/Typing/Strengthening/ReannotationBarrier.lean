import Lean4Lean.Theory.Typing.Strengthening.LeftReannotation

/-! # The exact cost of reflecting reannotation reductions

Even constant-body lambdas encode proposition equality in their annotations.
Reflecting their full reductions from a larger context is equivalent to the
proposition front, despite both endpoints already being well-typed below and the
repaired comparison being reflexive below. This is an equivalence barrier for a
proposed repair lemma, not a new smaller strengthening obligation.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params]
local notation:65 Γ " ⊢ " e " : " A:36 => HasType Params.env univs Γ e A
local notation:65 Γ " ⊢ " e1 " ≡ " e2:36 " : " A:36 => IsDefEq Params.env univs Γ e1 e2 A

/-- A constant-body lambda which retains its domain in its function type. -/
def domainProbe (A : VExpr) : VExpr := .lam A (.sort .zero)

/-- Both probes are typable independently of any relation between their domains. -/
theorem domainProbe_typed (hA : Γ ⊢ A : .sort u) :
    Γ ⊢ domainProbe A : .forallE A (.sort (.succ .zero)) :=
  HasType.lam hA (HasType.sort (by trivial))

/-- Full reannotation of a constant-body lambda is exactly domain conversion.
Independent endpoint typings do not remove this requirement. -/
theorem domainProbe_reduction_iff (hΓ : OnCtx Γ (Params.env.IsType univs))
    (hA : Γ ⊢ A : .sort u) (hB : Γ ⊢ B : .sort v) :
    FullReduction Γ (domainProbe A) (domainProbe B) ↔ IsDefEqU Params.env univs Γ A B := by
  constructor
  · intro R
    obtain ⟨⟨_, H⟩, _⟩ := ((R.hasType hΓ (domainProbe_typed hA)).uniqU henv hΓ
      (domainProbe_typed hB)).forallE_inv henv hΓ
    exact ⟨_, H⟩
  · intro H
    have HBA := (H.of_l henv hΓ hA).symm
    have h : Γ ⊢ domainProbe A : .forallE B (.sort (.succ .zero)) :=
      (IsDefEq.lamDF HBA (HasType.sort (by trivial))).hasType.2
    exact lambda_reannotation h

/-- Proposition strengthening at the fixed environment and universe parameters.
This is the original proposition-front shape, restricted to these parameters. -/
def PropositionFront : Prop :=
  ∀ {Γ Q P R}, OnCtx Γ (Params.env.IsType univs) → Params.env.IsType univs Γ Q →
    (Γ ⊢ P : .sort .zero) → (Γ ⊢ R : .sort .zero) →
    IsDefEqU Params.env univs (Q :: Γ) P.lift R.lift →
    IsDefEqU Params.env univs Γ P R

/-- The proposed lowering rule for just constant-body, proposition-domain probes.
The still-missing rule is not smaller than proposition strengthening: the theorem
below proves equivalence. Both probe endpoints have independent typings below. -/
def ProbeReductionReflection : Prop :=
  ∀ {Γ Q P R}, OnCtx Γ (Params.env.IsType univs) → Params.env.IsType univs Γ Q →
    (Γ ⊢ P : .sort .zero) → (Γ ⊢ R : .sort .zero) →
    FullReduction (Q :: Γ) (domainProbe P.lift) (domainProbe R.lift) →
    FullReduction Γ (domainProbe P) (domainProbe R)

/-- Reflecting even these scope-preserving reannotations is precisely the
proposition front. This equivalence needs no canonical-Eq hypothesis. -/
theorem probeReflection_iff_propositionFront : ProbeReductionReflection ↔ PropositionFront := by
  constructor
  · intro H Γ Q P R hΓ hQ hP hR HE
    have hΓ' : OnCtx (Q :: Γ) (Params.env.IsType univs) := ⟨hΓ, hQ⟩
    have hP' : Q :: Γ ⊢ P.lift : .sort .zero := hP.weak henv
    have hR' : Q :: Γ ⊢ R.lift : .sort .zero := hR.weak henv
    exact (domainProbe_reduction_iff hΓ hP hR).1
      (H hΓ hQ hP hR ((domainProbe_reduction_iff hΓ' hP' hR').2 HE))
  · intro H Γ Q P R hΓ hQ hP hR HR
    have hΓ' : OnCtx (Q :: Γ) (Params.env.IsType univs) := ⟨hΓ, hQ⟩
    have hP' : Q :: Γ ⊢ P.lift : .sort .zero := hP.weak henv
    have hR' : Q :: Γ ⊢ R.lift : .sort .zero := hR.weak henv
    exact (domainProbe_reduction_iff hΓ hP hR).2
      (H hΓ hQ hP hR ((domainProbe_reduction_iff hΓ' hP' hR').1 HR))

/-- The lowered syntax and final certificate in probe repair are available
without domain conversion. Only the reduction from the original probe is missing. -/
theorem domainProbe_repair_certificate (hA : Γ ⊢ A : .sort u) :
    Reannotates (domainProbe A) (domainProbe B) (domainProbe A) ∧
    DomainNormal 0 Γ (domainProbe A) (domainProbe A) :=
  ⟨.lam .keep, .refl (domainProbe_typed hA)⟩

end Lean4Lean.VEnv.Strengthening
