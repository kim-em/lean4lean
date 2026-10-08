import Lean4Lean.Theory.Typing.Strong
import Lean4Lean.Theory.Inductive.RestorationNaturality

namespace Lean4Lean.VEnv
open VExpr InductiveSignature

theorem EqUpToLevels.mkApps_args (H : EqUpToLevels U fn fn')
    (ha : List.Forall₂ (EqUpToLevels U) args args') :
    EqUpToLevels U (VExpr.mkApps fn args) (VExpr.mkApps fn' args') := by
  induction ha generalizing fn fn' with
  | nil => exact H
  | cons h hs ih => exact ih (.app H h)

theorem EqUpToLevels.subst_args (H : EqUpToLevels U e e')
    (hσ : ∀ i, EqUpToLevels U (σ i) (σ' i)) :
    EqUpToLevels U (e.subst σ) (e'.subst σ') := by
  induction H generalizing σ σ' with
  | bvar => exact hσ _
  | const h1 h2 h3 => exact .const h1 h2 h3
  | elim h1 h2 h3 => exact .elim h1 h2 h3
  | sort h1 h2 h3 => exact .sort h1 h2 h3
  | app _ _ ih1 ih2 => exact .app (ih1 hσ) (ih2 hσ)
  | proj _ ih => exact .proj (ih hσ)
  | lam _ _ ih1 ih2 | forallE _ _ ih1 ih2 =>
    constructor
    · exact ih1 hσ
    · apply ih2
      intro i
      cases i with
      | zero => exact .bvar
      | succ i => exact (hσ i).weakN

theorem EqUpToLevels.instantiateParams_args (H : EqUpToLevels U e e')
    (ha : List.Forall₂ (EqUpToLevels U) args args') :
    EqUpToLevels U (instantiateParams e args) (instantiateParams e' args') := by
  apply H.subst_args
  intro i
  have hlen := Lean4Lean.List.Forall₂.length_eq ha
  simp only [← hlen]
  split
  · rename_i hi
    exact List.forall₂_getElem ha _ (by omega) (by omega)
  · exact .bvar

end Lean4Lean.VEnv
namespace Lean4Lean.InductiveSignature
open VEnv

end Lean4Lean.InductiveSignature
