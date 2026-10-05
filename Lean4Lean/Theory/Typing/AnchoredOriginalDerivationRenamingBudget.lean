import Lean4Lean.Theory.Typing.AnchoredOriginalDerivationRenaming
import Lean4Lean.Theory.Typing.AnchoredOriginalDeclarationDependencies

/-! Structural renaming preserves the exact retained original trees, including
earlier header and projection reserves. Thus closing a new variable over a
weakened original does not replace its dependency budget by a reified proof. -/
namespace Lean4Lean.AnchoredSource.OriginalClosureMeasure
open VExpr VEnv
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

@[simp] theorem Derivation.origin_castIndices
    (H : Derivation env U Γ e1 e2 A)
    (context : Γ = Γ') (left : e1 = e1') (right : e2 = e2') (assigned : A = A') :
    (H.castIndices context left right assigned).origin = H.origin := by
  cases context; cases left; cases right; cases assigned
  rfl

@[simp] theorem Derivation.dependencyOrigin_castIndices
    (henv : Ordered env) (H : Derivation env U Γ e1 e2 A)
    (context : Γ = Γ') (left : e1 = e1') (right : e2 = e2') (assigned : A = A') :
    (H.castIndices context left right assigned).dependencyOrigin henv = H.dependencyOrigin henv := by
  cases context; cases left; cases right; cases assigned
  rfl

@[simp] theorem Derivation.origin_weakN
    (henv : Ordered env) (W : Ctx.LiftN n k Γ Γ') (H : Derivation env U Γ e1 e2 A) :
    (H.weakN henv W).origin = H.origin := by
  induction H generalizing k Γ' with
  | _ => simp_all only [Derivation.weakN, Derivation.origin_castIndices, Derivation.origin]

@[simp] theorem Derivation.dependencyOrigin_weakN
    (henv : Ordered env) (W : Ctx.LiftN n k Γ Γ') (H : Derivation env U Γ e1 e2 A) :
    (H.weakN henv W).dependencyOrigin henv = H.dependencyOrigin henv := by
  induction H generalizing k Γ' with
  | _ => simp_all only [Derivation.weakN, Derivation.dependencyOrigin_castIndices, Derivation.dependencyOrigin]

end Lean4Lean.AnchoredSource.OriginalClosureMeasure
