import Lean4Lean.Theory.Typing.AnchoredSortableAppOrigin
import Lean4Lean.Theory.Typing.AnchoredSortableFuture

/-! Future transport of the finite output program, below the rich grammar. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

noncomputable def GeneralOutputPath.future
    {Γ Δ : List VExpr} {ρ : Lift} (henv : env.Ordered)
    (W : FutureInsertion env U Γ Δ ρ)
    (path : GeneralOutputPath env U registry Γ source atom) :
    GeneralOutputPath env U registry Δ (source.rename ρ) (atom.rename ρ) := by
  induction path with
  | refl => exact .refl
  | action path action ih => exact .action ih (action.future henv W)
  | code path action formed ih =>
    exact .code ih (by simpa only [Profile.rename_singleton] using action.future henv W)
      (by simpa only [Profile.rename_singleton, Profile.rename_sort] using
        (Profile.rename_hasType_iff (ρ := ρ)).mpr formed)
  | pad path ih => exact .pad ih
  | unpad path ih => exact .unpad ih

end Lean4Lean.AnchoredSource.Adapted
