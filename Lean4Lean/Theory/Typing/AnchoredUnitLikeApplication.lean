import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceSyntax

/-! A field-free major is admitted by an ordinary empty-input function row.
The raw equality is the actual registered unit rule; no observation of an
arbitrary assigned type is introduced into the source grammar. -/
namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles

theorem Admitted.unitLikeEmpty
    {env : VEnv} {U n : Nat} {registry : CanonicalHead.Registry} {target : List VExpr}
    {info : VProjectionInfo} {name : Name} {levels : List VLevel} {params : List VExpr}
    (registered : env.projections name info)
    (paramCount : params.length = info.nparams)
    (unindexed : info.nindices = 0) (noFields : info.numFields = 0)
    {anchor left right : VExpr}
    (anchorTyped : env.HasType U target anchor (mkApps (.const name levels) params))
    (leftTyped : env.HasType U target left (mkApps (.const name levels) params))
    (rightTyped : env.HasType U target right (mkApps (.const name levels) params)) :
    Admitted env U registry target
      (⟨mkApps (.const name levels) params, anchor, .empty⟩ : Key n) left right := by
  refine ⟨.unitLike registered paramCount unindexed noFields anchorTyped leftTyped,
    .unitLike registered paramCount unindexed noFields leftTyped rightTyped,
    .empty, Profile.HasType.empty Profile.WF.empty,
    Profile.HasType.empty (Profile.HasType.sort true).wf_value, ?_, ?_, ?_⟩
  · cases n <;> exact fun _ _ _ _ member => nomatch member
  · cases n <;> exact fun _ member => nomatch member
  · cases n <;> exact fun _ member => nomatch member

end Lean4Lean.AnchoredSemantics

namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics

/-- Any output atom can use the same field-free major row. The original
function observation fixes the row's domain and anchor, while the source
major contributes no observation leaf. -/
noncomputable def Obs.unitLikeApplication
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {target : List VExpr}
    {locals : List Nat} {σ : Subst}
    {info : VProjectionInfo} {name : Name} {levels : List VLevel} {params : List VExpr}
    (registered : env.projections name info)
    (paramCount : params.length = info.nparams)
    (unindexed : info.nindices = 0) (noFields : info.numFields = 0)
    {function major anchor : VExpr} {output : Atom n} {footprint : Footprint}
    (functionObs : Obs env U registry target locals σ function
      (Profile.fn ⟨mkApps (.const name levels) params, anchor, .empty⟩ output) footprint)
    (anchorTyped : env.HasType U target anchor (mkApps (.const name levels) params))
    (majorTyped : env.HasType U target (major.subst σ) (mkApps (.const name levels) params)) :
    Obs env U registry target locals σ (.app function major) (.singleton output) footprint := by
  simpa only [List.append_nil] using Obs.app functionObs Obs.empty
    (ProfileAdapter.refl _)
    (Admitted.unitLikeEmpty registered paramCount unindexed noFields anchorTyped majorTyped majorTyped)

end Lean4Lean.AnchoredSource.Adapted
