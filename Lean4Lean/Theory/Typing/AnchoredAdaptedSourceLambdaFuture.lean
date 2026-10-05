import Lean4Lean.Theory.Typing.AnchoredSourceAdaptedLambdaFuture
import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceLambda

namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

noncomputable def LambdaTypeResult.future
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) {target future : List VExpr} {ρ : Lift}
    (insertion : FutureInsertion env U target future ρ)
    {locals : List Nat} {realization : Subst} {available : Valuation}
    {inputFootprint : Footprint} {A B body other : VExpr}
    {key : Key n} {output : Atom n} {domain : Profile n}
    (fixed : LambdaTypeResult env U registry target locals realization available
      (inputFootprint.localNeeds ++ inputFootprint.localNeeds.flatMap Need.singletons) A B body other key output domain) :
    LambdaTypeResult env U registry future locals (realization.lift_r ρ)
      (Valuation.rename ρ available) ((Footprint.rename ρ inputFootprint).localNeeds ++
        (Footprint.rename ρ inputFootprint).localNeeds.flatMap Need.singletons)
      A B body other (key.rename ρ) (output.rename ρ) (domain.rename ρ) where
  resultSupport := fixed.resultSupport.rename ρ
  bodyFootprint := Footprint.rename ρ fixed.bodyFootprint
  bodyCertificate := by
    simpa only [subst_cons_future, Key.rename] using fixed.bodyCertificate.future henv insertion
  bodyAvailable := by
    simpa only [Valuation.rename_push, Footprint.atomized_localNeeds_rename] using
      fixed.bodyAvailable.rename ρ
  outputTyped := by
    simpa only [Profile.rename_singleton] using
      (Profile.rename_hasType_iff (ρ := ρ)).mpr fixed.outputTyped
  footprint := Footprint.rename ρ fixed.footprint
  certificate := by
    simpa only [Profile.pi, Profile.rename_singleton, Atom.rename_pi, Rows.rename,
      List.map_cons, List.map_nil, lift'_subst, ← Subst.lift_r_lift] using
      fixed.certificate.future henv insertion
  available := fixed.available.rename ρ
  typed := by
    simpa only [Profile.fn, Profile.pi, Profile.rename_singleton, Atom.rename_fn,
      Atom.rename_pi, Rows.rename, List.map_cons, List.map_nil, lift'_subst,
      ← Subst.lift_r_lift] using
      (Profile.rename_hasType_iff (ρ := ρ)).mpr fixed.typed

end Lean4Lean.AnchoredSource.Adapted
