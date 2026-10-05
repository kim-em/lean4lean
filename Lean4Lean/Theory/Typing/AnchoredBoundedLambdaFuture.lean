import Lean4Lean.Theory.Typing.AnchoredBoundedLambdaType
import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceLambdaFuture

namespace Lean4Lean.AnchoredSource.Adapted.Staged
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false
variable {current : Name → Bool} {fuel : Nat}

noncomputable def LambdaTypeResult.future
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) {target future : List VExpr} {ρ : Lift}
    (insertion : FutureInsertion env U target future ρ)
    {locals : List Nat} {realization : Subst} {available : Valuation}
    {inputFootprint : Footprint} {A B body other : VExpr}
    {key : Key n} {output : Atom n} {domain : Profile n}
    (fixed : LambdaTypeResult current fuel env U registry target locals realization available
      (inputFootprint.localNeeds ++ inputFootprint.localNeeds.flatMap Need.singletons) A B body other key output domain) :
    LambdaTypeResult current fuel env U registry future locals (realization.lift_r ρ)
      (Valuation.rename ρ available) ((Footprint.rename ρ inputFootprint).localNeeds ++
        (Footprint.rename ρ inputFootprint).localNeeds.flatMap Need.singletons)
      A B body other (key.rename ρ) (output.rename ρ) (domain.rename ρ) := by
  have bodyPair : ∃ c : CodeCert env U registry future (Locals.push locals)
      ((realization.cons key.anchor).lift_r ρ) B (fixed.resultSupport.rename ρ)
      (Footprint.rename ρ fixed.bodyFootprint), c.nativeDepth current ≤ fuel :=
    ⟨fixed.bodyCertificate.future henv insertion, by simpa only [CodeCert.nativeDepth_future] using fixed.bodyBound⟩
  rw [subst_cons_future] at bodyPair
  let bodyCertificate := bodyPair.choose
  have bodyBound := bodyPair.choose_spec
  have codePair : ∃ c : CodeCert env U registry future locals (realization.lift_r ρ) (.forallE A B)
      ((Profile.pi (A.subst realization) (B.subst realization.lift) domain [(key, fixed.resultSupport)]).rename ρ)
      (Footprint.rename ρ fixed.footprint), c.nativeDepth current ≤ fuel :=
    ⟨fixed.certificate.future henv insertion, by simpa only [CodeCert.nativeDepth_future] using fixed.certificateBound⟩
  have profiles :
      ((Profile.pi (A.subst realization) (B.subst realization.lift) domain [(key, fixed.resultSupport)]).rename ρ) =
      Profile.pi (A.subst (realization.lift_r ρ)) (B.subst (realization.lift_r ρ).lift)
        (domain.rename ρ) [(key.rename ρ, fixed.resultSupport.rename ρ)] := by
    simp only [Profile.pi, Profile.rename_singleton, Atom.rename_pi, Rows.rename,
      List.map_cons, List.map_nil, lift'_subst, ← Subst.lift_r_lift]
  rw [profiles] at codePair
  let certificate := codePair.choose
  have certificateBound := codePair.choose_spec
  exact {

    resultSupport := fixed.resultSupport.rename ρ
    bodyFootprint := Footprint.rename ρ fixed.bodyFootprint
    bodyCertificate := bodyCertificate
    bodyAvailable := by
      simpa only [Valuation.rename_push, Footprint.atomized_localNeeds_rename] using
        fixed.bodyAvailable.rename ρ
    outputTyped := by
      simpa only [Profile.rename_singleton] using
        (Profile.rename_hasType_iff (ρ := ρ)).mpr fixed.outputTyped
    footprint := Footprint.rename ρ fixed.footprint
    certificate := certificate
    available := fixed.available.rename ρ
    typed := by
      simpa only [Profile.fn, Profile.pi, Profile.rename_singleton, Atom.rename_fn,
        Atom.rename_pi, Rows.rename, List.map_cons, List.map_nil, lift'_subst,
        ← Subst.lift_r_lift] using
        (Profile.rename_hasType_iff (ρ := ρ)).mpr fixed.typed
    bodyBound := bodyBound
    certificateBound := certificateBound }

end Lean4Lean.AnchoredSource.Adapted.Staged
