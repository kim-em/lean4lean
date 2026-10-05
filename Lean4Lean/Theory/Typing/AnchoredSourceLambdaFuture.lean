import Lean4Lean.Theory.Typing.AnchoredSourceLambda
import Lean4Lean.Theory.Typing.AnchoredSourceFuture

/-! Literal future transport of the fixed source-lambda anchor package.
Every stored observation, certificate and available local demand is renamed
together; no original-child induction hypothesis is used here. -/

namespace Lean4Lean.AnchoredSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

theorem subst_cons_future (σ : Subst) (anchor : VExpr) (ρ : Lift) :
    (σ.cons anchor).lift_r ρ = (σ.lift_r ρ).cons (anchor.lift' ρ) := by
  funext i
  cases i <;> rfl

theorem Footprint.localNeeds_rename (footprint : Footprint) (ρ : Lift) :
    (Footprint.rename ρ footprint).localNeeds = footprint.localNeeds.map (Need.rename ρ) := by
  induction footprint with
  | nil => rfl
  | cons entry rest ih =>
    rcases entry with ⟨i, need⟩
    cases i <;> simp only [Footprint.rename, List.map_cons, Footprint.localNeeds] at *
    · exact congrArg (List.cons (need.rename ρ)) ih
    · exact ih

theorem Valuation.rename_push (head : List Need) (tail : Valuation) (ρ : Lift) :
    Valuation.rename ρ (Valuation.push head tail) =
      Valuation.push (head.map (Need.rename ρ)) (Valuation.rename ρ tail) := by
  funext i
  cases i <;> rfl

noncomputable def LambdaTypeResult.future
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) {target future : List VExpr} {ρ : Lift}
    (insertion : FutureInsertion env U target future ρ)
    {locals : List Nat} {realization : Subst} {available : Valuation}
    {inputFootprint : Footprint} {A B body other : VExpr}
    {key : Key n} {output : Atom n} {domain : Profile n}
    (fixed : LambdaTypeResult env U registry target locals realization available
      inputFootprint.localNeeds A B body other key output domain) :
    LambdaTypeResult env U registry future locals (realization.lift_r ρ)
      (Valuation.rename ρ available) (Footprint.rename ρ inputFootprint).localNeeds
      A B body other (key.rename ρ) (output.rename ρ) (domain.rename ρ) where
  resultSupport := fixed.resultSupport.rename ρ
  bodyFootprint := Footprint.rename ρ fixed.bodyFootprint
  bodyCertificate := by
    simpa only [subst_cons_future, Key.rename] using fixed.bodyCertificate.future henv insertion
  bodyAvailable := by
    simpa only [Valuation.rename_push, Footprint.localNeeds_rename] using
      fixed.bodyAvailable.rename ρ
  otherFootprint := Footprint.rename ρ fixed.otherFootprint
  otherObservation := by
    simpa only [subst_cons_future, Key.rename, Profile.rename_singleton] using
      fixed.otherObservation.future henv insertion
  otherAvailable := by
    simpa only [Valuation.rename_push, Footprint.localNeeds_rename] using
      fixed.otherAvailable.rename ρ
  outputTyped := by
    simpa only [Profile.rename_singleton] using
      (Profile.rename_hasType_iff (ρ := ρ)).mpr fixed.outputTyped
  anchorRelated := by
    simpa only [lift'_subst, subst_cons_future, Key.rename, Profile.rename_singleton] using
      fixed.anchorRelated.future henv insertion
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

end Lean4Lean.AnchoredSource
