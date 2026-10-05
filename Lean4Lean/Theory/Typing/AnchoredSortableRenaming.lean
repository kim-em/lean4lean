import Lean4Lean.Theory.Typing.AnchoredSortableCert
import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceRenaming

namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

private theorem source_cons (ρ : Lift) (σ : Subst) (anchor : VExpr) :
    Subst.lift_l ρ.cons (σ.cons anchor) = (Subst.lift_l ρ σ).cons anchor := by
  funext i
  cases i <;> rfl

mutual
noncomputable def SortableObs.renameSource
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {Γ : List VExpr}
    {locals : List Nat} {σ : Subst} {expression : VExpr}
    {demand : Profile n} {footprint : Footprint}
    (observation : SortableObs env U registry Γ locals σ expression demand footprint)
    (ρ : Lift) (τ : Subst) (realized : Subst.lift_l ρ τ = σ) (newLocals : List Nat) :
    SortableObs env U registry Γ newLocals τ (expression.lift' ρ) demand
      (Footprint.sourceLift ρ footprint) := by
  match observation with
  | .family lookup noDefinition noNative noQuotient seedWF seedLength levelsWF equivalent signature typeClosed typeCertificate typed tree =>
    exact .family lookup noDefinition noNative noQuotient seedWF seedLength levelsWF equivalent signature typeClosed typeCertificate typed tree
  | .legacy observation => exact .legacy (observation.renameSource ρ τ realized newLocals)
  | .code relevant certificate => exact .code relevant (certificate.renameSource ρ τ realized newLocals)
  | .action source action => exact .action (source.renameSource ρ τ realized newLocals) action
  | .app fn arg arguments admitted =>
    have hf := fn.renameSource ρ τ realized newLocals
    have ha := arg.renameSource ρ τ realized newLocals
    simpa only [lift', Footprint.sourceLift_append] using
      SortableObs.app hf ha arguments (by simpa only [subst_lift', realized] using admitted)
  | .lam domain guard body normal covered =>
    have hd := domain.renameSource ρ τ realized newLocals
    have hg := guard.sourceRename ρ τ realized
    have hb := body.renameSource ρ.cons (τ.cons _) (by rw [source_cons, realized])
      (Locals.push newLocals)
    simpa only [lift', Footprint.sourceLift_append] using
      SortableObs.lam hd hg hb (normal.sourceLift ρ) covered
  | .union left right =>
    simpa only [Footprint.sourceLift_append] using SortableObs.union
      (left.renameSource ρ τ realized newLocals) (right.renameSource ρ τ realized newLocals)
  | .view source view => exact .view (source.renameSource ρ τ realized newLocals) view
  | .pad source => exact .pad (source.renameSource ρ τ realized newLocals)
  | .unpad source => exact .unpad (source.renameSource ρ τ realized newLocals)
  | .rowShift source => exact .rowShift (source.renameSource ρ τ realized newLocals)
termination_by sizeOf observation

noncomputable def SortableCert.renameSource
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {Γ : List VExpr}
    {locals : List Nat} {σ : Subst} {expression : VExpr}
    {demand : Profile n} {footprint : Footprint}
    (cert : SortableCert env U registry Γ locals σ expression relevant demand footprint)
    (ρ : Lift) (τ : Subst) (realized : Subst.lift_l ρ τ = σ) (newLocals : List Nat) :
    SortableCert env U registry Γ newLocals τ (expression.lift' ρ) relevant demand
      (Footprint.sourceLift ρ footprint) := by
  match cert with
  | .ofCode source formed => exact .ofCode (source.renameSource ρ τ realized newLocals) formed
  | .observe source formed => exact .observe (source.renameSource ρ τ realized newLocals) formed
  | .pi domain guard bodies =>
    simpa only [lift', Footprint.sourceLift_append] using
      SortableCert.pi (domain.renameSource ρ τ realized newLocals)
        (guard.sourceRename ρ τ realized) (bodies.renameSource ρ τ realized newLocals)
  | .seed observation formed => exact .seed (observation.renameSource ρ τ realized newLocals) formed
  | .union left right =>
    simpa only [Footprint.sourceLift_append] using SortableCert.union
      (left.renameSource ρ τ realized newLocals) (right.renameSource ρ τ realized newLocals)
  | .pad source => exact .pad (source.renameSource ρ τ realized newLocals)
  | .familyPad source => exact .familyPad (source.renameSource ρ τ realized newLocals)
  | .sortPad source => exact .sortPad (source.renameSource ρ τ realized newLocals)
  | .support action source => exact .support action (source.renameSource ρ τ realized newLocals)
  | .unpad source => exact .unpad (source.renameSource ρ τ realized newLocals)
  | .map view source => exact .map view (source.renameSource ρ τ realized newLocals)
  | .select source member => exact .select (source.renameSource ρ τ realized newLocals) member
  | .focusMinimal source minimal bound => exact .focusMinimal (source.renameSource ρ τ realized newLocals) minimal bound
  | .down source => exact .down (source.renameSource ρ τ realized newLocals)
termination_by sizeOf cert

noncomputable def SortableRows.renameSource
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {Γ : List VExpr}
    {locals : List Nat} {σ : Subst} {A B : VExpr} {ambient : Profile n}
    {rows : List (Key n × Profile n)} {footprint : Footprint}
    (bodies : SortableRows env U registry Γ locals σ A B relevant ambient rows footprint)
    (ρ : Lift) (τ : Subst) (realized : Subst.lift_l ρ τ = σ) (newLocals : List Nat) :
    SortableRows env U registry Γ newLocals τ (A.lift' ρ) (B.lift' ρ.cons) relevant ambient rows
      (Footprint.sourceLift ρ footprint) := by
  match bodies with
  | .nil => exact .nil
  | .cons guard body normal covered tail =>
    have hb := body.renameSource ρ.cons (τ.cons _) (by rw [source_cons, realized])
      (Locals.push newLocals)
    simpa only [Footprint.sourceLift_append] using
      SortableRows.cons (guard.sourceRename ρ τ realized) hb (normal.sourceLift ρ)
        covered (tail.renameSource ρ τ realized newLocals)
termination_by sizeOf bodies
end

end Lean4Lean.AnchoredSource.Adapted
