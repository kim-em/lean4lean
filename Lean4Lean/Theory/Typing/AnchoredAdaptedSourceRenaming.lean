import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceSyntax
import Lean4Lean.Theory.Typing.AnchoredSourceRenaming

/-! Source renaming for finite adapted observations. Target profiles, adapters
and guards remain in the same world; only genuine source leaves are renamed. -/

namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

private theorem source_cons (ρ : Lift) (σ : Subst) (anchor : VExpr) :
    Subst.lift_l ρ.cons (σ.cons anchor) = (Subst.lift_l ρ σ).cons anchor := by
  funext i
  cases i <;> rfl

mutual
noncomputable def Obs.renameSource
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {Γ : List VExpr}
    {locals : List Nat} {σ : Subst} {expression : VExpr}
    {demand : Profile n} {footprint : Footprint}
    (observation : Obs env U registry Γ locals σ expression demand footprint)
    (ρ : Lift) (τ : Subst) (realized : Subst.lift_l ρ τ = σ) (newLocals : List Nat) :
    Obs env U registry Γ newLocals τ (expression.lift' ρ) demand
      (Footprint.sourceLift ρ footprint) := by
  match observation with
  | .delta lookup nameEq registered seedWF seedLength levelsWF equivalent bodyClosed typeClosed typeCertificate typed body =>
    exact .delta lookup nameEq registered seedWF seedLength levelsWF equivalent bodyClosed typeClosed typeCertificate typed body
  | .native lookup noDefinition nameEq registered seedWF levelsWF equivalent signature typeClosed typeCertificate typed tree =>
    exact .native lookup noDefinition nameEq registered seedWF levelsWF equivalent signature typeClosed typeCertificate typed tree
  | .family lookup noDefinition noNative noQuotient seedWF seedLength levelsWF equivalent signature typeClosed typeCertificate typed tree =>
    exact .family lookup noDefinition noNative noQuotient seedWF seedLength levelsWF equivalent signature typeClosed typeCertificate typed tree
  | .constructor lookup noDefinition noNative noQuotient seedWF seedLength levelsWF equivalent signature typeClosed typeCertificate typed tree =>
    exact .constructor lookup noDefinition noNative noQuotient seedWF seedLength levelsWF equivalent signature typeClosed typeCertificate typed tree
  | .var _ _ i demand => exact .var newLocals τ (ρ.liftVar i) demand
  | .empty => exact .empty
  | .sort relevant => exact .sort relevant
  | .app fn arg arguments admitted =>
    have hf := fn.renameSource ρ τ realized newLocals
    have ha := arg.renameSource ρ τ realized newLocals
    simpa only [lift', Footprint.sourceLift_append] using
      Obs.app hf ha arguments (by simpa only [subst_lift', realized] using admitted)
  | .lam domain guard body normal covered =>
    have hd := domain.renameSource ρ τ realized newLocals
    have hg := guard.sourceRename ρ τ realized
    have hb := body.renameSource ρ.cons (τ.cons _) (by rw [source_cons, realized])
      (Locals.push newLocals)
    simpa only [lift', Footprint.sourceLift_append] using
      Obs.lam hd hg hb (normal.sourceLift ρ) covered
  | .pi domain guard bodies =>
    simpa only [lift', Footprint.sourceLift_append] using
      Obs.pi (domain.renameSource ρ τ realized newLocals)
        (guard.sourceRename ρ τ realized) (bodies.renameSource ρ τ realized newLocals)
  | .union left right =>
    simpa only [Footprint.sourceLift_append] using Obs.union
      (left.renameSource ρ τ realized newLocals) (right.renameSource ρ τ realized newLocals)
  | .view source view => exact .view (source.renameSource ρ τ realized newLocals) view
  | .pad source => exact .pad (source.renameSource ρ τ realized newLocals)
  | .unpad source => exact .unpad (source.renameSource ρ τ realized newLocals)
  | .rowShift source => exact .rowShift (source.renameSource ρ τ realized newLocals)
termination_by sizeOf observation

noncomputable def CodeCert.renameSource
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {Γ : List VExpr}
    {locals : List Nat} {σ : Subst} {expression : VExpr}
    {demand : Profile n} {footprint : Footprint}
    (cert : CodeCert env U registry Γ locals σ expression demand footprint)
    (ρ : Lift) (τ : Subst) (realized : Subst.lift_l ρ τ = σ) (newLocals : List Nat) :
    CodeCert env U registry Γ newLocals τ (expression.lift' ρ) demand
      (Footprint.sourceLift ρ footprint) := by
  match cert with
  | .seed observation formed => exact .seed (observation.renameSource ρ τ realized newLocals) formed
  | .union left right =>
    simpa only [Footprint.sourceLift_append] using CodeCert.union
      (left.renameSource ρ τ realized newLocals) (right.renameSource ρ τ realized newLocals)
  | .pad source => exact .pad (source.renameSource ρ τ realized newLocals)
  | .familyPad source => exact .familyPad (source.renameSource ρ τ realized newLocals)
  | .unpad source => exact .unpad (source.renameSource ρ τ realized newLocals)
  | .map view source => exact .map view (source.renameSource ρ τ realized newLocals)
  | .select source member => exact .select (source.renameSource ρ τ realized newLocals) member
  | .focusMinimal source minimal bound => exact .focusMinimal (source.renameSource ρ τ realized newLocals) minimal bound
  | .down source => exact .down (source.renameSource ρ τ realized newLocals)
termination_by sizeOf cert

noncomputable def PiRows.renameSource
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {Γ : List VExpr}
    {locals : List Nat} {σ : Subst} {A B : VExpr} {ambient : Profile n}
    {rows : List (Key n × Profile n)} {footprint : Footprint}
    (bodies : PiRows env U registry Γ locals σ A B ambient rows footprint)
    (ρ : Lift) (τ : Subst) (realized : Subst.lift_l ρ τ = σ) (newLocals : List Nat) :
    PiRows env U registry Γ newLocals τ (A.lift' ρ) (B.lift' ρ.cons) ambient rows
      (Footprint.sourceLift ρ footprint) := by
  match bodies with
  | .nil => exact .nil
  | .cons guard body normal covered tail =>
    have hb := body.renameSource ρ.cons (τ.cons _) (by rw [source_cons, realized])
      (Locals.push newLocals)
    simpa only [Footprint.sourceLift_append] using
      PiRows.cons (guard.sourceRename ρ τ realized) hb (normal.sourceLift ρ)
        covered (tail.renameSource ρ τ realized newLocals)
termination_by sizeOf bodies
end

end Lean4Lean.AnchoredSource.Adapted
