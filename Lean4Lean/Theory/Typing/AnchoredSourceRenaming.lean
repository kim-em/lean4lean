import Lean4Lean.Theory.Typing.AnchoredSourceFootprint

/-! Source-variable renaming changes neither the target context nor frozen
semantic guards. Its substitution equation is literal syntax; no inverse
weakening of target typing or semantic capabilities is involved. -/

namespace Lean4Lean.AnchoredSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

private theorem source_cons (ρ : Lift) (σ : Subst) (anchor : VExpr) :
    Subst.lift_l ρ.cons (σ.cons anchor) = (Subst.lift_l ρ σ).cons anchor := by
  funext i
  cases i <;> rfl

theorem LambdaGuard.sourceRename
    (guard : LambdaGuard env U registry Γ σ annotation key support)
    (ρ : Lift) (τ : Subst) (realized : Subst.lift_l ρ τ = σ) :
    LambdaGuard env U registry Γ τ (annotation.lift' ρ) key support := by
  refine ⟨guard.inputTyped, guard.formed, ?_, ?_, guard.anchor⟩
  · simpa only [subst_lift', realized] using guard.path
  · simpa only [subst_lift', realized] using guard.domains

theorem PiGuard.sourceRename
    (guard : PiGuard env U Γ σ A B prototypeDomain prototypeBody)
    (ρ : Lift) (τ : Subst) (realized : Subst.lift_l ρ τ = σ) :
    PiGuard env U Γ τ (A.lift' ρ) (B.lift' ρ.cons) prototypeDomain prototypeBody := by
  constructor
  · simpa only [subst_lift', realized] using guard.domainPath
  · simpa only [subst_lift', ← Subst.lift_l_lift, realized] using guard.bodyPath

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
  | .var _ _ i demand => exact .var newLocals τ (ρ.liftVar i) demand
  | .empty => exact .empty
  | .sort relevant => exact .sort relevant
  | .app fn arg admitted =>
    have hf := fn.renameSource ρ τ realized newLocals
    have ha := arg.renameSource ρ τ realized newLocals
    simpa only [lift', Footprint.sourceLift_append] using
      Obs.app hf ha (by simpa only [subst_lift', realized] using admitted)
  | .lam domain guard body normal =>
    have hd := domain.renameSource ρ τ realized newLocals
    have hg := guard.sourceRename ρ τ realized
    have hb := body.renameSource ρ.cons (τ.cons _) (by rw [source_cons, realized])
      (Locals.push newLocals)
    simpa only [lift', Footprint.sourceLift_append] using
      Obs.lam hd hg hb (normal.sourceLift ρ)
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
  | .unpad source => exact .unpad (source.renameSource ρ τ realized newLocals)
  | .map view source => exact .map view (source.renameSource ρ τ realized newLocals)
  | .select source member => exact .select (source.renameSource ρ τ realized newLocals) member
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

theorem LambdaGuard.reflectSource
    (guard : LambdaGuard env U registry Γ σ (annotation.lift' ρ) key support) :
    LambdaGuard env U registry Γ (Subst.lift_l ρ σ) annotation key support := by
  refine ⟨guard.inputTyped, guard.formed, ?_, ?_, guard.anchor⟩
  · simpa only [subst_lift'] using guard.path
  · simpa only [subst_lift'] using guard.domains

theorem PiGuard.reflectSource
    (guard : PiGuard env U Γ σ (A.lift' ρ) (B.lift' ρ.cons) prototypeDomain prototypeBody) :
    PiGuard env U Γ (Subst.lift_l ρ σ) A B prototypeDomain prototypeBody := by
  constructor
  · simpa only [subst_lift'] using guard.domainPath
  · simpa only [subst_lift', ← Subst.lift_l_lift] using guard.bodyPath

private theorem app_lift_inv {f a e : VExpr} {ρ : Lift}
    (h : VExpr.app f a = e.lift' ρ) :
    ∃ f₀ a₀, e = .app f₀ a₀ ∧ f = f₀.lift' ρ ∧ a = a₀.lift' ρ := by
  cases e <;> simp only [lift', app.injEq, reduceCtorEq] at h
  exact ⟨_, _, rfl, h⟩

private theorem lam_lift_inv {A b e : VExpr} {ρ : Lift}
    (h : VExpr.lam A b = e.lift' ρ) :
    ∃ A₀ b₀, e = .lam A₀ b₀ ∧ A = A₀.lift' ρ ∧ b = b₀.lift' ρ.cons := by
  cases e <;> simp only [lift', lam.injEq, reduceCtorEq] at h
  exact ⟨_, _, rfl, h⟩

private theorem pi_lift_inv {A B e : VExpr} {ρ : Lift}
    (h : VExpr.forallE A B = e.lift' ρ) :
    ∃ A₀ B₀, e = .forallE A₀ B₀ ∧ A = A₀.lift' ρ ∧ B = B₀.lift' ρ.cons := by
  cases e <;> simp only [lift', forallE.injEq, reduceCtorEq] at h
  exact ⟨_, _, rfl, h⟩

mutual
theorem Obs.reflectSource
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {Γ : List VExpr}
    {locals : List Nat} {σ : Subst} {expression e : VExpr}
    {demand : Profile n} {footprint : Footprint}
    (observation : Obs env U registry Γ locals σ expression demand footprint)
    (ρ : Lift) (he : expression = e.lift' ρ) (newLocals : List Nat) :
    ∃ required, Nonempty (Obs env U registry Γ newLocals (Subst.lift_l ρ σ) e demand required) ∧
      footprint = Footprint.sourceLift ρ required := by
  match observation with
  | .var _ _ i demand =>
    cases e <;> cases he
    exact ⟨_, ⟨Obs.var newLocals _ _ demand⟩, rfl⟩
  | .empty => exact ⟨[], ⟨Obs.empty⟩, rfl⟩
  | .sort relevant =>
    cases e <;> cases he
    exact ⟨[], ⟨Obs.sort relevant⟩, rfl⟩
  | .app fn arg admitted =>
    obtain ⟨f₀, a₀, rfl, hfn, harg⟩ := app_lift_inv he
    obtain ⟨ff, ⟨hf⟩, hff⟩ := fn.reflectSource ρ hfn newLocals
    obtain ⟨fa, ⟨ha⟩, hfa⟩ := arg.reflectSource ρ harg newLocals
    refine ⟨ff ++ fa, ⟨Obs.app hf ha ?_⟩, ?_⟩
    · simpa only [harg, subst_lift'] using admitted
    · rw [hff, hfa, Footprint.sourceLift_append]
  | .lam domain guard body normal =>
    obtain ⟨A₀, b₀, rfl, hdomain, hbody⟩ := lam_lift_inv he
    obtain ⟨fd, ⟨hd⟩, hfd⟩ := domain.reflectSource ρ hdomain newLocals
    obtain ⟨fb, ⟨hb⟩, hfb⟩ := body.reflectSource ρ.cons hbody (Locals.push newLocals)
    rw [source_cons] at hb
    rw [hdomain] at guard
    rw [hfb] at normal
    obtain ⟨outside, pack, houtside⟩ := normal.sourceLift_inv
    refine ⟨fd ++ outside, ⟨Obs.lam hd guard.reflectSource hb pack⟩, ?_⟩
    rw [hfd, houtside, Footprint.sourceLift_append]
  | .pi domain guard bodies =>
    obtain ⟨A₀, B₀, rfl, hdomain, hbody⟩ := pi_lift_inv he
    obtain ⟨fd, ⟨hd⟩, hfd⟩ := domain.reflectSource ρ hdomain newLocals
    obtain ⟨fb, ⟨hb⟩, hfb⟩ := bodies.reflectSource ρ hdomain hbody newLocals
    rw [hdomain, hbody] at guard
    exact ⟨fd ++ fb, ⟨Obs.pi hd guard.reflectSource hb⟩,
      by rw [hfd, hfb, Footprint.sourceLift_append]⟩
  | .union left right =>
    obtain ⟨fl, ⟨hl⟩, hfl⟩ := left.reflectSource ρ he newLocals
    obtain ⟨fr, ⟨hr⟩, hfr⟩ := right.reflectSource ρ he newLocals
    exact ⟨fl ++ fr, ⟨Obs.union hl hr⟩, by rw [hfl, hfr, Footprint.sourceLift_append]⟩
  | .view source view =>
    obtain ⟨f, ⟨h⟩, hf⟩ := source.reflectSource ρ he newLocals
    exact ⟨f, ⟨Obs.view h view⟩, hf⟩
  | .pad source =>
    obtain ⟨f, ⟨h⟩, hf⟩ := source.reflectSource ρ he newLocals
    exact ⟨f, ⟨Obs.pad h⟩, hf⟩
  | .unpad source =>
    obtain ⟨f, ⟨h⟩, hf⟩ := source.reflectSource ρ he newLocals
    exact ⟨f, ⟨Obs.unpad h⟩, hf⟩
  | .rowShift source =>
    obtain ⟨f, ⟨h⟩, hf⟩ := source.reflectSource ρ he newLocals
    exact ⟨f, ⟨Obs.rowShift h⟩, hf⟩
termination_by sizeOf observation

theorem CodeCert.reflectSource
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {Γ : List VExpr}
    {locals : List Nat} {σ : Subst} {expression e : VExpr}
    {demand : Profile n} {footprint : Footprint}
    (cert : CodeCert env U registry Γ locals σ expression demand footprint)
    (ρ : Lift) (he : expression = e.lift' ρ) (newLocals : List Nat) :
    ∃ required, Nonempty (CodeCert env U registry Γ newLocals (Subst.lift_l ρ σ) e demand required) ∧
      footprint = Footprint.sourceLift ρ required := by
  match cert with
  | .seed observation formed =>
    obtain ⟨f, ⟨h⟩, hf⟩ := observation.reflectSource ρ he newLocals
    exact ⟨f, ⟨CodeCert.seed h formed⟩, hf⟩
  | .union left right =>
    obtain ⟨fl, ⟨hl⟩, hfl⟩ := left.reflectSource ρ he newLocals
    obtain ⟨fr, ⟨hr⟩, hfr⟩ := right.reflectSource ρ he newLocals
    exact ⟨fl ++ fr, ⟨CodeCert.union hl hr⟩, by rw [hfl, hfr, Footprint.sourceLift_append]⟩
  | .pad source =>
    obtain ⟨f, ⟨h⟩, hf⟩ := source.reflectSource ρ he newLocals
    exact ⟨f, ⟨CodeCert.pad h⟩, hf⟩
  | .unpad source =>
    obtain ⟨f, ⟨h⟩, hf⟩ := source.reflectSource ρ he newLocals
    exact ⟨f, ⟨CodeCert.unpad h⟩, hf⟩
  | .map view source =>
    obtain ⟨f, ⟨h⟩, hf⟩ := source.reflectSource ρ he newLocals
    exact ⟨f, ⟨CodeCert.map view h⟩, hf⟩
  | .down source =>
    obtain ⟨f, ⟨h⟩, hf⟩ := source.reflectSource ρ he newLocals
    exact ⟨f, ⟨CodeCert.down h⟩, hf⟩
  | .select source member =>
    obtain ⟨f, ⟨h⟩, hf⟩ := source.reflectSource ρ he newLocals
    exact ⟨f, ⟨CodeCert.select h member⟩, hf⟩
termination_by sizeOf cert

theorem PiRows.reflectSource
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {Γ : List VExpr}
    {locals : List Nat} {σ : Subst} {A B A₀ B₀ : VExpr} {ambient : Profile n}
    {rows : List (Key n × Profile n)} {footprint : Footprint}
    (bodies : PiRows env U registry Γ locals σ A B ambient rows footprint)
    (ρ : Lift) (hA : A = A₀.lift' ρ) (hB : B = B₀.lift' ρ.cons) (newLocals : List Nat) :
    ∃ required, Nonempty (PiRows env U registry Γ newLocals (Subst.lift_l ρ σ)
      A₀ B₀ ambient rows required) ∧ footprint = Footprint.sourceLift ρ required := by
  match bodies with
  | .nil => exact ⟨[], ⟨PiRows.nil⟩, rfl⟩
  | .cons guard body normal covered tail =>
    obtain ⟨fb, ⟨hb⟩, hfb⟩ := body.reflectSource ρ.cons hB (Locals.push newLocals)
    obtain ⟨ft, ⟨ht⟩, hft⟩ := tail.reflectSource ρ hA hB newLocals
    rw [source_cons] at hb
    rw [hA] at guard
    rw [hfb] at normal
    obtain ⟨outside, pack, houtside⟩ := normal.sourceLift_inv
    exact ⟨outside ++ ft, ⟨PiRows.cons guard.reflectSource hb pack covered ht⟩,
      by rw [houtside, hft, Footprint.sourceLift_append]⟩
termination_by sizeOf bodies
end

end Lean4Lean.AnchoredSource
