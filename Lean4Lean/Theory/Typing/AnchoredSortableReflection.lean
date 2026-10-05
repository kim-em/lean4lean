import Lean4Lean.Theory.Typing.AnchoredSortableCert
import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceReflection

namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

private theorem source_cons (ρ : Lift) (σ : Subst) (anchor : VExpr) :
    Subst.lift_l ρ.cons (σ.cons anchor) = (Subst.lift_l ρ σ).cons anchor := by
  funext i
  cases i <;> rfl

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
theorem SortableCert.reflectSource
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {Γ : List VExpr}
    {locals : List Nat} {σ : Subst} {expression e : VExpr}
    {demand : Profile n} {footprint : Footprint}
    (cert : SortableCert env U registry Γ locals σ expression relevant demand footprint)
    (ρ : Lift) (he : expression = e.lift' ρ) (newLocals : List Nat) :
    ∃ required, Nonempty (SortableCert env U registry Γ newLocals (Subst.lift_l ρ σ) e relevant demand required) ∧
      footprint = Footprint.sourceLift ρ required := by
  match cert with
  | .ofCode source formed =>
    obtain ⟨f, ⟨h⟩, hf⟩ := source.reflectSource ρ he newLocals
    exact ⟨f, ⟨.ofCode h formed⟩, hf⟩
  | .pi domain guard bodies =>
    obtain ⟨A₀, B₀, rfl, hdomain, hbody⟩ := pi_lift_inv he
    obtain ⟨fd, ⟨hd⟩, hfd⟩ := domain.reflectSource ρ hdomain newLocals
    obtain ⟨fb, ⟨hb⟩, hfb⟩ := bodies.reflectSource ρ hdomain hbody newLocals
    rw [hdomain, hbody] at guard
    exact ⟨fd ++ fb, ⟨.pi hd guard.reflectSource hb⟩,
      by rw [hfd, hfb, Footprint.sourceLift_append]⟩
  | .observe observation formed =>
    obtain ⟨f, ⟨h⟩, hf⟩ := observation.reflectSource ρ he newLocals
    exact ⟨f, ⟨.observe h formed⟩, hf⟩
  | .seed observation formed =>
    obtain ⟨f, ⟨h⟩, hf⟩ := observation.reflectSource ρ he newLocals
    exact ⟨f, ⟨SortableCert.seed h formed⟩, hf⟩
  | .union left right =>
    obtain ⟨fl, ⟨hl⟩, hfl⟩ := left.reflectSource ρ he newLocals
    obtain ⟨fr, ⟨hr⟩, hfr⟩ := right.reflectSource ρ he newLocals
    exact ⟨fl ++ fr, ⟨SortableCert.union hl hr⟩, by rw [hfl, hfr, Footprint.sourceLift_append]⟩
  | .pad source =>
    obtain ⟨f, ⟨h⟩, hf⟩ := source.reflectSource ρ he newLocals
    exact ⟨f, ⟨SortableCert.pad h⟩, hf⟩
  | .familyPad source =>
    obtain ⟨f, ⟨h⟩, hf⟩ := source.reflectSource ρ he newLocals
    exact ⟨f, ⟨SortableCert.familyPad h⟩, hf⟩
  | .sortPad source =>
    obtain ⟨f, ⟨h⟩, hf⟩ := source.reflectSource ρ he newLocals
    exact ⟨f, ⟨SortableCert.sortPad h⟩, hf⟩
  | .unpad source =>
    obtain ⟨f, ⟨h⟩, hf⟩ := source.reflectSource ρ he newLocals
    exact ⟨f, ⟨SortableCert.unpad h⟩, hf⟩
  | .support action source =>
    obtain ⟨f, ⟨h⟩, hf⟩ := source.reflectSource ρ he newLocals
    exact ⟨f, ⟨SortableCert.support action h⟩, hf⟩
  | .map view source =>
    obtain ⟨f, ⟨h⟩, hf⟩ := source.reflectSource ρ he newLocals
    exact ⟨f, ⟨SortableCert.map view h⟩, hf⟩
  | .down source =>
    obtain ⟨f, ⟨h⟩, hf⟩ := source.reflectSource ρ he newLocals
    exact ⟨f, ⟨SortableCert.down h⟩, hf⟩
  | .select source member =>
    obtain ⟨f, ⟨h⟩, hf⟩ := source.reflectSource ρ he newLocals
    exact ⟨f, ⟨SortableCert.select h member⟩, hf⟩
  | .focusMinimal source minimal bound =>
    obtain ⟨f, ⟨h⟩, hf⟩ := source.reflectSource ρ he newLocals
    exact ⟨f, ⟨SortableCert.focusMinimal h minimal bound⟩, hf⟩
termination_by sizeOf cert

theorem SortableRows.reflectSource
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {Γ : List VExpr}
    {locals : List Nat} {σ : Subst} {A B A₀ B₀ : VExpr} {ambient : Profile n}
    {rows : List (Key n × Profile n)} {footprint : Footprint}
    (bodies : SortableRows env U registry Γ locals σ A B relevant ambient rows footprint)
    (ρ : Lift) (hA : A = A₀.lift' ρ) (hB : B = B₀.lift' ρ.cons) (newLocals : List Nat) :
    ∃ required, Nonempty (SortableRows env U registry Γ newLocals (Subst.lift_l ρ σ)
      A₀ B₀ relevant ambient rows required) ∧ footprint = Footprint.sourceLift ρ required := by
  match bodies with
  | .nil => exact ⟨[], ⟨SortableRows.nil⟩, rfl⟩
  | .cons guard body normal covered tail =>
    obtain ⟨fb, ⟨hb⟩, hfb⟩ := body.reflectSource ρ.cons hB (Locals.push newLocals)
    obtain ⟨ft, ⟨ht⟩, hft⟩ := tail.reflectSource ρ hA hB newLocals
    rw [source_cons] at hb
    rw [hA] at guard
    rw [hfb] at normal
    obtain ⟨outside, pack, houtside⟩ := normal.sourceLift_inv
    exact ⟨outside ++ ft, ⟨SortableRows.cons guard.reflectSource hb pack covered ht⟩,
      by rw [houtside, hft, Footprint.sourceLift_append]⟩
termination_by sizeOf bodies
theorem SortableObs.reflectSource
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {Γ : List VExpr}
    {locals : List Nat} {σ : Subst} {expression e : VExpr}
    {demand : Profile n} {footprint : Footprint}
    (observation : SortableObs env U registry Γ locals σ expression demand footprint)
    (ρ : Lift) (he : expression = e.lift' ρ) (newLocals : List Nat) :
    ∃ required, Nonempty (SortableObs env U registry Γ newLocals (Subst.lift_l ρ σ) e demand required) ∧
      footprint = Footprint.sourceLift ρ required := by
  match observation with
  | .family lookup noDefinition noNative noQuotient seedWF seedLength levelsWF equivalent signature typeClosed typeCertificate typed tree =>
    cases e <;> cases he
    exact ⟨[], ⟨.family lookup noDefinition noNative noQuotient seedWF seedLength levelsWF equivalent signature typeClosed typeCertificate typed tree⟩, rfl⟩
  | .legacy source =>
    obtain ⟨f, ⟨h⟩, hf⟩ := source.reflectSource ρ he newLocals
    exact ⟨f, ⟨.legacy h⟩, hf⟩
  | .code relevant source =>
    obtain ⟨f, ⟨h⟩, hf⟩ := source.reflectSource ρ he newLocals
    exact ⟨f, ⟨.code relevant h⟩, hf⟩
  | .action source action =>
    obtain ⟨f, ⟨h⟩, hf⟩ := source.reflectSource ρ he newLocals
    exact ⟨f, ⟨.action h action⟩, hf⟩
  | .app fn arg arguments admitted =>
    obtain ⟨f₀, a₀, rfl, hfn, harg⟩ := app_lift_inv he
    obtain ⟨ff, ⟨hf⟩, hff⟩ := fn.reflectSource ρ hfn newLocals
    obtain ⟨fa, ⟨ha⟩, hfa⟩ := arg.reflectSource ρ harg newLocals
    refine ⟨ff ++ fa, ⟨SortableObs.app hf ha arguments ?_⟩, ?_⟩
    · simpa only [harg, subst_lift'] using admitted
    · rw [hff, hfa, Footprint.sourceLift_append]
  | .lam domain guard body normal covered =>
    obtain ⟨A₀, b₀, rfl, hdomain, hbody⟩ := lam_lift_inv he
    obtain ⟨fd, ⟨hd⟩, hfd⟩ := domain.reflectSource ρ hdomain newLocals
    obtain ⟨fb, ⟨hb⟩, hfb⟩ := body.reflectSource ρ.cons hbody (Locals.push newLocals)
    rw [source_cons] at hb
    rw [hdomain] at guard
    rw [hfb] at normal
    obtain ⟨outside, pack, houtside⟩ := normal.sourceLift_inv
    refine ⟨fd ++ outside, ⟨SortableObs.lam hd guard.reflectSource hb pack covered⟩, ?_⟩
    rw [hfd, houtside, Footprint.sourceLift_append]
  | .union left right =>
    obtain ⟨fl, ⟨hl⟩, hfl⟩ := left.reflectSource ρ he newLocals
    obtain ⟨fr, ⟨hr⟩, hfr⟩ := right.reflectSource ρ he newLocals
    exact ⟨fl ++ fr, ⟨SortableObs.union hl hr⟩, by rw [hfl, hfr, Footprint.sourceLift_append]⟩
  | .view source view =>
    obtain ⟨f, ⟨h⟩, hf⟩ := source.reflectSource ρ he newLocals
    exact ⟨f, ⟨SortableObs.view h view⟩, hf⟩
  | .pad source =>
    obtain ⟨f, ⟨h⟩, hf⟩ := source.reflectSource ρ he newLocals
    exact ⟨f, ⟨SortableObs.pad h⟩, hf⟩
  | .unpad source =>
    obtain ⟨f, ⟨h⟩, hf⟩ := source.reflectSource ρ he newLocals
    exact ⟨f, ⟨SortableObs.unpad h⟩, hf⟩
  | .rowShift source =>
    obtain ⟨f, ⟨h⟩, hf⟩ := source.reflectSource ρ he newLocals
    exact ⟨f, ⟨SortableObs.rowShift h⟩, hf⟩
termination_by sizeOf observation

end

end Lean4Lean.AnchoredSource.Adapted
