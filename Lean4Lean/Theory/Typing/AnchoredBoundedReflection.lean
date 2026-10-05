import Lean4Lean.Theory.Typing.AnchoredNativeDepthRenaming

/-! Source reflection preserves the exact native nesting budget. Native plans
are retained literally; only the surrounding source variable indices change. -/
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
theorem Obs.reflectSourceBounded
    {current : Name → Bool} {fuel : Nat}
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {Γ : List VExpr}
    {locals : List Nat} {σ : Subst} {expression e : VExpr}
    {demand : Profile n} {footprint : Footprint}
    (observation : Obs env U registry Γ locals σ expression demand footprint)
    (ρ : Lift) (he : expression = e.lift' ρ) (newLocals : List Nat)
    (bounded : observation.nativeDepth current ≤ fuel) :
    ∃ required, ∃ result : Obs env U registry Γ newLocals (Subst.lift_l ρ σ) e demand required,
      footprint = Footprint.sourceLift ρ required ∧ result.nativeDepth current ≤ fuel := by
  match observation with
  | .delta lookup nameEq registered seedWF seedLength levelsWF equivalent bodyClosed typeClosed typeCertificate typed body =>
    cases e <;> cases he
    exact ⟨[],  .delta lookup nameEq registered seedWF seedLength levelsWF equivalent bodyClosed typeClosed typeCertificate typed body, rfl, by simpa only [Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth] using bounded⟩
  | .native lookup noDefinition nameEq registered seedWF levelsWF equivalent signature typeClosed typeCertificate typed tree =>
    cases e <;> cases he
    exact ⟨[],  .native lookup noDefinition nameEq registered seedWF levelsWF equivalent signature typeClosed typeCertificate typed tree, rfl, by simpa only [Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth] using bounded⟩
  | .family lookup noDefinition noNative noQuotient seedWF seedLength levelsWF equivalent signature typeClosed typeCertificate typed tree =>
    cases e <;> cases he
    exact ⟨[],  .family lookup noDefinition noNative noQuotient seedWF seedLength levelsWF equivalent signature typeClosed typeCertificate typed tree, rfl, by simpa only [Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth] using bounded⟩
  | .constructor lookup noDefinition noNative noQuotient seedWF seedLength levelsWF equivalent signature typeClosed typeCertificate typed tree =>
    cases e <;> cases he
    exact ⟨[],  .constructor lookup noDefinition noNative noQuotient seedWF seedLength levelsWF equivalent signature typeClosed typeCertificate typed tree, rfl, by simpa only [Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth] using bounded⟩
  | .var _ _ i demand =>
    cases e <;> cases he
    exact ⟨_, Obs.var newLocals _ _ demand, rfl, by simpa only [Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth] using bounded⟩
  | .empty => exact ⟨[], Obs.empty, rfl, by simp only [Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth]; omega⟩
  | .sort relevant =>
    cases e <;> cases he
    exact ⟨[], Obs.sort relevant, rfl, by simp only [Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth]; omega⟩
  | .app fn arg arguments admitted =>
    have bounds := Nat.max_le.mp (show max _ _ ≤ fuel from by simpa only [Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth] using bounded)
    obtain ⟨f₀, a₀, rfl, hfn, harg⟩ := app_lift_inv he
    obtain ⟨ff, hf, hff, hfBound⟩ := fn.reflectSourceBounded ρ hfn newLocals bounds.1
    obtain ⟨fa, ha, hfa, haBound⟩ := arg.reflectSourceBounded ρ harg newLocals bounds.2
    refine ⟨ff ++ fa, Obs.app hf ha arguments ?_, ?_, ?_⟩
    · simpa only [harg, subst_lift'] using admitted
    · rw [hff, hfa, Footprint.sourceLift_append]
    · simpa only [Obs.nativeDepth] using Nat.max_le.mpr ⟨hfBound, haBound⟩
  | .lam domain guard body normal covered =>
    have bounds := Nat.max_le.mp (show max _ _ ≤ fuel from by simpa only [Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth] using bounded)
    obtain ⟨A₀, b₀, rfl, hdomain, hbody⟩ := lam_lift_inv he
    obtain ⟨fd, hd, hfd, hdBound⟩ := domain.reflectSourceBounded ρ hdomain newLocals bounds.1
    have bodyResult := body.reflectSourceBounded ρ.cons hbody (Locals.push newLocals) bounds.2
    rw [source_cons] at bodyResult
    obtain ⟨fb, hb, hfb, hbBound⟩ := bodyResult
    rw [hdomain] at guard
    rw [hfb] at normal
    obtain ⟨outside, pack, houtside⟩ := normal.sourceLift_inv
    refine ⟨fd ++ outside, Obs.lam hd guard.reflectSource hb pack covered, ?_, by simpa only [Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth] using Nat.max_le.mpr ⟨hdBound, hbBound⟩⟩
    rw [hfd, houtside, Footprint.sourceLift_append]
  | .pi domain guard bodies =>
    have bounds := Nat.max_le.mp (show max _ _ ≤ fuel from by simpa only [Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth] using bounded)
    obtain ⟨A₀, B₀, rfl, hdomain, hbody⟩ := pi_lift_inv he
    obtain ⟨fd, hd, hfd, hdBound⟩ := domain.reflectSourceBounded ρ hdomain newLocals bounds.1
    obtain ⟨fb, hb, hfb, hbBound⟩ := bodies.reflectSourceBounded ρ hdomain hbody newLocals bounds.2
    rw [hdomain, hbody] at guard
    exact ⟨fd ++ fb, Obs.pi hd guard.reflectSource hb,
      by rw [hfd, hfb, Footprint.sourceLift_append], by simpa only [Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth] using Nat.max_le.mpr ⟨hdBound, hbBound⟩⟩
  | .union left right =>
    have bounds := Nat.max_le.mp (show max _ _ ≤ fuel from by simpa only [Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth] using bounded)
    obtain ⟨fl, hl, hfl, hlBound⟩ := left.reflectSourceBounded ρ he newLocals bounds.1
    obtain ⟨fr, hr, hfr, hrBound⟩ := right.reflectSourceBounded ρ he newLocals bounds.2
    exact ⟨fl ++ fr, Obs.union hl hr, by rw [hfl, hfr, Footprint.sourceLift_append], by simpa only [Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth] using Nat.max_le.mpr ⟨hlBound, hrBound⟩⟩
  | .view source view =>
    obtain ⟨f, h, hf, hBound⟩ := source.reflectSourceBounded ρ he newLocals (by simpa only [Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth] using bounded)
    exact ⟨f, Obs.view h view, hf, by simpa only [Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth] using hBound⟩
  | .pad source =>
    obtain ⟨f, h, hf, hBound⟩ := source.reflectSourceBounded ρ he newLocals (by simpa only [Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth] using bounded)
    exact ⟨f, Obs.pad h, hf, by simpa only [Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth] using hBound⟩
  | .unpad source =>
    obtain ⟨f, h, hf, hBound⟩ := source.reflectSourceBounded ρ he newLocals (by simpa only [Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth] using bounded)
    exact ⟨f, Obs.unpad h, hf, by simpa only [Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth] using hBound⟩
  | .rowShift source =>
    obtain ⟨f, h, hf, hBound⟩ := source.reflectSourceBounded ρ he newLocals (by simpa only [Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth] using bounded)
    exact ⟨f, Obs.rowShift h, hf, by simpa only [Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth] using hBound⟩
termination_by sizeOf observation

theorem CodeCert.reflectSourceBounded
    {current : Name → Bool} {fuel : Nat}
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {Γ : List VExpr}
    {locals : List Nat} {σ : Subst} {expression e : VExpr}
    {demand : Profile n} {footprint : Footprint}
    (cert : CodeCert env U registry Γ locals σ expression demand footprint)
    (ρ : Lift) (he : expression = e.lift' ρ) (newLocals : List Nat)
    (bounded : cert.nativeDepth current ≤ fuel) :
    ∃ required, ∃ result : CodeCert env U registry Γ newLocals (Subst.lift_l ρ σ) e demand required,
      footprint = Footprint.sourceLift ρ required ∧ result.nativeDepth current ≤ fuel := by
  match cert with
  | .seed observation formed =>
    obtain ⟨f, h, hf, hBound⟩ := observation.reflectSourceBounded ρ he newLocals (by simpa only [Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth] using bounded)
    exact ⟨f, CodeCert.seed h formed, hf, by simpa only [Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth] using hBound⟩
  | .union left right =>
    have bounds := Nat.max_le.mp (show max _ _ ≤ fuel from by simpa only [Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth] using bounded)
    obtain ⟨fl, hl, hfl, hlBound⟩ := left.reflectSourceBounded ρ he newLocals bounds.1
    obtain ⟨fr, hr, hfr, hrBound⟩ := right.reflectSourceBounded ρ he newLocals bounds.2
    exact ⟨fl ++ fr, CodeCert.union hl hr, by rw [hfl, hfr, Footprint.sourceLift_append], by simpa only [Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth] using Nat.max_le.mpr ⟨hlBound, hrBound⟩⟩
  | .pad source =>
    obtain ⟨f, h, hf, hBound⟩ := source.reflectSourceBounded ρ he newLocals (by simpa only [Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth] using bounded)
    exact ⟨f, CodeCert.pad h, hf, by simpa only [Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth] using hBound⟩
  | .familyPad source =>
    obtain ⟨f, h, hf, hBound⟩ := source.reflectSourceBounded ρ he newLocals (by simpa only [Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth] using bounded)
    exact ⟨f, CodeCert.familyPad h, hf, by simpa only [Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth] using hBound⟩
  | .unpad source =>
    obtain ⟨f, h, hf, hBound⟩ := source.reflectSourceBounded ρ he newLocals (by simpa only [Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth] using bounded)
    exact ⟨f, CodeCert.unpad h, hf, by simpa only [Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth] using hBound⟩
  | .map view source =>
    obtain ⟨f, h, hf, hBound⟩ := source.reflectSourceBounded ρ he newLocals (by simpa only [Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth] using bounded)
    exact ⟨f, CodeCert.map view h, hf, by simpa only [Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth] using hBound⟩
  | .down source =>
    obtain ⟨f, h, hf, hBound⟩ := source.reflectSourceBounded ρ he newLocals (by simpa only [Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth] using bounded)
    exact ⟨f, CodeCert.down h, hf, by simpa only [Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth] using hBound⟩
  | .select source member =>
    obtain ⟨f, h, hf, hBound⟩ := source.reflectSourceBounded ρ he newLocals (by simpa only [Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth] using bounded)
    exact ⟨f, CodeCert.select h member, hf, by simpa only [Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth] using hBound⟩
  | .focusMinimal source minimal focusedBound =>
    obtain ⟨f, h, hf, hBound⟩ := source.reflectSourceBounded ρ he newLocals (by simpa only [Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth] using bounded)
    exact ⟨f, CodeCert.focusMinimal h minimal focusedBound, hf, by simpa only [Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth] using hBound⟩
termination_by sizeOf cert

theorem PiRows.reflectSourceBounded
    {current : Name → Bool} {fuel : Nat}
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {Γ : List VExpr}
    {locals : List Nat} {σ : Subst} {A B A₀ B₀ : VExpr} {ambient : Profile n}
    {rows : List (Key n × Profile n)} {footprint : Footprint}
    (bodies : PiRows env U registry Γ locals σ A B ambient rows footprint)
    (ρ : Lift) (hA : A = A₀.lift' ρ) (hB : B = B₀.lift' ρ.cons) (newLocals : List Nat)
    (bounded : bodies.nativeDepth current ≤ fuel) :
    ∃ required, ∃ result : PiRows env U registry Γ newLocals (Subst.lift_l ρ σ)
      A₀ B₀ ambient rows required, footprint = Footprint.sourceLift ρ required ∧
      result.nativeDepth current ≤ fuel := by
  match bodies with
  | .nil => exact ⟨[], PiRows.nil, rfl, by simp only [Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth]; omega⟩
  | .cons guard body normal covered tail =>
    have bounds := Nat.max_le.mp (show max _ _ ≤ fuel from by simpa only [Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth] using bounded)
    have bodyResult := body.reflectSourceBounded ρ.cons hB (Locals.push newLocals) bounds.1
    rw [source_cons] at bodyResult
    obtain ⟨fb, hb, hfb, hbBound⟩ := bodyResult
    obtain ⟨ft, ht, hft, htBound⟩ := tail.reflectSourceBounded ρ hA hB newLocals bounds.2
    rw [hA] at guard
    rw [hfb] at normal
    obtain ⟨outside, pack, houtside⟩ := normal.sourceLift_inv
    exact ⟨outside ++ ft, PiRows.cons guard.reflectSource hb pack covered ht,
      by rw [houtside, hft, Footprint.sourceLift_append], by simpa only [Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth] using Nat.max_le.mpr ⟨hbBound, htBound⟩⟩
termination_by sizeOf bodies
end

end Lean4Lean.AnchoredSource.Adapted
