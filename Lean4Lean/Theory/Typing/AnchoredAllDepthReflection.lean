import Lean4Lean.Theory.Typing.AnchoredNativeDepthRenaming

/-! Source reflection preserves every declaration depth on one witness. Native plans
are retained literally; only the surrounding source variable indices change. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false

private theorem max_eq {a b c d : Nat} (ha : a = b) (hb : c = d) : max a c = max b d := by
  cases ha; cases hb; rfl

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
theorem Obs.reflectSource_allDepth
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {Γ : List VExpr}
    {locals : List Nat} {σ : Subst} {expression e : VExpr}
    {demand : Profile n} {footprint : Footprint}
    (observation : Obs env U registry Γ locals σ expression demand footprint)
    (ρ : Lift) (he : expression = e.lift' ρ) (newLocals : List Nat) :
    ∃ required, ∃ result : Obs env U registry Γ newLocals (Subst.lift_l ρ σ) e demand required,
      footprint = Footprint.sourceLift ρ required ∧ ∀ current, result.nativeDepth current = observation.nativeDepth current := by
  match observation with
  | .delta lookup nameEq registered seedWF seedLength levelsWF equivalent bodyClosed typeClosed typeCertificate typed body =>
    cases e <;> cases he
    exact ⟨[],  .delta lookup nameEq registered seedWF seedLength levelsWF equivalent bodyClosed typeClosed typeCertificate typed body, rfl, by intro current; simp only [Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth]⟩
  | .native lookup noDefinition nameEq registered seedWF levelsWF equivalent signature typeClosed typeCertificate typed tree =>
    cases e <;> cases he
    exact ⟨[],  .native lookup noDefinition nameEq registered seedWF levelsWF equivalent signature typeClosed typeCertificate typed tree, rfl, by intro current; simp only [Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth]⟩
  | .family lookup noDefinition noNative noQuotient seedWF seedLength levelsWF equivalent signature typeClosed typeCertificate typed tree =>
    cases e <;> cases he
    exact ⟨[],  .family lookup noDefinition noNative noQuotient seedWF seedLength levelsWF equivalent signature typeClosed typeCertificate typed tree, rfl, by intro current; simp only [Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth]⟩
  | .constructor lookup noDefinition noNative noQuotient seedWF seedLength levelsWF equivalent signature typeClosed typeCertificate typed tree =>
    cases e <;> cases he
    exact ⟨[],  .constructor lookup noDefinition noNative noQuotient seedWF seedLength levelsWF equivalent signature typeClosed typeCertificate typed tree, rfl, by intro current; simp only [Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth]⟩
  | .var _ _ i demand =>
    cases e <;> cases he
    exact ⟨_, Obs.var newLocals _ _ demand, rfl, by intro current; simp only [Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth]⟩
  | .empty => exact ⟨[], Obs.empty, rfl, by intro current; simp only [Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth]⟩
  | .sort relevant =>
    cases e <;> cases he
    exact ⟨[], Obs.sort relevant, rfl, by intro current; simp only [Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth]⟩
  | .app fn arg arguments admitted =>
    obtain ⟨f₀, a₀, rfl, hfn, harg⟩ := app_lift_inv he
    obtain ⟨ff, hf, hff, hfBound⟩ := fn.reflectSource_allDepth ρ hfn newLocals
    obtain ⟨fa, ha, hfa, haBound⟩ := arg.reflectSource_allDepth ρ harg newLocals
    refine ⟨ff ++ fa, Obs.app hf ha arguments ?_, ?_, ?_⟩
    · simpa only [harg, subst_lift'] using admitted
    · rw [hff, hfa, Footprint.sourceLift_append]
    · intro current; simpa only [Obs.nativeDepth] using max_eq (hfBound current) (haBound current)
  | .lam domain guard body normal covered =>
    obtain ⟨A₀, b₀, rfl, hdomain, hbody⟩ := lam_lift_inv he
    obtain ⟨fd, hd, hfd, hdBound⟩ := domain.reflectSource_allDepth ρ hdomain newLocals
    have bodyResult := body.reflectSource_allDepth ρ.cons hbody (Locals.push newLocals)
    rw [source_cons] at bodyResult
    obtain ⟨fb, hb, hfb, hbBound⟩ := bodyResult
    rw [hdomain] at guard
    rw [hfb] at normal
    obtain ⟨outside, pack, houtside⟩ := normal.sourceLift_inv
    refine ⟨fd ++ outside, Obs.lam hd guard.reflectSource hb pack covered, ?_, by intro current; simpa only [Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth] using max_eq (hdBound current) (hbBound current)⟩
    rw [hfd, houtside, Footprint.sourceLift_append]
  | .pi domain guard bodies =>
    obtain ⟨A₀, B₀, rfl, hdomain, hbody⟩ := pi_lift_inv he
    obtain ⟨fd, hd, hfd, hdBound⟩ := domain.reflectSource_allDepth ρ hdomain newLocals
    obtain ⟨fb, hb, hfb, hbBound⟩ := bodies.reflectSource_allDepth ρ hdomain hbody newLocals
    rw [hdomain, hbody] at guard
    exact ⟨fd ++ fb, Obs.pi hd guard.reflectSource hb,
      by rw [hfd, hfb, Footprint.sourceLift_append], by intro current; simpa only [Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth] using max_eq (hdBound current) (hbBound current)⟩
  | .union left right =>
    obtain ⟨fl, hl, hfl, hlBound⟩ := left.reflectSource_allDepth ρ he newLocals
    obtain ⟨fr, hr, hfr, hrBound⟩ := right.reflectSource_allDepth ρ he newLocals
    exact ⟨fl ++ fr, Obs.union hl hr, by rw [hfl, hfr, Footprint.sourceLift_append], by intro current; simpa only [Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth] using max_eq (hlBound current) (hrBound current)⟩
  | .view source view =>
    obtain ⟨f, h, hf, hBound⟩ := source.reflectSource_allDepth ρ he newLocals
    exact ⟨f, Obs.view h view, hf, by intro current; simpa only [Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth] using hBound current⟩
  | .pad source =>
    obtain ⟨f, h, hf, hBound⟩ := source.reflectSource_allDepth ρ he newLocals
    exact ⟨f, Obs.pad h, hf, by intro current; simpa only [Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth] using hBound current⟩
  | .unpad source =>
    obtain ⟨f, h, hf, hBound⟩ := source.reflectSource_allDepth ρ he newLocals
    exact ⟨f, Obs.unpad h, hf, by intro current; simpa only [Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth] using hBound current⟩
  | .rowShift source =>
    obtain ⟨f, h, hf, hBound⟩ := source.reflectSource_allDepth ρ he newLocals
    exact ⟨f, Obs.rowShift h, hf, by intro current; simpa only [Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth] using hBound current⟩
termination_by sizeOf observation

theorem CodeCert.reflectSource_allDepth
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {Γ : List VExpr}
    {locals : List Nat} {σ : Subst} {expression e : VExpr}
    {demand : Profile n} {footprint : Footprint}
    (cert : CodeCert env U registry Γ locals σ expression demand footprint)
    (ρ : Lift) (he : expression = e.lift' ρ) (newLocals : List Nat) :
    ∃ required, ∃ result : CodeCert env U registry Γ newLocals (Subst.lift_l ρ σ) e demand required,
      footprint = Footprint.sourceLift ρ required ∧ ∀ current, result.nativeDepth current = cert.nativeDepth current := by
  match cert with
  | .seed observation formed =>
    obtain ⟨f, h, hf, hBound⟩ := observation.reflectSource_allDepth ρ he newLocals
    exact ⟨f, CodeCert.seed h formed, hf, by intro current; simpa only [Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth] using hBound current⟩
  | .union left right =>
    obtain ⟨fl, hl, hfl, hlBound⟩ := left.reflectSource_allDepth ρ he newLocals
    obtain ⟨fr, hr, hfr, hrBound⟩ := right.reflectSource_allDepth ρ he newLocals
    exact ⟨fl ++ fr, CodeCert.union hl hr, by rw [hfl, hfr, Footprint.sourceLift_append], by intro current; simpa only [Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth] using max_eq (hlBound current) (hrBound current)⟩
  | .pad source =>
    obtain ⟨f, h, hf, hBound⟩ := source.reflectSource_allDepth ρ he newLocals
    exact ⟨f, CodeCert.pad h, hf, by intro current; simpa only [Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth] using hBound current⟩
  | .familyPad source =>
    obtain ⟨f, h, hf, hBound⟩ := source.reflectSource_allDepth ρ he newLocals
    exact ⟨f, CodeCert.familyPad h, hf, by intro current; simpa only [Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth] using hBound current⟩
  | .unpad source =>
    obtain ⟨f, h, hf, hBound⟩ := source.reflectSource_allDepth ρ he newLocals
    exact ⟨f, CodeCert.unpad h, hf, by intro current; simpa only [Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth] using hBound current⟩
  | .map view source =>
    obtain ⟨f, h, hf, hBound⟩ := source.reflectSource_allDepth ρ he newLocals
    exact ⟨f, CodeCert.map view h, hf, by intro current; simpa only [Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth] using hBound current⟩
  | .down source =>
    obtain ⟨f, h, hf, hBound⟩ := source.reflectSource_allDepth ρ he newLocals
    exact ⟨f, CodeCert.down h, hf, by intro current; simpa only [Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth] using hBound current⟩
  | .select source member =>
    obtain ⟨f, h, hf, hBound⟩ := source.reflectSource_allDepth ρ he newLocals
    exact ⟨f, CodeCert.select h member, hf, by intro current; simpa only [Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth] using hBound current⟩
  | .focusMinimal source minimal focusedBound =>
    obtain ⟨f, h, hf, hBound⟩ := source.reflectSource_allDepth ρ he newLocals
    exact ⟨f, CodeCert.focusMinimal h minimal focusedBound, hf, by intro current; simpa only [Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth] using hBound current⟩
termination_by sizeOf cert

theorem PiRows.reflectSource_allDepth
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {Γ : List VExpr}
    {locals : List Nat} {σ : Subst} {A B A₀ B₀ : VExpr} {ambient : Profile n}
    {rows : List (Key n × Profile n)} {footprint : Footprint}
    (bodies : PiRows env U registry Γ locals σ A B ambient rows footprint)
    (ρ : Lift) (hA : A = A₀.lift' ρ) (hB : B = B₀.lift' ρ.cons) (newLocals : List Nat) :
    ∃ required, ∃ result : PiRows env U registry Γ newLocals (Subst.lift_l ρ σ)
      A₀ B₀ ambient rows required, footprint = Footprint.sourceLift ρ required ∧
      ∀ current, result.nativeDepth current = bodies.nativeDepth current := by
  match bodies with
  | .nil => exact ⟨[], PiRows.nil, rfl, by intro current; simp only [Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth]⟩
  | .cons guard body normal covered tail =>
    have bodyResult := body.reflectSource_allDepth ρ.cons hB (Locals.push newLocals)
    rw [source_cons] at bodyResult
    obtain ⟨fb, hb, hfb, hbBound⟩ := bodyResult
    obtain ⟨ft, ht, hft, htBound⟩ := tail.reflectSource_allDepth ρ hA hB newLocals
    rw [hA] at guard
    rw [hfb] at normal
    obtain ⟨outside, pack, houtside⟩ := normal.sourceLift_inv
    exact ⟨outside ++ ft, PiRows.cons guard.reflectSource hb pack covered ht,
      by rw [houtside, hft, Footprint.sourceLift_append], by intro current; simpa only [Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth] using max_eq (hbBound current) (htBound current)⟩
termination_by sizeOf bodies
end

end Lean4Lean.AnchoredSource.Adapted
