import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceFactorFootprint

/-! Inverse source substitution retains exact demands. Removed argument
observations are finite children of the factorization certificate, and inner
binders retain the input profiles from their original observations. -/

namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

private theorem comp_cons (replacement realization : Subst) (anchor : VExpr) :
    replacement.lift.comp (realization.cons anchor) =
      (replacement.comp realization).cons anchor := by
  funext i
  cases i <;> simp [Subst.comp, Subst.lift, Subst.cons, lift_subst_cons]

private theorem tail_cons (depth : Nat) (τ σ : Subst) (anchor : VExpr)
    (tail : Subst.lift_l (.skipN .refl depth) τ = σ) :
    Subst.lift_l (.skipN .refl (depth + 1)) (τ.cons anchor) = σ := by
  rw [← tail]
  funext i
  simp [Subst.lift_l, Lift.liftVar_skipN, Lift.liftVar, Subst.cons, Nat.add_comm]

private theorem LambdaGuard.factorInst
    (guard : LambdaGuard env U registry Γ τ (annotation.inst argument depth) key support) :
    LambdaGuard env U registry Γ ((Subst.one argument).liftN depth |>.comp τ)
      annotation key support := by
  refine ⟨guard.inputTyped, guard.formed, ?_, ?_, guard.anchor⟩
  · simpa only [instN_eq, subst_subst] using guard.path
  · simpa only [instN_eq, subst_subst] using guard.domains

private theorem PiGuard.factorInst
    (guard : PiGuard env U Γ τ (A.inst argument depth) (B.inst argument (depth + 1)) C D) :
    PiGuard env U Γ ((Subst.one argument).liftN depth |>.comp τ) A B C D := by
  constructor
  · simpa only [instN_eq, subst_subst] using guard.domainPath
  · simpa only [instN_eq, subst_subst, Subst.liftN, Subst.comp_lift] using guard.bodyPath

private theorem Obs.cutArgument
    (observation : Obs env U registry Γ locals τ expression demand footprint)
    (he : expression = (VExpr.bvar depth).inst argument depth)
    (tail : Subst.lift_l (.skipN .refl depth) τ = σ)
    (baseLocals newLocals : List Nat) :
    ∃ required, Nonempty (Obs env U registry Γ newLocals
      ((Subst.one argument).liftN depth |>.comp τ) (.bvar depth) demand required) ∧
      Nonempty (InstFootprint env U registry Γ baseLocals σ argument depth footprint required) := by
  have he' : expression = argument.lift' (.skipN .refl depth) := by
    rw [he]
    simp only [inst, instVar, Nat.lt_irrefl, ite_false, ite_true]
    exact (lift'_consN_skipN (k := 0)).symm
  obtain ⟨required, ⟨original⟩, hf⟩ := observation.reflectSource _ he' baseLocals
  rw [tail] at original
  refine ⟨[(depth, ⟨_, demand⟩)], ⟨.var newLocals _ depth demand⟩, ?_⟩
  rw [hf, ← shiftFootprint_sourceLift]
  exact ⟨by simpa only [List.append_nil] using InstFootprint.cut original InstFootprint.nil⟩

private theorem const_inst_inv
    {expression argument : VExpr} {depth : Nat}
    (he : VExpr.const name levels = expression.inst argument depth)
    (hne : expression ≠ .bvar depth) : expression = .const name levels := by
  cases expression <;> simp only [inst, reduceCtorEq, const.injEq] at he
  · simp only [instVar] at he
    split at he <;> try contradiction
    split at he <;> try contradiction
    rename_i h
    exact (hne (h ▸ rfl)).elim
  · rcases he with ⟨rfl, rfl⟩
    rfl

private theorem sort_inst_inv
    {expression argument : VExpr} {depth : Nat}
    (he : VExpr.sort level = expression.inst argument depth)
    (hne : expression ≠ .bvar depth) : expression = .sort level := by
  cases expression <;> simp only [inst, reduceCtorEq, sort.injEq] at he
  · simp only [instVar] at he
    split at he <;> try contradiction
    split at he <;> try contradiction
    rename_i h
    exact (hne (h ▸ rfl)).elim
  · exact he.symm ▸ rfl

private theorem app_inst_inv
    {expression argument : VExpr} {depth : Nat}
    (he : VExpr.app f a = expression.inst argument depth)
    (hne : expression ≠ .bvar depth) :
    ∃ f₀ a₀, expression = .app f₀ a₀ ∧ f = f₀.inst argument depth ∧ a = a₀.inst argument depth := by
  cases expression <;> simp only [inst, reduceCtorEq, app.injEq] at he
  · simp only [instVar] at he
    split at he <;> try contradiction
    split at he <;> try contradiction
    rename_i h
    exact (hne (h ▸ rfl)).elim
  · exact ⟨_, _, rfl, he⟩

private theorem lam_inst_inv
    {expression argument : VExpr} {depth : Nat}
    (he : VExpr.lam A body = expression.inst argument depth)
    (hne : expression ≠ .bvar depth) :
    ∃ A₀ body₀, expression = .lam A₀ body₀ ∧ A = A₀.inst argument depth ∧
      body = body₀.inst argument (depth + 1) := by
  cases expression <;> simp only [inst, reduceCtorEq, lam.injEq] at he
  · simp only [instVar] at he
    split at he <;> try contradiction
    split at he <;> try contradiction
    rename_i h
    exact (hne (h ▸ rfl)).elim
  · exact ⟨_, _, rfl, he⟩

private theorem pi_inst_inv
    {expression argument : VExpr} {depth : Nat}
    (he : VExpr.forallE A B = expression.inst argument depth)
    (hne : expression ≠ .bvar depth) :
    ∃ A₀ B₀, expression = .forallE A₀ B₀ ∧ A = A₀.inst argument depth ∧
      B = B₀.inst argument (depth + 1) := by
  cases expression <;> simp only [inst, reduceCtorEq, forallE.injEq] at he
  · simp only [instVar] at he
    split at he <;> try contradiction
    split at he <;> try contradiction
    rename_i h
    exact (hne (h ▸ rfl)).elim
  · exact ⟨_, _, rfl, he⟩

mutual
theorem Obs.factorInst
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {Γ : List VExpr}
    {locals : List Nat} {τ : Subst} {expression : VExpr} {demand : Profile n} {footprint : Footprint}
    (observation : Obs env U registry Γ locals τ expression demand footprint)
    (original argument : VExpr) (depth : Nat) (he : expression = original.inst argument depth)
    (σ : Subst) (tail : Subst.lift_l (.skipN .refl depth) τ = σ)
    (baseLocals newLocals : List Nat) :
    ∃ required, Nonempty (Obs env U registry Γ newLocals
      ((Subst.one argument).liftN depth |>.comp τ) original demand required) ∧
      Nonempty (InstFootprint env U registry Γ baseLocals σ argument depth footprint required) := by
  classical
  by_cases hcut : original = .bvar depth
  · subst original
    exact observation.cutArgument he tail baseLocals newLocals
  match observation with
  | .delta lookup nameEq registered seedWF seedLength levelsWF equivalent bodyClosed typeClosed typeCertificate typed body =>
    obtain rfl := const_inst_inv he hcut
    exact ⟨[], ⟨.delta lookup nameEq registered seedWF seedLength levelsWF equivalent bodyClosed typeClosed typeCertificate typed body⟩, ⟨.nil⟩⟩
  | .native lookup noDefinition nameEq registered seedWF levelsWF equivalent signature typeClosed typeCertificate typed tree =>
    obtain rfl := const_inst_inv he hcut
    exact ⟨[], ⟨.native lookup noDefinition nameEq registered seedWF levelsWF equivalent signature typeClosed typeCertificate typed tree⟩, ⟨.nil⟩⟩
  | .family lookup noDefinition noNative noQuotient seedWF seedLength levelsWF equivalent signature typeClosed typeCertificate typed tree =>
    obtain rfl := const_inst_inv he hcut
    exact ⟨[], ⟨.family lookup noDefinition noNative noQuotient seedWF seedLength levelsWF equivalent signature typeClosed typeCertificate typed tree⟩, ⟨.nil⟩⟩
  | .constructor lookup noDefinition noNative noQuotient seedWF seedLength levelsWF equivalent signature typeClosed typeCertificate typed tree =>
    obtain rfl := const_inst_inv he hcut
    exact ⟨[], ⟨.constructor lookup noDefinition noNative noQuotient seedWF seedLength levelsWF equivalent signature typeClosed typeCertificate typed tree⟩, ⟨.nil⟩⟩
  | .var _ _ index demand =>
    cases original <;> simp only [inst, reduceCtorEq] at he
    rename_i i
    simp only [instVar] at he
    split at he
    · have hi := VExpr.bvar.inj he
      subst index
      refine ⟨[(i, ⟨_, demand⟩)], ⟨.var newLocals _ i demand⟩, ?_⟩
      simpa only [insertIndex, if_pos ‹i < depth›] using
        (show Nonempty (InstFootprint env U registry Γ baseLocals σ argument depth
          [(i, ⟨_, demand⟩)] [(insertIndex depth i, ⟨_, demand⟩)]) from ⟨.keep i _ .nil⟩)
    · split at he
      · rename_i hi; exact (hcut (hi ▸ rfl)).elim
      · have hi := VExpr.bvar.inj he
        subst index
        have hindex : insertIndex depth (i - 1) = i := by
          unfold insertIndex
          split <;> omega
        refine ⟨[(i, ⟨_, demand⟩)], ⟨.var newLocals _ i demand⟩, ?_⟩
        simpa only [hindex] using
          (show Nonempty (InstFootprint env U registry Γ baseLocals σ argument depth
            [(i - 1, ⟨_, demand⟩)] [(insertIndex depth (i - 1), ⟨_, demand⟩)]) from
            ⟨.keep (i - 1) _ .nil⟩)
  | .empty => exact ⟨[], ⟨.empty⟩, ⟨.nil⟩⟩
  | .sort relevant =>
    obtain rfl := sort_inst_inv he hcut
    exact ⟨[], ⟨.sort relevant⟩, ⟨.nil⟩⟩
  | .app fn arg arguments admitted =>
    obtain ⟨f₀, a₀, rfl, hfn, harg⟩ := app_inst_inv he hcut
    obtain ⟨ff, ⟨hf⟩, ⟨sf⟩⟩ := fn.factorInst f₀ argument depth hfn σ tail baseLocals newLocals
    obtain ⟨fa, ⟨ha⟩, ⟨sa⟩⟩ := arg.factorInst a₀ argument depth harg σ tail baseLocals newLocals
    refine ⟨ff ++ fa, ⟨.app hf ha arguments ?_⟩, ⟨sf.append sa⟩⟩
    simpa only [harg, instN_eq, subst_subst] using admitted
  | .lam domain guard body normal covered =>
    obtain ⟨A₀, body₀, rfl, hA, hb⟩ := lam_inst_inv he hcut
    obtain ⟨fd, ⟨hd⟩, ⟨sd⟩⟩ := domain.factorInst A₀ argument depth hA σ tail baseLocals newLocals
    obtain ⟨fb, ⟨hb'⟩, ⟨sb⟩⟩ := body.factorInst body₀ argument (depth + 1) hb σ
      (tail_cons depth τ σ _ tail) baseLocals (Locals.push newLocals)
    rw [Subst.liftN, comp_cons] at hb'
    obtain ⟨outside, pack, ⟨so⟩⟩ := sb.underBinder normal
    rw [hA] at guard
    exact ⟨fd ++ outside, ⟨.lam hd (LambdaGuard.factorInst guard) hb' pack covered⟩, ⟨sd.append so⟩⟩
  | .pi domain guard bodies =>
    obtain ⟨A₀, B₀, rfl, hA, hB⟩ := pi_inst_inv he hcut
    obtain ⟨fd, ⟨hd⟩, ⟨sd⟩⟩ := domain.factorInst A₀ argument depth hA σ tail baseLocals newLocals
    obtain ⟨fb, ⟨hb⟩, ⟨sb⟩⟩ := bodies.factorInst A₀ B₀ argument depth hA hB σ tail baseLocals newLocals
    rw [hA, hB] at guard
    exact ⟨fd ++ fb, ⟨.pi hd (PiGuard.factorInst guard) hb⟩, ⟨sd.append sb⟩⟩
  | .union left right =>
    obtain ⟨fl, ⟨hl⟩, ⟨sl⟩⟩ := left.factorInst original argument depth he σ tail baseLocals newLocals
    obtain ⟨fr, ⟨hr⟩, ⟨sr⟩⟩ := right.factorInst original argument depth he σ tail baseLocals newLocals
    exact ⟨fl ++ fr, ⟨.union hl hr⟩, ⟨sl.append sr⟩⟩
  | .view source view =>
    obtain ⟨f, ⟨h⟩, ⟨s⟩⟩ := source.factorInst original argument depth he σ tail baseLocals newLocals
    exact ⟨f, ⟨.view h view⟩, ⟨s⟩⟩
  | .pad source =>
    obtain ⟨f, ⟨h⟩, ⟨s⟩⟩ := source.factorInst original argument depth he σ tail baseLocals newLocals
    exact ⟨f, ⟨.pad h⟩, ⟨s⟩⟩
  | .unpad source =>
    obtain ⟨f, ⟨h⟩, ⟨s⟩⟩ := source.factorInst original argument depth he σ tail baseLocals newLocals
    exact ⟨f, ⟨.unpad h⟩, ⟨s⟩⟩
  | .rowShift source =>
    obtain ⟨f, ⟨h⟩, ⟨s⟩⟩ := source.factorInst original argument depth he σ tail baseLocals newLocals
    exact ⟨f, ⟨.rowShift h⟩, ⟨s⟩⟩
termination_by sizeOf observation

theorem CodeCert.factorInst
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {Γ : List VExpr}
    {locals : List Nat} {τ : Subst} {expression : VExpr} {demand : Profile n} {footprint : Footprint}
    (certificate : CodeCert env U registry Γ locals τ expression demand footprint)
    (original argument : VExpr) (depth : Nat) (he : expression = original.inst argument depth)
    (σ : Subst) (tail : Subst.lift_l (.skipN .refl depth) τ = σ)
    (baseLocals newLocals : List Nat) :
    ∃ required, Nonempty (CodeCert env U registry Γ newLocals
      ((Subst.one argument).liftN depth |>.comp τ) original demand required) ∧
      Nonempty (InstFootprint env U registry Γ baseLocals σ argument depth footprint required) := by
  match certificate with
  | .seed observation formed =>
    obtain ⟨f, ⟨h⟩, s⟩ := observation.factorInst original argument depth he σ tail baseLocals newLocals
    exact ⟨f, ⟨.seed h formed⟩, s⟩
  | .union left right =>
    obtain ⟨fl, ⟨hl⟩, ⟨sl⟩⟩ := left.factorInst original argument depth he σ tail baseLocals newLocals
    obtain ⟨fr, ⟨hr⟩, ⟨sr⟩⟩ := right.factorInst original argument depth he σ tail baseLocals newLocals
    exact ⟨fl ++ fr, ⟨.union hl hr⟩, ⟨sl.append sr⟩⟩
  | .pad source =>
    obtain ⟨f, ⟨h⟩, s⟩ := source.factorInst original argument depth he σ tail baseLocals newLocals
    exact ⟨f, ⟨.pad h⟩, s⟩
  | .familyPad source =>
    obtain ⟨f, ⟨h⟩, s⟩ := source.factorInst original argument depth he σ tail baseLocals newLocals
    exact ⟨f, ⟨.familyPad h⟩, s⟩
  | .unpad source =>
    obtain ⟨f, ⟨h⟩, s⟩ := source.factorInst original argument depth he σ tail baseLocals newLocals
    exact ⟨f, ⟨.unpad h⟩, s⟩
  | .down source =>
    obtain ⟨f, ⟨h⟩, s⟩ := source.factorInst original argument depth he σ tail baseLocals newLocals
    exact ⟨f, ⟨.down h⟩, s⟩
  | .map view source =>
    obtain ⟨f, ⟨h⟩, s⟩ := source.factorInst original argument depth he σ tail baseLocals newLocals
    exact ⟨f, ⟨.map view h⟩, s⟩
  | .select source member =>
    obtain ⟨f, ⟨h⟩, s⟩ := source.factorInst original argument depth he σ tail baseLocals newLocals
    exact ⟨f, ⟨.select h member⟩, s⟩
  | .focusMinimal source minimal bound =>
    obtain ⟨f, ⟨h⟩, s⟩ := source.factorInst original argument depth he σ tail baseLocals newLocals
    exact ⟨f, ⟨.focusMinimal h minimal bound⟩, s⟩
termination_by sizeOf certificate

theorem PiRows.factorInst
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {Γ : List VExpr}
    {locals : List Nat} {τ : Subst} {A B : VExpr} {ambient : Profile n}
    {rows : List (Key n × Profile n)} {footprint : Footprint}
    (bodies : PiRows env U registry Γ locals τ A B ambient rows footprint)
    (A₀ B₀ argument : VExpr) (depth : Nat)
    (hA : A = A₀.inst argument depth) (hB : B = B₀.inst argument (depth + 1))
    (σ : Subst) (tail : Subst.lift_l (.skipN .refl depth) τ = σ)
    (baseLocals newLocals : List Nat) :
    ∃ required, Nonempty (PiRows env U registry Γ newLocals
      ((Subst.one argument).liftN depth |>.comp τ) A₀ B₀ ambient rows required) ∧
      Nonempty (InstFootprint env U registry Γ baseLocals σ argument depth footprint required) := by
  match bodies with
  | .nil => exact ⟨[], ⟨.nil⟩, ⟨.nil⟩⟩
  | .cons guard body normal covered rest =>
    obtain ⟨fb, ⟨hb⟩, ⟨sb⟩⟩ := body.factorInst B₀ argument (depth + 1) hB σ
      (tail_cons depth τ σ _ tail) baseLocals (Locals.push newLocals)
    rw [Subst.liftN, comp_cons] at hb
    obtain ⟨outside, pack, ⟨so⟩⟩ := sb.underBinder normal
    obtain ⟨fr, ⟨hr⟩, ⟨sr⟩⟩ := rest.factorInst A₀ B₀ argument depth hA hB σ tail baseLocals newLocals
    rw [hA] at guard
    exact ⟨outside ++ fr, ⟨.cons (LambdaGuard.factorInst guard) hb pack covered hr⟩, ⟨so.append sr⟩⟩
termination_by sizeOf bodies
end

end Lean4Lean.AnchoredSource.Adapted
