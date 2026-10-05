import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceFactorization
import Lean4Lean.Theory.Typing.AnchoredBoundedReflection

/-! Inverse source substitution retains exact demands and the native-depth
budget. Every removed argument observation is retained in a bounded finite
ledger; no recursive call uses the size of a reconstructed observation. -/

namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false


/-- A concrete inverse-substitution ledger with a budget on each actual cut.
Forgetting budgets gives the existing `InstFootprint`, with identical cuts. -/
inductive BoundedInstFootprint (current : Name → Bool) (fuel : Nat)
    (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (Γ : List VExpr) (locals : List Nat) (σ : Subst) (argument : VExpr)
    (depth : Nat) : Footprint → Footprint → Type where
  | nil : BoundedInstFootprint current fuel env U registry Γ locals σ argument depth [] []
  | keep (index : Nat) (need : Need)
      (tail : BoundedInstFootprint current fuel env U registry Γ locals σ argument depth before after) :
      BoundedInstFootprint current fuel env U registry Γ locals σ argument depth
        ((index, need) :: before) ((insertIndex depth index, need) :: after)
  | cut {demand : Profile n} {argumentFootprint : Footprint}
      (observation : Obs env U registry Γ locals σ argument demand argumentFootprint)
      (bound : observation.nativeDepth current ≤ fuel)
      (tail : BoundedInstFootprint current fuel env U registry Γ locals σ argument depth before after) :
      BoundedInstFootprint current fuel env U registry Γ locals σ argument depth
        (shiftFootprint depth argumentFootprint ++ before) ((depth, ⟨n, demand⟩) :: after)

noncomputable def BoundedInstFootprint.forget
    (ledger : BoundedInstFootprint current fuel env U registry Γ locals σ argument depth before after) :
    InstFootprint env U registry Γ locals σ argument depth before after := by
  induction ledger with
  | nil => exact .nil
  | keep index need tail ih => exact .keep index need ih
  | cut observation bound tail ih => exact .cut observation ih

noncomputable def BoundedInstFootprint.append
    (first : BoundedInstFootprint current fuel env U registry Γ locals σ argument depth before₁ after₁)
    (second : BoundedInstFootprint current fuel env U registry Γ locals σ argument depth before₂ after₂) :
    BoundedInstFootprint current fuel env U registry Γ locals σ argument depth
      (before₁ ++ before₂) (after₁ ++ after₂) := by
  induction first with
  | nil => exact second
  | keep index need tail ih => exact .keep index need ih
  | cut observation bound tail ih =>
    simpa only [List.append_assoc, List.cons_append] using BoundedInstFootprint.cut observation bound ih

private theorem BinderPack.strip_external_bounded
    (pack : BinderPack n input (before.sourceLift (.skip .refl) ++ required) outside) :
    ∃ rest, BinderPack n input required rest ∧ outside = before ++ rest := by
  induction before generalizing outside with
  | nil => exact ⟨outside, pack, rfl⟩
  | cons entry tail ih =>
    obtain ⟨index, need⟩ := entry
    cases pack with
    | external _ _ rest =>
      obtain ⟨outside, normal, he⟩ := ih rest
      exact ⟨outside, normal, congrArg (List.cons (index, need)) he⟩

/-- Crossing a binder preserves its original consumed profile exactly. -/
theorem BoundedInstFootprint.underBinder
    (factor : BoundedInstFootprint current fuel env U registry Γ locals σ argument (depth + 1) before after)
    (pack : BinderPack n input before outside) :
    ∃ newOutside, BinderPack n input after newOutside ∧
      Nonempty (BoundedInstFootprint current fuel env U registry Γ locals σ argument depth outside newOutside) := by
  induction factor generalizing input outside with
  | nil => cases pack; exact ⟨[], .nil, ⟨.nil⟩⟩
  | keep index need tail ih =>
    cases index with
    | zero =>
      cases pack with
      | «local» _ bound rest =>
        obtain ⟨newOutside, normal, factor⟩ := ih rest
        exact ⟨newOutside, by simpa only [insertIndex_zero] using BinderPack.local need bound normal,
          factor⟩
    | succ index =>
      cases pack with
      | external _ _ rest =>
        obtain ⟨newOutside, normal, ⟨factor⟩⟩ := ih rest
        exact ⟨(insertIndex depth index, need) :: newOutside,
          by simpa only [insertIndex_succ] using BinderPack.external _ need normal,
          ⟨BoundedInstFootprint.keep index need factor⟩⟩
  | cut observation bound tail ih =>
    rw [shiftFootprint_succ] at pack
    obtain ⟨rest, normal, he⟩ := BinderPack.strip_external_bounded pack
    obtain ⟨newOutside, normal', ⟨factor⟩⟩ := ih normal
    subst outside
    exact ⟨(depth, _) :: newOutside, .external depth _ normal',
      ⟨BoundedInstFootprint.cut observation bound factor⟩⟩

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

private theorem Obs.cutArgumentBounded
    (observation : Obs env U registry Γ locals τ expression demand footprint)
    (he : expression = (VExpr.bvar depth).inst argument depth)
    (tail : Subst.lift_l (.skipN .refl depth) τ = σ)
    (baseLocals newLocals : List Nat)
    (bounded : observation.nativeDepth current ≤ fuel) :
    ∃ required, ∃ result : Obs env U registry Γ newLocals
      ((Subst.one argument).liftN depth |>.comp τ) (.bvar depth) demand required,
      Nonempty (BoundedInstFootprint current fuel env U registry Γ baseLocals σ argument depth footprint required) ∧
      result.nativeDepth current ≤ fuel := by
  have he' : expression = argument.lift' (.skipN .refl depth) := by
    rw [he]
    simp only [inst, instVar, Nat.lt_irrefl, ite_false, ite_true]
    exact (lift'_consN_skipN (k := 0)).symm
  have reflected := observation.reflectSourceBounded _ he' baseLocals bounded
  rw [tail] at reflected
  obtain ⟨required, original, hf, originalBound⟩ := reflected
  refine ⟨[(depth, ⟨_, demand⟩)],  .var newLocals _ depth demand, ?_, by simp only [Obs.nativeDepth]; omega⟩
  rw [hf, ← shiftFootprint_sourceLift]
  exact ⟨by simpa only [List.append_nil] using BoundedInstFootprint.cut original originalBound BoundedInstFootprint.nil⟩

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
theorem Obs.factorInstBounded
    {current : Name → Bool} {fuel : Nat}
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {Γ : List VExpr}
    {locals : List Nat} {τ : Subst} {expression : VExpr} {demand : Profile n} {footprint : Footprint}
    (observation : Obs env U registry Γ locals τ expression demand footprint)
    (original argument : VExpr) (depth : Nat) (he : expression = original.inst argument depth)
    (σ : Subst) (tail : Subst.lift_l (.skipN .refl depth) τ = σ)
    (baseLocals newLocals : List Nat)
    (bounded : observation.nativeDepth current ≤ fuel) :
    ∃ required, ∃ result : Obs env U registry Γ newLocals
      ((Subst.one argument).liftN depth |>.comp τ) original demand required,
      Nonempty (BoundedInstFootprint current fuel env U registry Γ baseLocals σ argument depth footprint required) ∧
      result.nativeDepth current ≤ fuel := by
  classical
  by_cases hcut : original = .bvar depth
  · subst original
    exact observation.cutArgumentBounded he tail baseLocals newLocals bounded
  match observation with
  | .delta lookup nameEq registered seedWF seedLength levelsWF equivalent bodyClosed typeClosed typeCertificate typed body =>
    obtain rfl := const_inst_inv he hcut
    exact ⟨[], .delta lookup nameEq registered seedWF seedLength levelsWF equivalent bodyClosed typeClosed typeCertificate typed body, ⟨.nil⟩, by simpa only [Obs.nativeDepth] using bounded⟩
  | .native lookup noDefinition nameEq registered seedWF levelsWF equivalent signature typeClosed typeCertificate typed tree =>
    obtain rfl := const_inst_inv he hcut
    exact ⟨[], .native lookup noDefinition nameEq registered seedWF levelsWF equivalent signature typeClosed typeCertificate typed tree, ⟨.nil⟩, by simpa only [Obs.nativeDepth] using bounded⟩
  | .family lookup noDefinition noNative noQuotient seedWF seedLength levelsWF equivalent signature typeClosed typeCertificate typed tree =>
    obtain rfl := const_inst_inv he hcut
    exact ⟨[], .family lookup noDefinition noNative noQuotient seedWF seedLength levelsWF equivalent signature typeClosed typeCertificate typed tree, ⟨.nil⟩, by simpa only [Obs.nativeDepth] using bounded⟩
  | .constructor lookup noDefinition noNative noQuotient seedWF seedLength levelsWF equivalent signature typeClosed typeCertificate typed tree =>
    obtain rfl := const_inst_inv he hcut
    exact ⟨[], .constructor lookup noDefinition noNative noQuotient seedWF seedLength levelsWF equivalent signature typeClosed typeCertificate typed tree, ⟨.nil⟩, by simpa only [Obs.nativeDepth] using bounded⟩
  | .var _ _ index demand =>
    cases original <;> simp only [inst, reduceCtorEq] at he
    rename_i i
    simp only [instVar] at he
    split at he
    · have hi := VExpr.bvar.inj he
      subst index
      refine ⟨[(i, ⟨_, demand⟩)], .var newLocals _ i demand, ?_, by simp only [Obs.nativeDepth]; omega⟩
      simpa only [insertIndex, if_pos ‹i < depth›] using
        (show Nonempty (BoundedInstFootprint current fuel env U registry Γ baseLocals σ argument depth
          [(i, ⟨_, demand⟩)] [(insertIndex depth i, ⟨_, demand⟩)]) from ⟨.keep i _ .nil⟩)
    · split at he
      · rename_i hi; exact (hcut (hi ▸ rfl)).elim
      · have hi := VExpr.bvar.inj he
        subst index
        have hindex : insertIndex depth (i - 1) = i := by
          unfold insertIndex
          split <;> omega
        refine ⟨[(i, ⟨_, demand⟩)], .var newLocals _ i demand, ?_, by simp only [Obs.nativeDepth]; omega⟩
        simpa only [hindex] using
          (show Nonempty (BoundedInstFootprint current fuel env U registry Γ baseLocals σ argument depth
            [(i - 1, ⟨_, demand⟩)] [(insertIndex depth (i - 1), ⟨_, demand⟩)]) from
            ⟨.keep (i - 1) _ .nil⟩)
  | .empty => exact ⟨[], .empty, ⟨.nil⟩, by simp only [Obs.nativeDepth]; omega⟩
  | .sort relevant =>
    obtain rfl := sort_inst_inv he hcut
    exact ⟨[], .sort relevant, ⟨.nil⟩, by simp only [Obs.nativeDepth]; omega⟩
  | .app fn arg arguments admitted =>
    have bounds := Nat.max_le.mp (show max _ _ ≤ fuel from by simpa only [Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth] using bounded)
    obtain ⟨f₀, a₀, rfl, hfn, harg⟩ := app_inst_inv he hcut
    obtain ⟨ff, hf, ⟨sf⟩, hfBound⟩ := fn.factorInstBounded f₀ argument depth hfn σ tail baseLocals newLocals bounds.1
    obtain ⟨fa, ha, ⟨sa⟩, haBound⟩ := arg.factorInstBounded a₀ argument depth harg σ tail baseLocals newLocals bounds.2
    refine ⟨ff ++ fa, .app hf ha arguments ?_, ⟨sf.append sa⟩, ?_⟩
    · simpa only [harg, instN_eq, subst_subst] using admitted
    · simpa only [Obs.nativeDepth] using Nat.max_le.mpr ⟨hfBound, haBound⟩
  | .lam domain guard body normal covered =>
    have bounds := Nat.max_le.mp (show max _ _ ≤ fuel from by simpa only [Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth] using bounded)
    obtain ⟨A₀, body₀, rfl, hA, hb⟩ := lam_inst_inv he hcut
    obtain ⟨fd, hd, ⟨sd⟩, hdBound⟩ := domain.factorInstBounded A₀ argument depth hA σ tail baseLocals newLocals bounds.1
    have bodyResult := body.factorInstBounded body₀ argument (depth + 1) hb σ
      (tail_cons depth τ σ _ tail) baseLocals (Locals.push newLocals) bounds.2
    rw [Subst.liftN, comp_cons] at bodyResult
    obtain ⟨fb, hb', ⟨sb⟩, hb'Bound⟩ := bodyResult
    obtain ⟨outside, pack, ⟨so⟩⟩ := sb.underBinder normal
    rw [hA] at guard
    exact ⟨fd ++ outside, .lam hd (LambdaGuard.factorInst guard) hb' pack covered, ⟨sd.append so⟩, by simpa only [Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth] using Nat.max_le.mpr ⟨hdBound, hb'Bound⟩⟩
  | .pi domain guard bodies =>
    have bounds := Nat.max_le.mp (show max _ _ ≤ fuel from by simpa only [Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth] using bounded)
    obtain ⟨A₀, B₀, rfl, hA, hB⟩ := pi_inst_inv he hcut
    obtain ⟨fd, hd, ⟨sd⟩, hdBound⟩ := domain.factorInstBounded A₀ argument depth hA σ tail baseLocals newLocals bounds.1
    obtain ⟨fb, hb, ⟨sb⟩, hbBound⟩ := bodies.factorInstBounded A₀ B₀ argument depth hA hB σ tail baseLocals newLocals bounds.2
    rw [hA, hB] at guard
    exact ⟨fd ++ fb, .pi hd (PiGuard.factorInst guard) hb, ⟨sd.append sb⟩, by simpa only [Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth] using Nat.max_le.mpr ⟨hdBound, hbBound⟩⟩
  | .union left right =>
    have bounds := Nat.max_le.mp (show max _ _ ≤ fuel from by simpa only [Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth] using bounded)
    obtain ⟨fl, hl, ⟨sl⟩, hlBound⟩ := left.factorInstBounded original argument depth he σ tail baseLocals newLocals bounds.1
    obtain ⟨fr, hr, ⟨sr⟩, hrBound⟩ := right.factorInstBounded original argument depth he σ tail baseLocals newLocals bounds.2
    exact ⟨fl ++ fr, .union hl hr, ⟨sl.append sr⟩, by simpa only [Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth] using Nat.max_le.mpr ⟨hlBound, hrBound⟩⟩
  | .view source view =>
    obtain ⟨f, h, ⟨s⟩, hBound⟩ := source.factorInstBounded original argument depth he σ tail baseLocals newLocals (by simpa only [Obs.nativeDepth, CodeCert.nativeDepth] using bounded)
    exact ⟨f, .view h view, ⟨s⟩, by simpa only [Obs.nativeDepth, CodeCert.nativeDepth] using hBound⟩
  | .pad source =>
    obtain ⟨f, h, ⟨s⟩, hBound⟩ := source.factorInstBounded original argument depth he σ tail baseLocals newLocals (by simpa only [Obs.nativeDepth, CodeCert.nativeDepth] using bounded)
    exact ⟨f, .pad h, ⟨s⟩, by simpa only [Obs.nativeDepth, CodeCert.nativeDepth] using hBound⟩
  | .unpad source =>
    obtain ⟨f, h, ⟨s⟩, hBound⟩ := source.factorInstBounded original argument depth he σ tail baseLocals newLocals (by simpa only [Obs.nativeDepth, CodeCert.nativeDepth] using bounded)
    exact ⟨f, .unpad h, ⟨s⟩, by simpa only [Obs.nativeDepth, CodeCert.nativeDepth] using hBound⟩
  | .rowShift source =>
    obtain ⟨f, h, ⟨s⟩, hBound⟩ := source.factorInstBounded original argument depth he σ tail baseLocals newLocals (by simpa only [Obs.nativeDepth, CodeCert.nativeDepth] using bounded)
    exact ⟨f, .rowShift h, ⟨s⟩, by simpa only [Obs.nativeDepth, CodeCert.nativeDepth] using hBound⟩
termination_by sizeOf observation

theorem CodeCert.factorInstBounded
    {current : Name → Bool} {fuel : Nat}
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {Γ : List VExpr}
    {locals : List Nat} {τ : Subst} {expression : VExpr} {demand : Profile n} {footprint : Footprint}
    (certificate : CodeCert env U registry Γ locals τ expression demand footprint)
    (original argument : VExpr) (depth : Nat) (he : expression = original.inst argument depth)
    (σ : Subst) (tail : Subst.lift_l (.skipN .refl depth) τ = σ)
    (baseLocals newLocals : List Nat)
    (bounded : certificate.nativeDepth current ≤ fuel) :
    ∃ required, ∃ result : CodeCert env U registry Γ newLocals
      ((Subst.one argument).liftN depth |>.comp τ) original demand required,
      Nonempty (BoundedInstFootprint current fuel env U registry Γ baseLocals σ argument depth footprint required) ∧
      result.nativeDepth current ≤ fuel := by
  match certificate with
  | .seed observation formed =>
    obtain ⟨f, h, s, hBound⟩ := observation.factorInstBounded original argument depth he σ tail baseLocals newLocals (by simpa only [Obs.nativeDepth, CodeCert.nativeDepth] using bounded)
    exact ⟨f, .seed h formed, s, by simpa only [Obs.nativeDepth, CodeCert.nativeDepth] using hBound⟩
  | .union left right =>
    have bounds := Nat.max_le.mp (show max _ _ ≤ fuel from by simpa only [Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth] using bounded)
    obtain ⟨fl, hl, ⟨sl⟩, hlBound⟩ := left.factorInstBounded original argument depth he σ tail baseLocals newLocals bounds.1
    obtain ⟨fr, hr, ⟨sr⟩, hrBound⟩ := right.factorInstBounded original argument depth he σ tail baseLocals newLocals bounds.2
    exact ⟨fl ++ fr, .union hl hr, ⟨sl.append sr⟩, by simpa only [Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth] using Nat.max_le.mpr ⟨hlBound, hrBound⟩⟩
  | .pad source =>
    obtain ⟨f, h, s, hBound⟩ := source.factorInstBounded original argument depth he σ tail baseLocals newLocals (by simpa only [Obs.nativeDepth, CodeCert.nativeDepth] using bounded)
    exact ⟨f, .pad h, s, by simpa only [Obs.nativeDepth, CodeCert.nativeDepth] using hBound⟩
  | .familyPad source =>
    obtain ⟨f, h, s, hBound⟩ := source.factorInstBounded original argument depth he σ tail baseLocals newLocals (by simpa only [Obs.nativeDepth, CodeCert.nativeDepth] using bounded)
    exact ⟨f, .familyPad h, s, by simpa only [Obs.nativeDepth, CodeCert.nativeDepth] using hBound⟩
  | .unpad source =>
    obtain ⟨f, h, s, hBound⟩ := source.factorInstBounded original argument depth he σ tail baseLocals newLocals (by simpa only [Obs.nativeDepth, CodeCert.nativeDepth] using bounded)
    exact ⟨f, .unpad h, s, by simpa only [Obs.nativeDepth, CodeCert.nativeDepth] using hBound⟩
  | .down source =>
    obtain ⟨f, h, s, hBound⟩ := source.factorInstBounded original argument depth he σ tail baseLocals newLocals (by simpa only [Obs.nativeDepth, CodeCert.nativeDepth] using bounded)
    exact ⟨f, .down h, s, by simpa only [Obs.nativeDepth, CodeCert.nativeDepth] using hBound⟩
  | .map view source =>
    obtain ⟨f, h, s, hBound⟩ := source.factorInstBounded original argument depth he σ tail baseLocals newLocals (by simpa only [Obs.nativeDepth, CodeCert.nativeDepth] using bounded)
    exact ⟨f, .map view h, s, by simpa only [Obs.nativeDepth, CodeCert.nativeDepth] using hBound⟩
  | .select source member =>
    obtain ⟨f, h, s, hBound⟩ := source.factorInstBounded original argument depth he σ tail baseLocals newLocals (by simpa only [Obs.nativeDepth, CodeCert.nativeDepth] using bounded)
    exact ⟨f, .select h member, s, by simpa only [Obs.nativeDepth, CodeCert.nativeDepth] using hBound⟩
  | .focusMinimal source minimal focusedBound =>
    obtain ⟨f, h, s, hBound⟩ := source.factorInstBounded original argument depth he σ tail baseLocals newLocals (by simpa only [Obs.nativeDepth, CodeCert.nativeDepth] using bounded)
    exact ⟨f, .focusMinimal h minimal focusedBound, s, by simpa only [Obs.nativeDepth, CodeCert.nativeDepth] using hBound⟩
termination_by sizeOf certificate

theorem PiRows.factorInstBounded
    {current : Name → Bool} {fuel : Nat}
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {Γ : List VExpr}
    {locals : List Nat} {τ : Subst} {A B : VExpr} {ambient : Profile n}
    {rows : List (Key n × Profile n)} {footprint : Footprint}
    (bodies : PiRows env U registry Γ locals τ A B ambient rows footprint)
    (A₀ B₀ argument : VExpr) (depth : Nat)
    (hA : A = A₀.inst argument depth) (hB : B = B₀.inst argument (depth + 1))
    (σ : Subst) (tail : Subst.lift_l (.skipN .refl depth) τ = σ)
    (baseLocals newLocals : List Nat)
    (bounded : bodies.nativeDepth current ≤ fuel) :
    ∃ required, ∃ result : PiRows env U registry Γ newLocals
      ((Subst.one argument).liftN depth |>.comp τ) A₀ B₀ ambient rows required,
      Nonempty (BoundedInstFootprint current fuel env U registry Γ baseLocals σ argument depth footprint required) ∧
      result.nativeDepth current ≤ fuel := by
  match bodies with
  | .nil => exact ⟨[], .nil, ⟨.nil⟩, by simp only [PiRows.nativeDepth]; omega⟩
  | .cons guard body normal covered rest =>
    have bounds := Nat.max_le.mp (show max _ _ ≤ fuel from by simpa only [Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth] using bounded)
    have bodyResult := body.factorInstBounded B₀ argument (depth + 1) hB σ
      (tail_cons depth τ σ _ tail) baseLocals (Locals.push newLocals) bounds.1
    rw [Subst.liftN, comp_cons] at bodyResult
    obtain ⟨fb, hb, ⟨sb⟩, hbBound⟩ := bodyResult
    obtain ⟨outside, pack, ⟨so⟩⟩ := sb.underBinder normal
    obtain ⟨fr, hr, ⟨sr⟩, hrBound⟩ := rest.factorInstBounded A₀ B₀ argument depth hA hB σ tail baseLocals newLocals bounds.2
    rw [hA] at guard
    exact ⟨outside ++ fr, .cons (LambdaGuard.factorInst guard) hb pack covered hr, ⟨so.append sr⟩, by simpa only [Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth] using Nat.max_le.mpr ⟨hbBound, hrBound⟩⟩
termination_by sizeOf bodies
end

end Lean4Lean.AnchoredSource.Adapted
