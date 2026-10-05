import Lean4Lean.Theory.Typing.AnchoredOriginalSortableDepthFootprint
import Lean4Lean.Theory.Typing.AnchoredSortableDepthReflection

/-! Inverse substitution at actual original endpoints preserves every
caller declaration-depth control on both the residual and retained cuts. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalFactorCut
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure OriginalEndpointFactor
open private const_inst_inv sort_inst_inv app_inst_inv lam_inst_inv pi_inst_inv comp_cons tail_cons
  LambdaGuard.factorInstLocated PiGuard.factorInstLocated
  from Lean4Lean.Theory.Typing.AnchoredOriginalFactorTraversal
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false

set_option hygiene false in
local macro "depth_bound" : tactic => `(tactic| (
  intro current
  try have := sDepth current
  try have := slDepth current
  try have := srDepth current
  try have := sdDepth current
  try have := sbDepth current
  try have := sfDepth current
  try have := saDepth current
  try have := soDepth current
  simp only [Obs.nativeDepth, CodeCert.nativeDepth, PiRows.nativeDepth,
    BoundedLocatedFootprintAt.nativeDepth_append, BoundedLocatedFootprintAt.nativeDepth_weaken,
    BoundedLocatedFootprintAt.nativeDepth_rec,
    BoundedLocatedFootprintAt.nativeDepth, Obs.nativeDepth_rec, CodeCert.nativeDepth_rec] at *
  omega))

private theorem Obs.cutArgument_allDepth
    (observation : Obs env U registry Γ locals τ expression demand footprint)
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    (typing : EndpointState sourceEnv U source expression assigned)
    (location : Located root typing)
    (innerPrefix : List VExpr) (prefixSplit : location.binderPrefix = innerPrefix ++ boundary)
    {baseDepth : Nat} (depthEq : depth = baseDepth + innerPrefix.length)
    (he : expression = (VExpr.bvar depth).inst argument depth)
    (tail : Subst.lift_l (.skipN .refl depth) τ = σ)
    (baseLocals newLocals : List Nat) :
    ∃ required, ∃ result : Obs env U registry Γ newLocals
      ((Subst.one argument).liftN depth |>.comp τ) (.bvar depth) demand required,
      ∃ trace : BoundedLocatedFootprintAt (env := env) root boundary registry Γ baseLocals σ argument baseDepth depth
        (fun initial => (Closure.close typing.origin (location.environment initial)).cost) footprint required,
      ∀ current, max (result.nativeDepth current) (trace.nativeDepth current) ≤ observation.nativeDepth current := by
  have he' : expression = argument.lift' (.skipN .refl depth) := by
    rw [he]
    simp only [inst, instVar, Nat.lt_irrefl, ite_false, ite_true]
    exact (lift'_consN_skipN (k := 0)).symm
  let cut : OriginalEndpointFactor.CutOriginAt root boundary argument baseDepth :=
    ⟨source, expression, assigned, typing, location, depth, he', innerPrefix, prefixSplit, depthEq⟩
  have reflected := observation.reflectSource_allDepth _ he' baseLocals
  rw [tail] at reflected
  obtain ⟨required, original, hf, originalDepth⟩ := reflected
  let whole : WholeCutQuery (env := env) cut registry Γ σ demand required :=
    ⟨locals, τ, footprint, observation, tail, hf⟩
  refine ⟨[(depth, ⟨_, demand⟩)], .var newLocals _ depth demand, ?_⟩
  let ledger := BoundedLocatedFootprintAt.cut (depth := depth) cut original whole
    (fun _ => Nat.le_refl _) BoundedLocatedFootprintAt.nil
  have exactFootprint : footprint = shiftFootprint depth required ++ [] := by
    rw [hf, ← shiftFootprint_sourceLift, List.append_nil]
  cases exactFootprint
  exact ⟨ledger, by
    intro current
    simp only [ledger, Obs.nativeDepth, BoundedLocatedFootprintAt.nativeDepth,
      Nat.max_zero, Nat.zero_max, originalDepth]
    exact Nat.le_refl _⟩


mutual
theorem Obs.factorInstLocatedRelative_allDepth
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {Γ : List VExpr}
    {locals : List Nat} {τ : Subst} {expression : VExpr} {demand : Profile n} {footprint : Footprint}
    (observation : Obs env U registry Γ locals τ expression demand footprint)
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    (typing : EndpointState sourceEnv U source expression assigned)
    (location : Located root typing)
    (innerPrefix : List VExpr) (prefixSplit : location.binderPrefix = innerPrefix ++ boundary)
    (original argument : VExpr) (depth : Nat)
    {baseDepth : Nat} (depthEq : depth = baseDepth + innerPrefix.length)
    (he : expression = original.inst argument depth)
    (σ : Subst) (tail : Subst.lift_l (.skipN .refl depth) τ = σ)
    (baseLocals newLocals : List Nat) :
    ∃ required, ∃ result : Obs env U registry Γ newLocals
      ((Subst.one argument).liftN depth |>.comp τ) original demand required,
      ∃ trace : BoundedLocatedFootprintAt (env := env) root boundary registry Γ baseLocals σ argument baseDepth depth
        (fun initial => (Closure.close typing.origin (location.environment initial)).cost) footprint required,
      ∀ current, max (result.nativeDepth current) (trace.nativeDepth current) ≤ observation.nativeDepth current := by
  classical
  by_cases hcut : original = .bvar depth
  · subst original
    exact Obs.cutArgument_allDepth observation typing location innerPrefix prefixSplit depthEq he tail baseLocals newLocals
  match observation, typing, location with
  | .delta lookup nameEq registered seedWF seedLength levelsWF equivalent bodyClosed typeClosed typeCertificate typed body, typing, location =>
    obtain rfl := const_inst_inv he hcut
    exact ⟨[], .delta lookup nameEq registered seedWF seedLength levelsWF equivalent bodyClosed typeClosed typeCertificate typed body, .nil, by depth_bound⟩
  | .native lookup noDefinition nameEq registered seedWF levelsWF equivalent signature typeClosed typeCertificate typed tree, typing, location =>
    obtain rfl := const_inst_inv he hcut
    exact ⟨[], .native lookup noDefinition nameEq registered seedWF levelsWF equivalent signature typeClosed typeCertificate typed tree, .nil, by depth_bound⟩
  | .family lookup noDefinition noNative noQuotient seedWF seedLength levelsWF equivalent signature typeClosed typeCertificate typed tree, typing, location =>
    obtain rfl := const_inst_inv he hcut
    exact ⟨[], .family lookup noDefinition noNative noQuotient seedWF seedLength levelsWF equivalent signature typeClosed typeCertificate typed tree, .nil, by depth_bound⟩
  | .constructor lookup noDefinition noNative noQuotient seedWF seedLength levelsWF equivalent signature typeClosed typeCertificate typed tree, typing, location =>
    obtain rfl := const_inst_inv he hcut
    exact ⟨[], .constructor lookup noDefinition noNative noQuotient seedWF seedLength levelsWF equivalent signature typeClosed typeCertificate typed tree, .nil, by depth_bound⟩
  | .var _ _ index demand, typing, location =>
    cases original <;> simp only [inst, reduceCtorEq] at he
    rename_i i
    simp only [instVar] at he
    split at he
    · have hi := VExpr.bvar.inj he
      subst index
      have hi : insertIndex depth i = i := by simp only [insertIndex, if_pos ‹i < depth›]
      refine ⟨[(i, ⟨_, demand⟩)], .var newLocals _ i demand, ?_⟩
      let trace := BoundedLocatedFootprintAt.keep (env := env) (registry := registry) (Γ := Γ) (depth := depth) (budget := fun initial =>
        (Closure.close typing.origin (location.environment initial)).cost)
        (root := root) (boundary := boundary) (baseDepth := baseDepth)
        (locals := baseLocals) (σ := σ) (argument := argument) i ⟨_, demand⟩ .nil
      have packet : ∃ value : BoundedLocatedFootprintAt (env := env) root boundary registry Γ baseLocals σ argument baseDepth depth
          (fun initial => (Closure.close typing.origin (location.environment initial)).cost) [(i, ⟨_, demand⟩)] [(insertIndex depth i, ⟨_, demand⟩)],
          ∀ current, value.nativeDepth current = 0 := ⟨trace, fun _ => rfl⟩
      rw [hi] at packet
      obtain ⟨value, valueDepth⟩ := packet
      exact ⟨value, by intro current; simp only [Obs.nativeDepth, valueDepth, Nat.max_self]; exact Nat.le_refl _⟩
    · split at he
      · rename_i hi; exact (hcut (hi ▸ rfl)).elim
      · have hi := VExpr.bvar.inj he
        subst index
        have hindex : insertIndex depth (i - 1) = i := by
          unfold insertIndex
          split <;> omega
        refine ⟨[(i, ⟨_, demand⟩)], .var newLocals _ i demand, ?_⟩
        let trace := BoundedLocatedFootprintAt.keep (env := env) (registry := registry) (Γ := Γ) (depth := depth) (budget := fun initial =>
          (Closure.close typing.origin (location.environment initial)).cost)
          (root := root) (boundary := boundary) (baseDepth := baseDepth)
          (locals := baseLocals) (σ := σ) (argument := argument) (i - 1) ⟨_, demand⟩ .nil
        have packet : ∃ value : BoundedLocatedFootprintAt (env := env) root boundary registry Γ baseLocals σ argument baseDepth depth
            (fun initial => (Closure.close typing.origin (location.environment initial)).cost) [(i - 1, ⟨_, demand⟩)] [(insertIndex depth (i - 1), ⟨_, demand⟩)],
            ∀ current, value.nativeDepth current = 0 := ⟨trace, fun _ => rfl⟩
        rw [hindex] at packet
        obtain ⟨value, valueDepth⟩ := packet
        exact ⟨value, by intro current; simp only [Obs.nativeDepth, valueDepth, Nat.max_self]; exact Nat.le_refl _⟩
  | .empty, typing, location => exact ⟨[], .empty, .nil, by depth_bound⟩
  | .sort relevant, typing, location =>
    obtain rfl := sort_inst_inv he hcut
    exact ⟨[], .sort relevant, .nil, by depth_bound⟩
  | .app fn arg arguments admitted, typing, location =>
    obtain ⟨_, _, _, _, hu, hv, domainTyping, codomainTyping, function,
      argumentTyping, resultTyping, path, prefixEq, headBound⟩ := appView location
    obtain ⟨f₀, a₀, rfl, hfn, harg⟩ := app_inst_inv he hcut
    obtain ⟨ff, hf, sf, sfDepth⟩ := Obs.factorInstLocatedRelative_allDepth (baseDepth := baseDepth) fn function (.appFunction path) innerPrefix (by simpa only [Located.binderPrefix, prefixEq] using prefixSplit) f₀ argument depth depthEq hfn σ tail baseLocals newLocals
    obtain ⟨fa, ha, sa, saDepth⟩ := Obs.factorInstLocatedRelative_allDepth (baseDepth := baseDepth) arg argumentTyping (.appArgument path) innerPrefix (by simpa only [Located.binderPrefix, prefixEq] using prefixSplit) a₀ argument depth depthEq harg σ tail baseLocals newLocals
    refine ⟨ff ++ fa, (.app hf ha arguments (by simpa only [harg, instN_eq, subst_subst] using admitted)), (sf.weaken (fun initial => Nat.le_trans
      (Nat.le_of_lt (binder_other_cost (by simp) (path.environment initial))) (headBound initial))).append
      (sa.weaken (fun initial => Nat.le_trans
        (Nat.le_of_lt (binder_other_cost (by simp) (path.environment initial))) (headBound initial))), by depth_bound⟩
  | .lam domain guard body normal covered, typing, location =>
    obtain ⟨_, _, _, hu, hv, domainTyping, codomainTyping, bodyTyping, path, prefixEq, headBound⟩ := lamView location
    obtain ⟨A₀, body₀, rfl, hA, hb⟩ := lam_inst_inv he hcut
    obtain ⟨fd, hd, sd, sdDepth⟩ := CodeCert.factorInstLocatedRelative_allDepth (baseDepth := baseDepth) domain domainTyping (.lamDomain path) innerPrefix (by simpa only [Located.binderPrefix, prefixEq] using prefixSplit) A₀ argument depth depthEq hA σ tail baseLocals newLocals
    have bodyResult := Obs.factorInstLocatedRelative_allDepth (baseDepth := baseDepth) body bodyTyping (.lamBody path) (_ :: innerPrefix) (by simpa only [Located.binderPrefix, prefixEq, List.cons_append] using congrArg (List.cons _) prefixSplit) body₀ argument (depth + 1) (by simp only [List.length_cons]; omega) hb σ
      (tail_cons depth τ σ _ tail) baseLocals (Locals.push newLocals)
    rw [Subst.liftN, comp_cons] at bodyResult
    obtain ⟨fb, hb', sb, sbDepth⟩ := bodyResult
    obtain ⟨outside, pack, so, soDepth⟩ := sb.underBinder_allDepth normal
    rw [hA] at guard
    exact ⟨fd ++ outside, (.lam hd (LambdaGuard.factorInstLocated guard) hb' pack covered), (sd.weaken (fun initial => Nat.le_trans
      (Nat.le_of_lt (binder_domain_cost _ _ _ (path.environment initial))) (headBound initial))).append
      (so.weaken (fun initial => Nat.le_trans
        (Nat.le_of_lt (binder_body_cost (by simp) (path.environment initial))) (headBound initial))), by depth_bound⟩
  | .pi domain guard bodies, typing, location =>
    obtain ⟨_, _, hu, hv, domainTyping, bodyTyping, path, prefixEq, headBound⟩ := piView location
    obtain ⟨A₀, B₀, rfl, hA, hB⟩ := pi_inst_inv he hcut
    obtain ⟨fd, hd, sd, sdDepth⟩ := CodeCert.factorInstLocatedRelative_allDepth (baseDepth := baseDepth) domain domainTyping (.piDomain path) innerPrefix (by simpa only [Located.binderPrefix, prefixEq] using prefixSplit) A₀ argument depth depthEq hA σ tail baseLocals newLocals
    obtain ⟨fb, hb, sb, sbDepth⟩ := PiRows.factorInstLocatedRelative_allDepth (baseDepth := baseDepth) bodies bodyTyping (.piBody path) (_ :: innerPrefix) (by simpa only [Located.binderPrefix, prefixEq, List.cons_append] using congrArg (List.cons _) prefixSplit) A₀ B₀ argument depth (by simp only [List.length_cons]; omega) hA hB σ tail baseLocals newLocals
    rw [hA, hB] at guard
    exact ⟨fd ++ fb, (.pi hd (PiGuard.factorInstLocated guard) hb), (sd.weaken (fun initial => Nat.le_trans
      (Nat.le_of_lt (binder_domain_cost _ _ _ (path.environment initial))) (headBound initial))).append
      (sb.weaken (fun initial => Nat.le_trans
        (Nat.le_of_lt (binder_body_cost (by simp) (path.environment initial))) (headBound initial))), by depth_bound⟩
  | .union left right, typing, location =>
    obtain ⟨fl, hl, sl, slDepth⟩ := Obs.factorInstLocatedRelative_allDepth (baseDepth := baseDepth) left typing location innerPrefix prefixSplit original argument depth depthEq he σ tail baseLocals newLocals
    obtain ⟨fr, hr, sr, srDepth⟩ := Obs.factorInstLocatedRelative_allDepth (baseDepth := baseDepth) right typing location innerPrefix prefixSplit original argument depth depthEq he σ tail baseLocals newLocals
    exact ⟨fl ++ fr, .union hl hr, sl.append sr, by depth_bound⟩
  | .view source view, typing, location =>
    obtain ⟨f, h, s, sDepth⟩ := Obs.factorInstLocatedRelative_allDepth (baseDepth := baseDepth) source typing location innerPrefix prefixSplit original argument depth depthEq he σ tail baseLocals newLocals
    exact ⟨f, .view h view, s, by depth_bound⟩
  | .pad source, typing, location =>
    obtain ⟨f, h, s, sDepth⟩ := Obs.factorInstLocatedRelative_allDepth (baseDepth := baseDepth) source typing location innerPrefix prefixSplit original argument depth depthEq he σ tail baseLocals newLocals
    exact ⟨f, .pad h, s, by depth_bound⟩
  | .unpad source, typing, location =>
    obtain ⟨f, h, s, sDepth⟩ := Obs.factorInstLocatedRelative_allDepth (baseDepth := baseDepth) source typing location innerPrefix prefixSplit original argument depth depthEq he σ tail baseLocals newLocals
    exact ⟨f, .unpad h, s, by depth_bound⟩
  | .rowShift source, typing, location =>
    obtain ⟨f, h, s, sDepth⟩ := Obs.factorInstLocatedRelative_allDepth (baseDepth := baseDepth) source typing location innerPrefix prefixSplit original argument depth depthEq he σ tail baseLocals newLocals
    exact ⟨f, .rowShift h, s, by depth_bound⟩
termination_by sizeOf observation

theorem CodeCert.factorInstLocatedRelative_allDepth
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {Γ : List VExpr}
    {locals : List Nat} {τ : Subst} {expression : VExpr} {demand : Profile n} {footprint : Footprint}
    (certificate : CodeCert env U registry Γ locals τ expression demand footprint)
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    (typing : EndpointState sourceEnv U source expression assigned)
    (location : Located root typing)
    (innerPrefix : List VExpr) (prefixSplit : location.binderPrefix = innerPrefix ++ boundary)
    (original argument : VExpr) (depth : Nat)
    {baseDepth : Nat} (depthEq : depth = baseDepth + innerPrefix.length)
    (he : expression = original.inst argument depth)
    (σ : Subst) (tail : Subst.lift_l (.skipN .refl depth) τ = σ)
    (baseLocals newLocals : List Nat) :
    ∃ required, ∃ result : CodeCert env U registry Γ newLocals
      ((Subst.one argument).liftN depth |>.comp τ) original demand required,
      ∃ trace : BoundedLocatedFootprintAt (env := env) root boundary registry Γ baseLocals σ argument baseDepth depth
        (fun initial => (Closure.close typing.origin (location.environment initial)).cost) footprint required,
      ∀ current, max (result.nativeDepth current) (trace.nativeDepth current) ≤ certificate.nativeDepth current := by
  match certificate, typing, location with
  | .seed observation formed, typing, location =>
    obtain ⟨f, h, s, sDepth⟩ := Obs.factorInstLocatedRelative_allDepth (baseDepth := baseDepth) observation typing location innerPrefix prefixSplit original argument depth depthEq he σ tail baseLocals newLocals
    exact ⟨f, .seed h formed, s, by depth_bound⟩
  | .union left right, typing, location =>
    obtain ⟨fl, hl, sl, slDepth⟩ := CodeCert.factorInstLocatedRelative_allDepth (baseDepth := baseDepth) left typing location innerPrefix prefixSplit original argument depth depthEq he σ tail baseLocals newLocals
    obtain ⟨fr, hr, sr, srDepth⟩ := CodeCert.factorInstLocatedRelative_allDepth (baseDepth := baseDepth) right typing location innerPrefix prefixSplit original argument depth depthEq he σ tail baseLocals newLocals
    exact ⟨fl ++ fr, .union hl hr, sl.append sr, by depth_bound⟩
  | .pad source, typing, location =>
    obtain ⟨f, h, s, sDepth⟩ := CodeCert.factorInstLocatedRelative_allDepth (baseDepth := baseDepth) source typing location innerPrefix prefixSplit original argument depth depthEq he σ tail baseLocals newLocals
    exact ⟨f, .pad h, s, by depth_bound⟩
  | .familyPad source, typing, location =>
    obtain ⟨f, h, s, sDepth⟩ := CodeCert.factorInstLocatedRelative_allDepth (baseDepth := baseDepth) source typing location innerPrefix prefixSplit original argument depth depthEq he σ tail baseLocals newLocals
    exact ⟨f, .familyPad h, s, by depth_bound⟩
  | .unpad source, typing, location =>
    obtain ⟨f, h, s, sDepth⟩ := CodeCert.factorInstLocatedRelative_allDepth (baseDepth := baseDepth) source typing location innerPrefix prefixSplit original argument depth depthEq he σ tail baseLocals newLocals
    exact ⟨f, .unpad h, s, by depth_bound⟩
  | .down source, typing, location =>
    obtain ⟨f, h, s, sDepth⟩ := CodeCert.factorInstLocatedRelative_allDepth (baseDepth := baseDepth) source typing location innerPrefix prefixSplit original argument depth depthEq he σ tail baseLocals newLocals
    exact ⟨f, .down h, s, by depth_bound⟩
  | .map view source, typing, location =>
    obtain ⟨f, h, s, sDepth⟩ := CodeCert.factorInstLocatedRelative_allDepth (baseDepth := baseDepth) source typing location innerPrefix prefixSplit original argument depth depthEq he σ tail baseLocals newLocals
    exact ⟨f, .map view h, s, by depth_bound⟩
  | .select source member, typing, location =>
    obtain ⟨f, h, s, sDepth⟩ := CodeCert.factorInstLocatedRelative_allDepth (baseDepth := baseDepth) source typing location innerPrefix prefixSplit original argument depth depthEq he σ tail baseLocals newLocals
    exact ⟨f, .select h member, s, by depth_bound⟩
  | .focusMinimal source minimal bound, typing, location =>
    obtain ⟨f, h, s, sDepth⟩ := CodeCert.factorInstLocatedRelative_allDepth (baseDepth := baseDepth) source typing location innerPrefix prefixSplit original argument depth depthEq he σ tail baseLocals newLocals
    exact ⟨f, .focusMinimal h minimal bound, s, by depth_bound⟩
termination_by sizeOf certificate

theorem PiRows.factorInstLocatedRelative_allDepth
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {Γ : List VExpr}
    {locals : List Nat} {τ : Subst} {A B : VExpr} {ambient : Profile n}
    {rows : List (Key n × Profile n)} {footprint : Footprint}
    (bodies : PiRows env U registry Γ locals τ A B ambient rows footprint)
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    (typing : EndpointState sourceEnv U (A :: source) B assigned)
    (location : Located root typing)
    (innerPrefix : List VExpr) (prefixSplit : location.binderPrefix = innerPrefix ++ boundary)
    (A₀ B₀ argument : VExpr) (depth : Nat)
    {baseDepth : Nat} (depthEq : depth + 1 = baseDepth + innerPrefix.length)
    (hA : A = A₀.inst argument depth) (hB : B = B₀.inst argument (depth + 1))
    (σ : Subst) (tail : Subst.lift_l (.skipN .refl depth) τ = σ)
    (baseLocals newLocals : List Nat) :
    ∃ required, ∃ result : PiRows env U registry Γ newLocals
      ((Subst.one argument).liftN depth |>.comp τ) A₀ B₀ ambient rows required,
      ∃ trace : BoundedLocatedFootprintAt (env := env) root boundary registry Γ baseLocals σ argument baseDepth depth
        (fun initial => (Closure.close typing.origin (location.environment initial)).cost) footprint required,
      ∀ current, max (result.nativeDepth current) (trace.nativeDepth current) ≤ bodies.nativeDepth current := by
  match bodies, typing, location with
  | .nil, typing, location => exact ⟨[], .nil, .nil, by depth_bound⟩
  | .cons guard body normal covered rest, typing, location =>
    have bodyResult := CodeCert.factorInstLocatedRelative_allDepth (baseDepth := baseDepth) body typing location innerPrefix prefixSplit B₀ argument (depth + 1) depthEq hB σ
      (tail_cons depth τ σ _ tail) baseLocals (Locals.push newLocals)
    rw [Subst.liftN, comp_cons] at bodyResult
    obtain ⟨fb, hb, sb, sbDepth⟩ := bodyResult
    obtain ⟨outside, pack, so, soDepth⟩ := sb.underBinder_allDepth normal
    obtain ⟨fr, hr, sr, srDepth⟩ := PiRows.factorInstLocatedRelative_allDepth (baseDepth := baseDepth) rest typing location innerPrefix prefixSplit A₀ B₀ argument depth depthEq hA hB σ tail baseLocals newLocals
    rw [hA] at guard
    exact ⟨outside ++ fr, .cons (LambdaGuard.factorInstLocated guard) hb pack covered hr, so.append sr, by depth_bound⟩
termination_by sizeOf bodies
end

end Lean4Lean.AnchoredSource.Adapted.OriginalFactorCut
