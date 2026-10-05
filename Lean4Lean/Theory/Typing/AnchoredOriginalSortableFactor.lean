import Lean4Lean.Theory.Typing.AnchoredOriginalSortableFootprint

/-! Inverse substitution for the full Boolean-indexed formation grammar.
Every native sortable cut retains both its exact original endpoint and its
pre-reflection certificate. The budget is the selected input closure, not an
unrestricted root allowance. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalFactorCut
open VExpr VEnv AnchoredProfiles AnchoredSemantics
open OriginalClosureMeasure OriginalEndpointFactor
open private const_inst_inv app_inst_inv lam_inst_inv pi_inst_inv comp_cons tail_cons LambdaGuard.factorInstLocated PiGuard.factorInstLocated
  from Lean4Lean.Theory.Typing.AnchoredOriginalFactorTraversal
set_option backward.isDefEq.respectTransparency false

private theorem SortableCert.cutArgument
    (certificate : SortableCert env U registry Γ locals τ expression relevant demand footprint)
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    (typing : EndpointState sourceEnv U source expression assigned)
    (location : Located root typing)
    (innerPrefix : List VExpr) (prefixSplit : location.binderPrefix = innerPrefix ++ boundary)
    {baseDepth : Nat} (depthEq : depth = baseDepth + innerPrefix.length)
    (he : expression = (VExpr.bvar depth).inst argument depth)
    (tail : Subst.lift_l (.skipN .refl depth) τ = σ)
    (baseLocals newLocals : List Nat) :
    ∃ required, Nonempty (SortableCert env U registry Γ newLocals
      ((Subst.one argument).liftN depth |>.comp τ) (.bvar depth) relevant demand required) ∧
      Nonempty (SortableLocatedFootprint (env := env) root boundary registry Γ baseLocals σ argument baseDepth depth
        (fun initial => (Closure.close typing.origin (location.environment initial)).cost) footprint required) := by
  have he' : expression = argument.lift' (.skipN .refl depth) := by
    rw [he]
    simp only [inst, instVar, Nat.lt_irrefl, ite_false, ite_true]
    exact (lift'_consN_skipN (k := 0)).symm
  let cut : OriginalEndpointFactor.CutOriginAt root boundary argument baseDepth :=
    ⟨source, expression, assigned, typing, location, depth, he', innerPrefix, prefixSplit, depthEq⟩
  obtain ⟨required, ⟨original⟩, hf⟩ := certificate.reflectSource _ he' baseLocals
  rw [tail] at original
  let whole : WholeSortableCutQuery (env := env) cut registry Γ σ relevant demand required :=
    ⟨locals, τ, footprint, certificate, tail, hf⟩
  refine ⟨[(depth, ⟨_, demand⟩)], ⟨.seed (.var newLocals _ depth demand) certificate.formed⟩, ?_⟩
  rw [hf, ← shiftFootprint_sourceLift]
  exact ⟨by simpa only [List.append_nil] using SortableLocatedFootprint.cut cut (.sortable relevant original whole) (fun _ => Nat.le_refl _) SortableLocatedFootprint.nil⟩

private theorem SortableObs.cutArgument
    (observation : SortableObs env U registry Γ locals τ expression demand footprint)
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    (typing : EndpointState sourceEnv U source expression assigned)
    (location : Located root typing)
    (innerPrefix : List VExpr) (prefixSplit : location.binderPrefix = innerPrefix ++ boundary)
    {baseDepth : Nat} (depthEq : depth = baseDepth + innerPrefix.length)
    (he : expression = (VExpr.bvar depth).inst argument depth)
    (tail : Subst.lift_l (.skipN .refl depth) τ = σ)
    (baseLocals newLocals : List Nat) :
    ∃ required, Nonempty (SortableObs env U registry Γ newLocals
      ((Subst.one argument).liftN depth |>.comp τ) (.bvar depth) demand required) ∧
      Nonempty (SortableLocatedFootprint (env := env) root boundary registry Γ baseLocals σ argument baseDepth depth
        (fun initial => (Closure.close typing.origin (location.environment initial)).cost) footprint required) := by
  have he' : expression = argument.lift' (.skipN .refl depth) := by
    rw [he]
    simp only [inst, instVar, Nat.lt_irrefl, ite_false, ite_true]
    exact (lift'_consN_skipN (k := 0)).symm
  let cut : OriginalEndpointFactor.CutOriginAt root boundary argument baseDepth :=
    ⟨source, expression, assigned, typing, location, depth, he', innerPrefix, prefixSplit, depthEq⟩
  obtain ⟨required, ⟨original⟩, hf⟩ := observation.reflectSource _ he' baseLocals
  rw [tail] at original
  let whole : WholeObservedCutQuery (env := env) cut registry Γ σ demand required :=
    ⟨locals, τ, footprint, observation, tail, hf⟩
  refine ⟨[(depth, ⟨_, demand⟩)], ⟨.legacy (.var newLocals _ depth demand)⟩, ?_⟩
  rw [hf, ← shiftFootprint_sourceLift]
  exact ⟨by simpa only [List.append_nil] using SortableLocatedFootprint.cut cut (.observed original whole) (fun _ => Nat.le_refl _) SortableLocatedFootprint.nil⟩

mutual
theorem SortableCert.factorInstLocatedRelative
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {Γ : List VExpr}
    {locals : List Nat} {τ : Subst} {expression : VExpr} {demand : Profile n} {footprint : Footprint}
    (certificate : SortableCert env U registry Γ locals τ expression relevant demand footprint)
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    (typing : EndpointState sourceEnv U source expression assigned)
    (location : Located root typing)
    (innerPrefix : List VExpr) (prefixSplit : location.binderPrefix = innerPrefix ++ boundary)
    (original argument : VExpr) (depth : Nat)
    {baseDepth : Nat} (depthEq : depth = baseDepth + innerPrefix.length)
    (he : expression = original.inst argument depth)
    (σ : Subst) (tail : Subst.lift_l (.skipN .refl depth) τ = σ)
    (baseLocals newLocals : List Nat) :
    ∃ required, Nonempty (SortableCert env U registry Γ newLocals
      ((Subst.one argument).liftN depth |>.comp τ) original relevant demand required) ∧
      Nonempty (SortableLocatedFootprint (env := env) root boundary registry Γ baseLocals σ argument baseDepth depth
        (fun initial => (Closure.close typing.origin (location.environment initial)).cost) footprint required) := by
  classical
  by_cases hcut : original = .bvar depth
  · subst original
    exact SortableCert.cutArgument certificate typing location innerPrefix prefixSplit depthEq he tail baseLocals newLocals
  match certificate, typing, location with
  | .observe observation formed, typing, location =>
    obtain ⟨f, ⟨h⟩, trace⟩ := SortableObs.factorInstLocatedRelative (baseDepth := baseDepth) observation typing location innerPrefix prefixSplit original argument depth depthEq he σ tail baseLocals newLocals
    exact ⟨f, ⟨.observe h formed⟩, trace⟩
  | .ofCode source formed, typing, location =>
    obtain ⟨f, ⟨h⟩, ⟨s⟩⟩ := CodeCert.factorInstLocatedRelative (baseDepth := baseDepth) source typing location innerPrefix prefixSplit original argument depth depthEq he σ tail baseLocals newLocals
    exact ⟨f, ⟨.ofCode h formed⟩, ⟨(SortableLocatedFootprint.ofLegacy s)⟩⟩
  | .pi domain guard bodies, typing, location =>
    obtain ⟨_, _, hu, hv, domainTyping, bodyTyping, path, prefixEq, headBound⟩ := piView location
    obtain ⟨A₀, B₀, rfl, hA, hB⟩ := pi_inst_inv he hcut
    obtain ⟨fd, ⟨hd⟩, ⟨sd⟩⟩ := SortableCert.factorInstLocatedRelative (baseDepth := baseDepth) domain domainTyping (.piDomain path) innerPrefix (by simpa only [Located.binderPrefix, prefixEq] using prefixSplit) A₀ argument depth depthEq hA σ tail baseLocals newLocals
    obtain ⟨fb, ⟨hb⟩, ⟨sb⟩⟩ := SortableRows.factorInstLocatedRelative (baseDepth := baseDepth) bodies bodyTyping (.piBody path) (_ :: innerPrefix) (by simpa only [Located.binderPrefix, prefixEq, List.cons_append] using congrArg (List.cons _) prefixSplit) A₀ B₀ argument depth (by simp only [List.length_cons]; omega) hA hB σ tail baseLocals newLocals
    rw [hA, hB] at guard
    exact ⟨fd ++ fb, ⟨.pi hd (PiGuard.factorInstLocated guard) hb⟩, ⟨(sd.weaken (fun initial => Nat.le_trans
      (Nat.le_of_lt (binder_domain_cost _ _ _ (path.environment initial))) (headBound initial))).append
      (sb.weaken (fun initial => Nat.le_trans
        (Nat.le_of_lt (binder_body_cost (by simp) (path.environment initial))) (headBound initial)))⟩⟩
  | .seed observation formed, typing, location =>
    obtain ⟨f, ⟨h⟩, ⟨s⟩⟩ := Obs.factorInstLocatedRelative (baseDepth := baseDepth) observation typing location innerPrefix prefixSplit original argument depth depthEq he σ tail baseLocals newLocals
    exact ⟨f, ⟨.seed h formed⟩, ⟨(SortableLocatedFootprint.ofLegacy s)⟩⟩
  | .union left right, typing, location =>
    obtain ⟨fl, ⟨hl⟩, ⟨sl⟩⟩ := SortableCert.factorInstLocatedRelative (baseDepth := baseDepth) left typing location innerPrefix prefixSplit original argument depth depthEq he σ tail baseLocals newLocals
    obtain ⟨fr, ⟨hr⟩, ⟨sr⟩⟩ := SortableCert.factorInstLocatedRelative (baseDepth := baseDepth) right typing location innerPrefix prefixSplit original argument depth depthEq he σ tail baseLocals newLocals
    exact ⟨fl ++ fr, ⟨.union hl hr⟩, ⟨sl.append sr⟩⟩
  | .pad source, typing, location =>
    obtain ⟨f, ⟨h⟩, s⟩ := SortableCert.factorInstLocatedRelative (baseDepth := baseDepth) source typing location innerPrefix prefixSplit original argument depth depthEq he σ tail baseLocals newLocals
    exact ⟨f, ⟨.pad h⟩, s⟩
  | .familyPad source, typing, location =>
    obtain ⟨f, ⟨h⟩, s⟩ := SortableCert.factorInstLocatedRelative (baseDepth := baseDepth) source typing location innerPrefix prefixSplit original argument depth depthEq he σ tail baseLocals newLocals
    exact ⟨f, ⟨.familyPad h⟩, s⟩
  | .sortPad source, typing, location =>
    obtain ⟨f, ⟨h⟩, s⟩ := SortableCert.factorInstLocatedRelative (baseDepth := baseDepth) source typing location innerPrefix prefixSplit original argument depth depthEq he σ tail baseLocals newLocals
    exact ⟨f, ⟨.sortPad h⟩, s⟩
  | .unpad source, typing, location =>
    obtain ⟨f, ⟨h⟩, s⟩ := SortableCert.factorInstLocatedRelative (baseDepth := baseDepth) source typing location innerPrefix prefixSplit original argument depth depthEq he σ tail baseLocals newLocals
    exact ⟨f, ⟨.unpad h⟩, s⟩
  | .down source, typing, location =>
    obtain ⟨f, ⟨h⟩, s⟩ := SortableCert.factorInstLocatedRelative (baseDepth := baseDepth) source typing location innerPrefix prefixSplit original argument depth depthEq he σ tail baseLocals newLocals
    exact ⟨f, ⟨.down h⟩, s⟩
  | .support action source, typing, location =>
    obtain ⟨f, ⟨h⟩, s⟩ := SortableCert.factorInstLocatedRelative (baseDepth := baseDepth) source typing location innerPrefix prefixSplit original argument depth depthEq he σ tail baseLocals newLocals
    exact ⟨f, ⟨.support action h⟩, s⟩
  | .map view source, typing, location =>
    obtain ⟨f, ⟨h⟩, s⟩ := SortableCert.factorInstLocatedRelative (baseDepth := baseDepth) source typing location innerPrefix prefixSplit original argument depth depthEq he σ tail baseLocals newLocals
    exact ⟨f, ⟨.map view h⟩, s⟩
  | .select source member, typing, location =>
    obtain ⟨f, ⟨h⟩, s⟩ := SortableCert.factorInstLocatedRelative (baseDepth := baseDepth) source typing location innerPrefix prefixSplit original argument depth depthEq he σ tail baseLocals newLocals
    exact ⟨f, ⟨.select h member⟩, s⟩
  | .focusMinimal source minimal bound, typing, location =>
    obtain ⟨f, ⟨h⟩, s⟩ := SortableCert.factorInstLocatedRelative (baseDepth := baseDepth) source typing location innerPrefix prefixSplit original argument depth depthEq he σ tail baseLocals newLocals
    exact ⟨f, ⟨.focusMinimal h minimal bound⟩, s⟩
termination_by sizeOf certificate

theorem SortableRows.factorInstLocatedRelative
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {Γ : List VExpr}
    {locals : List Nat} {τ : Subst} {A B : VExpr} {ambient : Profile n}
    {rows : List (Key n × Profile n)} {footprint : Footprint}
    (bodies : SortableRows env U registry Γ locals τ A B relevant ambient rows footprint)
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    (typing : EndpointState sourceEnv U (A :: source) B assigned)
    (location : Located root typing)
    (innerPrefix : List VExpr) (prefixSplit : location.binderPrefix = innerPrefix ++ boundary)
    (A₀ B₀ argument : VExpr) (depth : Nat)
    {baseDepth : Nat} (depthEq : depth + 1 = baseDepth + innerPrefix.length)
    (hA : A = A₀.inst argument depth) (hB : B = B₀.inst argument (depth + 1))
    (σ : Subst) (tail : Subst.lift_l (.skipN .refl depth) τ = σ)
    (baseLocals newLocals : List Nat) :
    ∃ required, Nonempty (SortableRows env U registry Γ newLocals
      ((Subst.one argument).liftN depth |>.comp τ) A₀ B₀ relevant ambient rows required) ∧
      Nonempty (SortableLocatedFootprint (env := env) root boundary registry Γ baseLocals σ argument baseDepth depth
        (fun initial => (Closure.close typing.origin (location.environment initial)).cost) footprint required) := by
  match bodies, typing, location with
  | .nil, typing, location => exact ⟨[], ⟨.nil⟩, ⟨.nil⟩⟩
  | .cons guard body normal covered rest, typing, location =>
    obtain ⟨fb, ⟨hb⟩, ⟨sb⟩⟩ := SortableCert.factorInstLocatedRelative (baseDepth := baseDepth) body typing location innerPrefix prefixSplit B₀ argument (depth + 1) depthEq hB σ
      (tail_cons depth τ σ _ tail) baseLocals (Locals.push newLocals)
    rw [Subst.liftN, comp_cons] at hb
    obtain ⟨outside, pack, ⟨so⟩⟩ := sb.underBinder normal
    obtain ⟨fr, ⟨hr⟩, ⟨sr⟩⟩ := SortableRows.factorInstLocatedRelative (baseDepth := baseDepth) rest typing location innerPrefix prefixSplit A₀ B₀ argument depth depthEq hA hB σ tail baseLocals newLocals
    rw [hA] at guard
    exact ⟨outside ++ fr, ⟨.cons (LambdaGuard.factorInstLocated guard) hb pack covered hr⟩, ⟨so.append sr⟩⟩
termination_by sizeOf bodies
theorem SortableObs.factorInstLocatedRelative
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {Γ : List VExpr}
    {locals : List Nat} {τ : Subst} {expression : VExpr} {demand : Profile n} {footprint : Footprint}
    (observation : SortableObs env U registry Γ locals τ expression demand footprint)
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    (typing : EndpointState sourceEnv U source expression assigned)
    (location : Located root typing)
    (innerPrefix : List VExpr) (prefixSplit : location.binderPrefix = innerPrefix ++ boundary)
    (original argument : VExpr) (depth : Nat)
    {baseDepth : Nat} (depthEq : depth = baseDepth + innerPrefix.length)
    (he : expression = original.inst argument depth)
    (σ : Subst) (tail : Subst.lift_l (.skipN .refl depth) τ = σ)
    (baseLocals newLocals : List Nat) :
    ∃ required, Nonempty (SortableObs env U registry Γ newLocals
      ((Subst.one argument).liftN depth |>.comp τ) original demand required) ∧
      Nonempty (SortableLocatedFootprint (env := env) root boundary registry Γ baseLocals σ argument baseDepth depth
        (fun initial => (Closure.close typing.origin (location.environment initial)).cost) footprint required) := by
  classical
  by_cases hcut : original = .bvar depth
  · subst original
    exact SortableObs.cutArgument observation typing location innerPrefix prefixSplit depthEq he tail baseLocals newLocals
  match observation, typing, location with
  | .family lookup noDefinition noNative noQuotient seedWF seedLength levelsWF equivalent signature typeClosed typeCertificate typed tree, typing, location =>
    obtain rfl := const_inst_inv he hcut
    exact ⟨[], ⟨.family lookup noDefinition noNative noQuotient seedWF seedLength levelsWF equivalent signature typeClosed typeCertificate typed tree⟩, ⟨.nil⟩⟩
  | .legacy source, typing, location =>
    obtain ⟨f, ⟨h⟩, ⟨trace⟩⟩ := Obs.factorInstLocatedRelative (baseDepth := baseDepth) source typing location innerPrefix prefixSplit original argument depth depthEq he σ tail baseLocals newLocals
    exact ⟨f, ⟨.legacy h⟩, ⟨SortableLocatedFootprint.ofLegacy trace⟩⟩
  | .code relevant source, typing, location =>
    obtain ⟨f, ⟨h⟩, trace⟩ := SortableCert.factorInstLocatedRelative (baseDepth := baseDepth) source typing location innerPrefix prefixSplit original argument depth depthEq he σ tail baseLocals newLocals
    exact ⟨f, ⟨.code relevant h⟩, trace⟩
  | .app fn arg arguments admitted, typing, location =>
    obtain ⟨_, _, _, _, hu, hv, domainTyping, codomainTyping, function,
      argumentTyping, resultTyping, path, prefixEq, headBound⟩ := appView location
    obtain ⟨f₀, a₀, rfl, hfn, harg⟩ := app_inst_inv he hcut
    obtain ⟨ff, ⟨hf⟩, ⟨sf⟩⟩ := SortableObs.factorInstLocatedRelative (baseDepth := baseDepth) fn function (.appFunction path) innerPrefix (by simpa only [Located.binderPrefix, prefixEq] using prefixSplit) f₀ argument depth depthEq hfn σ tail baseLocals newLocals
    obtain ⟨fa, ⟨ha⟩, ⟨sa⟩⟩ := SortableObs.factorInstLocatedRelative (baseDepth := baseDepth) arg argumentTyping (.appArgument path) innerPrefix (by simpa only [Located.binderPrefix, prefixEq] using prefixSplit) a₀ argument depth depthEq harg σ tail baseLocals newLocals
    refine ⟨ff ++ fa, ⟨.app hf ha arguments ?_⟩, ⟨(sf.weaken (fun initial => Nat.le_trans
      (Nat.le_of_lt (binder_other_cost (by simp) (path.environment initial))) (headBound initial))).append
      (sa.weaken (fun initial => Nat.le_trans
        (Nat.le_of_lt (binder_other_cost (by simp) (path.environment initial))) (headBound initial)))⟩⟩
    simpa only [harg, instN_eq, subst_subst] using admitted
  | .lam domain guard body normal covered, typing, location =>
    obtain ⟨_, _, _, hu, hv, domainTyping, codomainTyping, bodyTyping, path, prefixEq, headBound⟩ := lamView location
    obtain ⟨A₀, body₀, rfl, hA, hb⟩ := lam_inst_inv he hcut
    obtain ⟨fd, ⟨hd⟩, ⟨sd⟩⟩ := SortableCert.factorInstLocatedRelative (baseDepth := baseDepth) domain domainTyping (.lamDomain path) innerPrefix (by simpa only [Located.binderPrefix, prefixEq] using prefixSplit) A₀ argument depth depthEq hA σ tail baseLocals newLocals
    obtain ⟨fb, ⟨hb'⟩, ⟨sb⟩⟩ := SortableObs.factorInstLocatedRelative (baseDepth := baseDepth) body bodyTyping (.lamBody path) (_ :: innerPrefix) (by simpa only [Located.binderPrefix, prefixEq, List.cons_append] using congrArg (List.cons _) prefixSplit) body₀ argument (depth + 1) (by simp only [List.length_cons]; omega) hb σ
      (tail_cons depth τ σ _ tail) baseLocals (Locals.push newLocals)
    rw [Subst.liftN, comp_cons] at hb'
    obtain ⟨outside, pack, ⟨so⟩⟩ := sb.underBinder normal
    rw [hA] at guard
    exact ⟨fd ++ outside, ⟨.lam hd (LambdaGuard.factorInstLocated guard) hb' pack covered⟩, ⟨(sd.weaken (fun initial => Nat.le_trans
      (Nat.le_of_lt (binder_domain_cost _ _ _ (path.environment initial))) (headBound initial))).append
      (so.weaken (fun initial => Nat.le_trans
        (Nat.le_of_lt (binder_body_cost (by simp) (path.environment initial))) (headBound initial)))⟩⟩
  | .union left right, typing, location =>
    obtain ⟨fl, ⟨hl⟩, ⟨sl⟩⟩ := SortableObs.factorInstLocatedRelative (baseDepth := baseDepth) left typing location innerPrefix prefixSplit original argument depth depthEq he σ tail baseLocals newLocals
    obtain ⟨fr, ⟨hr⟩, ⟨sr⟩⟩ := SortableObs.factorInstLocatedRelative (baseDepth := baseDepth) right typing location innerPrefix prefixSplit original argument depth depthEq he σ tail baseLocals newLocals
    exact ⟨fl ++ fr, ⟨.union hl hr⟩, ⟨sl.append sr⟩⟩
  | .action source action, typing, location =>
    obtain ⟨f, ⟨h⟩, ⟨s⟩⟩ := SortableObs.factorInstLocatedRelative (baseDepth := baseDepth) source typing location innerPrefix prefixSplit original argument depth depthEq he σ tail baseLocals newLocals
    exact ⟨f, ⟨.action h action⟩, ⟨s⟩⟩
  | .view source view, typing, location =>
    obtain ⟨f, ⟨h⟩, ⟨s⟩⟩ := SortableObs.factorInstLocatedRelative (baseDepth := baseDepth) source typing location innerPrefix prefixSplit original argument depth depthEq he σ tail baseLocals newLocals
    exact ⟨f, ⟨.view h view⟩, ⟨s⟩⟩
  | .pad source, typing, location =>
    obtain ⟨f, ⟨h⟩, ⟨s⟩⟩ := SortableObs.factorInstLocatedRelative (baseDepth := baseDepth) source typing location innerPrefix prefixSplit original argument depth depthEq he σ tail baseLocals newLocals
    exact ⟨f, ⟨.pad h⟩, ⟨s⟩⟩
  | .unpad source, typing, location =>
    obtain ⟨f, ⟨h⟩, ⟨s⟩⟩ := SortableObs.factorInstLocatedRelative (baseDepth := baseDepth) source typing location innerPrefix prefixSplit original argument depth depthEq he σ tail baseLocals newLocals
    exact ⟨f, ⟨.unpad h⟩, ⟨s⟩⟩
  | .rowShift source, typing, location =>
    obtain ⟨f, ⟨h⟩, ⟨s⟩⟩ := SortableObs.factorInstLocatedRelative (baseDepth := baseDepth) source typing location innerPrefix prefixSplit original argument depth depthEq he σ tail baseLocals newLocals
    exact ⟨f, ⟨.rowShift h⟩, ⟨s⟩⟩
termination_by sizeOf observation

end

theorem SortableCert.factorInstAtStart
    (certificate : SortableCert env U registry Γ locals σ (B.inst argument) relevant demand footprint)
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    (typing : EndpointState sourceEnv U source (B.inst argument) assigned)
    (location : Located root typing) (baseLocals newLocals : List Nat) :
    ∃ required, Nonempty (SortableCert env U registry Γ newLocals
      ((Subst.one argument).comp σ) B relevant demand required) ∧
      Nonempty (SortableLocatedFootprint (env := env) root location.binderPrefix registry Γ
        baseLocals σ argument 0 0
        (fun initial => (Closure.close typing.origin (location.environment initial)).cost)
        footprint required) := by
  exact SortableCert.factorInstLocatedRelative (baseDepth := 0) certificate typing location []
    (by simp) B argument 0 rfl rfl σ rfl baseLocals newLocals

theorem SortableObs.factorInstAtStart
    (observation : SortableObs env U registry Γ locals σ (body.inst argument) demand footprint)
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    (typing : EndpointState sourceEnv U source (body.inst argument) assigned)
    (location : Located root typing) (baseLocals newLocals : List Nat) :
    ∃ required, Nonempty (SortableObs env U registry Γ newLocals
      ((Subst.one argument).comp σ) body demand required) ∧
      Nonempty (SortableLocatedFootprint (env := env) root location.binderPrefix registry Γ
        baseLocals σ argument 0 0
        (fun initial => (Closure.close typing.origin (location.environment initial)).cost)
        footprint required) := by
  exact SortableObs.factorInstLocatedRelative (baseDepth := 0) observation typing location []
    (by simp) body argument 0 rfl rfl σ rfl baseLocals newLocals


end Lean4Lean.AnchoredSource.Adapted.OriginalFactorCut
