import Lean4Lean.Theory.Typing.AnchoredOriginalCaptureFootprint
import Lean4Lean.Theory.Typing.AnchoredOriginalCaptureSubstitution
import Lean4Lean.Theory.Typing.AnchoredNativeTemplateRealization

/-! Simultaneous inverse capture substitution at one actual original endpoint.
Every removed capture observation retains its original assigned type, source
location and query before reflection. No intermediate residual certificate is
assigned a synthesized original typing. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalFactorCut
open VExpr VEnv AnchoredProfiles AnchoredSemantics
open OriginalClosureMeasure OriginalEndpointFactor
set_option backward.isDefEq.respectTransparency false

private theorem LambdaGuard.factorCaptures
    (guard : LambdaGuard env U registry Γ τ (annotation.subst replacement) key support) :
    LambdaGuard env U registry Γ (replacement.comp τ) annotation key support := by
  refine ⟨guard.inputTyped, guard.formed, ?_, ?_, guard.anchor⟩
  · simpa only [subst_subst] using guard.path
  · simpa only [subst_subst] using guard.domains

private theorem PiGuard.factorCaptures
    (guard : PiGuard env U Γ τ (A.subst replacement) (B.subst replacement.lift) C D) :
    PiGuard env U Γ (replacement.comp τ) A B C D := by
  constructor
  · simpa only [subst_subst] using guard.domainPath
  · simpa only [subst_subst, Subst.comp_lift] using guard.bodyPath

private theorem Obs.cutCapture
    (observation : Obs env U registry Γ locals τ expression demand footprint)
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    (typing : EndpointState sourceEnv U source expression assigned)
    (location : Located root typing)
    (index : Nat) (bound : index < arguments.length)
    {baseDepth : Nat} (depthEq : depth = baseDepth + location.binderPrefix.length)
    (he : expression = (VExpr.bvar (depth + index)).subst
      ((Subst.ofList arguments).liftN depth))
    (tail : Subst.lift_l (.skipN .refl depth) τ = σ)
    (baseLocals newLocals : List Nat) :
    ∃ required, Nonempty (Obs env U registry Γ newLocals
      (((Subst.ofList arguments).liftN depth).comp τ) (.bvar (depth + index)) demand required) ∧
      Nonempty (CaptureFootprint (env := env) root registry Γ baseLocals σ arguments baseDepth depth
        (fun initial => (Closure.close typing.origin (location.environment initial)).cost) footprint required) := by
  have he' : expression = arguments[arguments.length - 1 - index].lift' (.skipN .refl depth) :=
    he.trans (capture_selected arguments depth index bound)
  let cut : OriginalEndpointFactor.CutOrigin root arguments[arguments.length - 1 - index] baseDepth :=
    ⟨source, expression, assigned, typing, location, depth, he',
      location.binderPrefix, by simp, depthEq⟩
  obtain ⟨required, ⟨original⟩, hf⟩ := observation.reflectSource _ he' baseLocals
  rw [tail] at original
  let whole : WholeCutQuery (env := env) cut registry Γ σ demand required :=
    ⟨locals, τ, footprint, observation, tail, hf⟩
  refine ⟨[(depth + index, ⟨_, demand⟩)], ⟨.var newLocals _ _ demand⟩, ?_⟩
  rw [hf, ← shiftFootprint_sourceLift]
  exact ⟨by simpa only [List.append_nil] using
    CaptureFootprint.cut index bound cut original whole (fun _ => Nat.le_refl _) CaptureFootprint.nil⟩

mutual
theorem Obs.factorCapturesLocated
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {Γ : List VExpr}
    {locals : List Nat} {τ : Subst} {expression : VExpr} {demand : Profile n} {footprint : Footprint}
    (observation : Obs env U registry Γ locals τ expression demand footprint)
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    (typing : EndpointState sourceEnv U source expression assigned)
    (location : Located root typing)
    (original : VExpr) (arguments : List VExpr) (depth : Nat)
    {baseDepth : Nat} (depthEq : depth = baseDepth + location.binderPrefix.length)
    (he : expression = original.subst ((Subst.ofList arguments).liftN depth))
    (σ : Subst) (tail : Subst.lift_l (.skipN .refl depth) τ = σ)
    (baseLocals newLocals : List Nat) :
    ∃ required, Nonempty (Obs env U registry Γ newLocals
      ((Subst.ofList arguments).liftN depth |>.comp τ) original demand required) ∧
      Nonempty (CaptureFootprint (env := env) root registry Γ baseLocals σ arguments baseDepth depth
        (fun initial => (Closure.close typing.origin (location.environment initial)).cost) footprint required) := by
  classical
  by_cases hcut : CaptureSelected arguments depth original
  · obtain ⟨index, bound, rfl⟩ := hcut
    exact Obs.cutCapture observation typing location index bound depthEq he tail baseLocals newLocals
  match observation, typing, location with
  | .delta lookup nameEq registered seedWF seedLength levelsWF equivalent bodyClosed typeClosed typeCertificate typed body, typing, location =>
    obtain rfl := capture_const_inv he hcut
    exact ⟨[], ⟨.delta lookup nameEq registered seedWF seedLength levelsWF equivalent bodyClosed typeClosed typeCertificate typed body⟩, ⟨.nil⟩⟩
  | .native lookup noDefinition nameEq registered seedWF levelsWF equivalent signature typeClosed typeCertificate typed tree, typing, location =>
    obtain rfl := capture_const_inv he hcut
    exact ⟨[], ⟨.native lookup noDefinition nameEq registered seedWF levelsWF equivalent signature typeClosed typeCertificate typed tree⟩, ⟨.nil⟩⟩
  | .family lookup noDefinition noNative noQuotient seedWF seedLength levelsWF equivalent signature typeClosed typeCertificate typed tree, typing, location =>
    obtain rfl := capture_const_inv he hcut
    exact ⟨[], ⟨.family lookup noDefinition noNative noQuotient seedWF seedLength levelsWF equivalent signature typeClosed typeCertificate typed tree⟩, ⟨.nil⟩⟩
  | .constructor lookup noDefinition noNative noQuotient seedWF seedLength levelsWF equivalent signature typeClosed typeCertificate typed tree, typing, location =>
    obtain rfl := capture_const_inv he hcut
    exact ⟨[], ⟨.constructor lookup noDefinition noNative noQuotient seedWF seedLength levelsWF equivalent signature typeClosed typeCertificate typed tree⟩, ⟨.nil⟩⟩
  | .var _ _ index demand, typing, location =>
    obtain rfl := capture_bvar_inv he hcut
    exact ⟨[(captureInsert arguments.length depth index, ⟨_, demand⟩)],
      ⟨.var newLocals _ _ demand⟩, ⟨.keep index _ .nil⟩⟩
  | .empty, typing, location => exact ⟨[], ⟨.empty⟩, ⟨.nil⟩⟩
  | .sort relevant, typing, location =>
    obtain rfl := capture_sort_inv he hcut
    exact ⟨[], ⟨.sort relevant⟩, ⟨.nil⟩⟩
  | .app fn arg coveredArgs admitted, typing, location =>
    obtain ⟨_, _, _, _, hu, hv, domainTyping, codomainTyping, function,
      argumentTyping, resultTyping, path, prefixEq, headBound⟩ := appView location
    obtain ⟨f₀, a₀, rfl, hfn, harg⟩ := capture_app_inv he hcut
    obtain ⟨ff, ⟨hf⟩, ⟨sf⟩⟩ := Obs.factorCapturesLocated (baseDepth := baseDepth) fn function (.appFunction path) f₀ arguments depth (by simpa only [Located.binderPrefix, prefixEq] using depthEq) hfn σ tail baseLocals newLocals
    obtain ⟨fa, ⟨ha⟩, ⟨sa⟩⟩ := Obs.factorCapturesLocated (baseDepth := baseDepth) arg argumentTyping (.appArgument path) a₀ arguments depth (by simpa only [Located.binderPrefix, prefixEq] using depthEq) harg σ tail baseLocals newLocals
    refine ⟨ff ++ fa, ⟨.app hf ha coveredArgs ?_⟩, ⟨(sf.weaken (fun initial => Nat.le_trans
      (Nat.le_of_lt (binder_other_cost (by simp) (path.environment initial))) (headBound initial))).append
      (sa.weaken (fun initial => Nat.le_trans
        (Nat.le_of_lt (binder_other_cost (by simp) (path.environment initial))) (headBound initial)))⟩⟩
    simpa only [harg, subst_subst] using admitted
  | .lam domain guard body normal covered, typing, location =>
    obtain ⟨_, _, _, hu, hv, domainTyping, codomainTyping, bodyTyping, path, prefixEq, headBound⟩ := lamView location
    obtain ⟨A₀, body₀, rfl, hA, hb⟩ := capture_lam_inv he hcut
    obtain ⟨fd, ⟨hd⟩, ⟨sd⟩⟩ := CodeCert.factorCapturesLocated (baseDepth := baseDepth) domain domainTyping (.lamDomain path) A₀ arguments depth (by simpa only [Located.binderPrefix, prefixEq] using depthEq) hA σ tail baseLocals newLocals
    obtain ⟨fb, ⟨hb'⟩, ⟨sb⟩⟩ := Obs.factorCapturesLocated (baseDepth := baseDepth) body bodyTyping (.lamBody path) body₀ arguments (depth + 1) (by simp only [Located.binderPrefix, List.length_cons, prefixEq]; omega) hb σ
      (capture_tail_cons depth τ σ _ tail) baseLocals (Locals.push newLocals)
    rw [Subst.liftN, capture_realization_cons] at hb'
    obtain ⟨outside, pack, ⟨so⟩⟩ := sb.underBinder normal
    rw [hA] at guard
    exact ⟨fd ++ outside, ⟨.lam hd (LambdaGuard.factorCaptures guard) hb' pack covered⟩, ⟨(sd.weaken (fun initial => Nat.le_trans
      (Nat.le_of_lt (binder_domain_cost _ _ _ (path.environment initial))) (headBound initial))).append
      (so.weaken (fun initial => Nat.le_trans
        (Nat.le_of_lt (binder_body_cost (by simp) (path.environment initial))) (headBound initial)))⟩⟩
  | .pi domain guard bodies, typing, location =>
    obtain ⟨_, _, hu, hv, domainTyping, bodyTyping, path, prefixEq, headBound⟩ := piView location
    obtain ⟨A₀, B₀, rfl, hA, hB⟩ := capture_pi_inv he hcut
    obtain ⟨fd, ⟨hd⟩, ⟨sd⟩⟩ := CodeCert.factorCapturesLocated (baseDepth := baseDepth) domain domainTyping (.piDomain path) A₀ arguments depth (by simpa only [Located.binderPrefix, prefixEq] using depthEq) hA σ tail baseLocals newLocals
    obtain ⟨fb, ⟨hb⟩, ⟨sb⟩⟩ := PiRows.factorCapturesLocated (baseDepth := baseDepth) bodies bodyTyping (.piBody path) A₀ B₀ arguments depth (by simp only [Located.binderPrefix, List.length_cons, prefixEq]; omega) hA hB σ tail baseLocals newLocals
    rw [hA, hB] at guard
    exact ⟨fd ++ fb, ⟨.pi hd (PiGuard.factorCaptures (by simpa only [Subst.liftN] using guard)) hb⟩, ⟨(sd.weaken (fun initial => Nat.le_trans
      (Nat.le_of_lt (binder_domain_cost _ _ _ (path.environment initial))) (headBound initial))).append
      (sb.weaken (fun initial => Nat.le_trans
        (Nat.le_of_lt (binder_body_cost (by simp) (path.environment initial))) (headBound initial)))⟩⟩
  | .union left right, typing, location =>
    obtain ⟨fl, ⟨hl⟩, ⟨sl⟩⟩ := Obs.factorCapturesLocated (baseDepth := baseDepth) left typing location original arguments depth depthEq he σ tail baseLocals newLocals
    obtain ⟨fr, ⟨hr⟩, ⟨sr⟩⟩ := Obs.factorCapturesLocated (baseDepth := baseDepth) right typing location original arguments depth depthEq he σ tail baseLocals newLocals
    exact ⟨fl ++ fr, ⟨.union hl hr⟩, ⟨sl.append sr⟩⟩
  | .view source view, typing, location =>
    obtain ⟨f, ⟨h⟩, ⟨s⟩⟩ := Obs.factorCapturesLocated (baseDepth := baseDepth) source typing location original arguments depth depthEq he σ tail baseLocals newLocals
    exact ⟨f, ⟨.view h view⟩, ⟨s⟩⟩
  | .pad source, typing, location =>
    obtain ⟨f, ⟨h⟩, ⟨s⟩⟩ := Obs.factorCapturesLocated (baseDepth := baseDepth) source typing location original arguments depth depthEq he σ tail baseLocals newLocals
    exact ⟨f, ⟨.pad h⟩, ⟨s⟩⟩
  | .unpad source, typing, location =>
    obtain ⟨f, ⟨h⟩, ⟨s⟩⟩ := Obs.factorCapturesLocated (baseDepth := baseDepth) source typing location original arguments depth depthEq he σ tail baseLocals newLocals
    exact ⟨f, ⟨.unpad h⟩, ⟨s⟩⟩
  | .rowShift source, typing, location =>
    obtain ⟨f, ⟨h⟩, ⟨s⟩⟩ := Obs.factorCapturesLocated (baseDepth := baseDepth) source typing location original arguments depth depthEq he σ tail baseLocals newLocals
    exact ⟨f, ⟨.rowShift h⟩, ⟨s⟩⟩
termination_by sizeOf observation

theorem CodeCert.factorCapturesLocated
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {Γ : List VExpr}
    {locals : List Nat} {τ : Subst} {expression : VExpr} {demand : Profile n} {footprint : Footprint}
    (certificate : CodeCert env U registry Γ locals τ expression demand footprint)
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    (typing : EndpointState sourceEnv U source expression assigned)
    (location : Located root typing)
    (original : VExpr) (arguments : List VExpr) (depth : Nat)
    {baseDepth : Nat} (depthEq : depth = baseDepth + location.binderPrefix.length)
    (he : expression = original.subst ((Subst.ofList arguments).liftN depth))
    (σ : Subst) (tail : Subst.lift_l (.skipN .refl depth) τ = σ)
    (baseLocals newLocals : List Nat) :
    ∃ required, Nonempty (CodeCert env U registry Γ newLocals
      ((Subst.ofList arguments).liftN depth |>.comp τ) original demand required) ∧
      Nonempty (CaptureFootprint (env := env) root registry Γ baseLocals σ arguments baseDepth depth
        (fun initial => (Closure.close typing.origin (location.environment initial)).cost) footprint required) := by
  match certificate, typing, location with
  | .seed observation formed, typing, location =>
    obtain ⟨f, ⟨h⟩, s⟩ := Obs.factorCapturesLocated (baseDepth := baseDepth) observation typing location original arguments depth depthEq he σ tail baseLocals newLocals
    exact ⟨f, ⟨.seed h formed⟩, s⟩
  | .union left right, typing, location =>
    obtain ⟨fl, ⟨hl⟩, ⟨sl⟩⟩ := CodeCert.factorCapturesLocated (baseDepth := baseDepth) left typing location original arguments depth depthEq he σ tail baseLocals newLocals
    obtain ⟨fr, ⟨hr⟩, ⟨sr⟩⟩ := CodeCert.factorCapturesLocated (baseDepth := baseDepth) right typing location original arguments depth depthEq he σ tail baseLocals newLocals
    exact ⟨fl ++ fr, ⟨.union hl hr⟩, ⟨sl.append sr⟩⟩
  | .pad source, typing, location =>
    obtain ⟨f, ⟨h⟩, s⟩ := CodeCert.factorCapturesLocated (baseDepth := baseDepth) source typing location original arguments depth depthEq he σ tail baseLocals newLocals
    exact ⟨f, ⟨.pad h⟩, s⟩
  | .familyPad source, typing, location =>
    obtain ⟨f, ⟨h⟩, s⟩ := CodeCert.factorCapturesLocated (baseDepth := baseDepth) source typing location original arguments depth depthEq he σ tail baseLocals newLocals
    exact ⟨f, ⟨.familyPad h⟩, s⟩
  | .unpad source, typing, location =>
    obtain ⟨f, ⟨h⟩, s⟩ := CodeCert.factorCapturesLocated (baseDepth := baseDepth) source typing location original arguments depth depthEq he σ tail baseLocals newLocals
    exact ⟨f, ⟨.unpad h⟩, s⟩
  | .down source, typing, location =>
    obtain ⟨f, ⟨h⟩, s⟩ := CodeCert.factorCapturesLocated (baseDepth := baseDepth) source typing location original arguments depth depthEq he σ tail baseLocals newLocals
    exact ⟨f, ⟨.down h⟩, s⟩
  | .map view source, typing, location =>
    obtain ⟨f, ⟨h⟩, s⟩ := CodeCert.factorCapturesLocated (baseDepth := baseDepth) source typing location original arguments depth depthEq he σ tail baseLocals newLocals
    exact ⟨f, ⟨.map view h⟩, s⟩
  | .select source member, typing, location =>
    obtain ⟨f, ⟨h⟩, s⟩ := CodeCert.factorCapturesLocated (baseDepth := baseDepth) source typing location original arguments depth depthEq he σ tail baseLocals newLocals
    exact ⟨f, ⟨.select h member⟩, s⟩
  | .focusMinimal source minimal bound, typing, location =>
    obtain ⟨f, ⟨h⟩, s⟩ := CodeCert.factorCapturesLocated (baseDepth := baseDepth) source typing location original arguments depth depthEq he σ tail baseLocals newLocals
    exact ⟨f, ⟨.focusMinimal h minimal bound⟩, s⟩
termination_by sizeOf certificate

theorem PiRows.factorCapturesLocated
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {Γ : List VExpr}
    {locals : List Nat} {τ : Subst} {A B : VExpr} {ambient : Profile n}
    {rows : List (Key n × Profile n)} {footprint : Footprint}
    (bodies : PiRows env U registry Γ locals τ A B ambient rows footprint)
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    (typing : EndpointState sourceEnv U (A :: source) B assigned)
    (location : Located root typing)
    (A₀ B₀ : VExpr) (arguments : List VExpr) (depth : Nat)
    {baseDepth : Nat} (depthEq : depth + 1 = baseDepth + location.binderPrefix.length)
    (hA : A = A₀.subst ((Subst.ofList arguments).liftN depth)) (hB : B = B₀.subst ((Subst.ofList arguments).liftN (depth + 1)))
    (σ : Subst) (tail : Subst.lift_l (.skipN .refl depth) τ = σ)
    (baseLocals newLocals : List Nat) :
    ∃ required, Nonempty (PiRows env U registry Γ newLocals
      ((Subst.ofList arguments).liftN depth |>.comp τ) A₀ B₀ ambient rows required) ∧
      Nonempty (CaptureFootprint (env := env) root registry Γ baseLocals σ arguments baseDepth depth
        (fun initial => (Closure.close typing.origin (location.environment initial)).cost) footprint required) := by
  match bodies, typing, location with
  | .nil, typing, location => exact ⟨[], ⟨.nil⟩, ⟨.nil⟩⟩
  | .cons guard body normal covered rest, typing, location =>
    obtain ⟨fb, ⟨hb⟩, ⟨sb⟩⟩ := CodeCert.factorCapturesLocated (baseDepth := baseDepth) body typing location B₀ arguments (depth + 1) depthEq hB σ
      (capture_tail_cons depth τ σ _ tail) baseLocals (Locals.push newLocals)
    rw [Subst.liftN, capture_realization_cons] at hb
    obtain ⟨outside, pack, ⟨so⟩⟩ := sb.underBinder normal
    obtain ⟨fr, ⟨hr⟩, ⟨sr⟩⟩ := PiRows.factorCapturesLocated (baseDepth := baseDepth) rest typing location A₀ B₀ arguments depth depthEq hA hB σ tail baseLocals newLocals
    rw [hA] at guard
    exact ⟨outside ++ fr, ⟨.cons (LambdaGuard.factorCaptures guard) hb pack covered hr⟩, ⟨so.append sr⟩⟩
termination_by sizeOf bodies
end

/-- Enter at the unchanged original endpoint. The literal template equation
is used only by inverse syntax substitution; no typing of any residual
template is created or interpreted. -/
theorem CodeCert.factorCapturesOriginal
    (certificate : CodeCert env U registry Γ locals σ expression demand footprint)
    (root : EndpointRef sourceEnv U source expression assigned)
    (template : VExpr) (arguments : List VExpr)
    (literal : expression = template.instOuter arguments) (newLocals : List Nat) :
    ∃ required, Nonempty (CodeCert env U registry Γ newLocals
      ((Subst.ofList arguments).comp σ) template demand required) ∧
      Nonempty (CaptureFootprint (env := env) root registry Γ locals σ arguments 0 0
        (fun initial => (Closure.close root.origin initial).cost) footprint required) := by
  exact CodeCert.factorCapturesLocated certificate (.ref root) .here template arguments 0
    rfl (literal.trans (instOuter_eq_subst template arguments)) σ rfl locals newLocals

/-- Realize the simultaneous result at the registered finite capture tuple.
All cuts and their original locations are unchanged by tail realization. -/
theorem CodeCert.factorNativeTemplateOriginal
    (certificate : CodeCert env U registry Γ locals σ expression demand footprint)
    (root : EndpointRef sourceEnv U source expression assigned)
    (template : VExpr) (arguments : List VExpr)
    (literal : expression = template.instOuter arguments)
    (scope : template.ClosedN arguments.length) (newLocals : List Nat) :
    ∃ required, Nonempty (CodeCert env U registry Γ newLocals
      (nativeCaptureSubst (arguments.map (·.subst σ))) template demand required) ∧
      Nonempty (CaptureFootprint (env := env) root registry Γ locals σ arguments 0 0
        (fun initial => (Closure.close root.origin initial).cost) footprint required) := by
  obtain ⟨required, ⟨factored⟩, cuts⟩ :=
    CodeCert.factorCapturesOriginal certificate root template arguments literal newLocals
  refine ⟨required, ⟨factored.realizePrefix scope _ ?_⟩, cuts⟩
  intro index bound
  simp only [Subst.comp, Subst.ofList, nativeCaptureSubst, List.length_map]
  rw [dif_pos bound, dif_pos bound]
  simp only [List.getElem_map]


end Lean4Lean.AnchoredSource.Adapted.OriginalFactorCut
