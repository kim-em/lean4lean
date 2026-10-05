import Lean4Lean.Theory.Typing.AnchoredEtaFootprint
import Lean4Lean.Theory.Typing.AnchoredSourceRenaming
import Lean4Lean.Theory.Typing.AnchoredApplicationTrace
import Lean4Lean.Theory.Typing.AnchoredSourceFundamental
import Lean4Lean.Theory.Typing.AnchoredFunctionDomain

/-! The direct application case of source eta contraction. Reflection removes
the unused source binder; argument normalization preserves the lambda's actual
input and the reflected function's exact external footprint. Converted raw
domains are handled only when the required concrete domain capability is given.
Singleton body observations may use arbitrary output views and grade changes.
The converted-domain capability still requires its original-typing producer. -/

namespace Lean4Lean.AnchoredSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

/-- The original application's admission supplies the anchor change. The
original binder pack supplies the input change, including all empty leaves. -/
theorem Obs.eta_app_input {lambdaKey appKey : Key n} {output : Atom n}
    (henv : env.Ordered)
    (function : Obs env U registry Γ (Locals.push locals) (σ.cons lambdaKey.anchor)
      f.lift (Profile.fn appKey output) functionFootprint)
    (argument : Obs env U registry Γ (Locals.push locals) (σ.cons lambdaKey.anchor)
      (.bvar 0) appKey.input argumentFootprint)
    (admitted : Admitted env U registry Γ appKey lambdaKey.anchor lambdaKey.anchor)
    (pack : BinderPack n lambdaKey.input (functionFootprint ++ argumentFootprint) outside) :
    Nonempty (Obs env U registry Γ locals σ f
      (Profile.fn (domainKey lambdaKey appKey.domain) output) outside) := by
  obtain ⟨required, ⟨reflected⟩, hrequired⟩ :=
    function.reflectSource (.skip .refl) lift_eq_lift' locals
  change Obs env U registry Γ locals σ f (Profile.fn appKey output) required at reflected
  rw [hrequired] at pack
  let trace := VariableTrace.ofObs argument
  obtain ⟨hinput, hbounds, houtside⟩ := pack.etaFootprint trace
  have anchored := Obs.view reflected (AtomView.reanchor (output := output) admitted)
  have adjusted := anchored.inputFromVariableTrace henv trace hbounds
  have hkey : inputKey (reanchorKey appKey lambdaKey.anchor)
      (argumentFootprint.atGrade n) = domainKey lambdaKey appKey.domain := by
    rw [← hinput]
    cases lambdaKey
    rfl
  rw [hkey, ← houtside] at adjusted
  exact ⟨adjusted⟩

/-- Same-domain eta application contraction requires no type-coherence or
new semantic capability. The lambda domain certificate's footprint is outside
this body's footprint calculation. -/
theorem Obs.eta_app_sameDomain {lambdaKey appKey : Key n} {output : Atom n}
    (henv : env.Ordered)
    (function : Obs env U registry Γ (Locals.push locals) (σ.cons lambdaKey.anchor)
      f.lift (Profile.fn appKey output) functionFootprint)
    (argument : Obs env U registry Γ (Locals.push locals) (σ.cons lambdaKey.anchor)
      (.bvar 0) appKey.input argumentFootprint)
    (admitted : Admitted env U registry Γ appKey lambdaKey.anchor lambdaKey.anchor)
    (pack : BinderPack n lambdaKey.input (functionFootprint ++ argumentFootprint) outside)
    (sameDomain : appKey.domain = lambdaKey.domain) :
    Nonempty (Obs env U registry Γ locals σ f (Profile.fn lambdaKey output) outside) := by
  simpa only [sameDomain, domainKey] using
    Obs.eta_app_input henv function argument admitted pack

/-- The remaining converted-domain step is exactly this concrete raw path
and finite type capability at a support typing the lambda's input. No callback
for arbitrary source observations is required by this consumer. -/
theorem Obs.eta_app_domainBridge {lambdaKey appKey : Key n} {output : Atom n}
    (henv : env.Ordered)
    (function : Obs env U registry Γ (Locals.push locals) (σ.cons lambdaKey.anchor)
      f.lift (Profile.fn appKey output) functionFootprint)
    (argument : Obs env U registry Γ (Locals.push locals) (σ.cons lambdaKey.anchor)
      (.bvar 0) appKey.input argumentFootprint)
    (admitted : Admitted env U registry Γ appKey lambdaKey.anchor lambdaKey.anchor)
    (pack : BinderPack n lambdaKey.input (functionFootprint ++ argumentFootprint) outside)
    (path : TypeConversion env U Γ appKey.domain lambdaKey.domain)
    (typed : lambdaKey.input.HasType support)
    (formed : support.HasType (.sort true))
    (bridge : TypeRelated env U registry Γ appKey.domain lambdaKey.domain support) :
    Nonempty (Obs env U registry Γ locals σ f (Profile.fn lambdaKey output) outside) := by
  obtain ⟨adjusted⟩ := Obs.eta_app_input henv function argument admitted pack
  have view := AtomView.domainRekey (key := domainKey lambdaKey appKey.domain)
    (output := output) path typed formed bridge
  simpa only [Profile.fn, domainKey] using Nonempty.intro (Obs.view adjusted view)

/-- Contract an eta body through every source output closure. Its unique
application leaf may be at a different grade from the enclosing lambda. The
common grade is used only internally; the conclusion has the original key's
input, anchor and grade, the original output, and the exact external footprint.
Only the application's raw domain remains to be aligned. -/
theorem Obs.eta_body {lambdaKey : Key n} {output : Atom n}
    (henv : env.Ordered)
    (body : Obs env U registry Γ (Locals.push locals) (σ.cons lambdaKey.anchor)
      (.app f.lift (.bvar 0)) (.singleton output) bodyFootprint)
    (pack : BinderPack n lambdaKey.input bodyFootprint outside) :
    ∃ domain, Nonempty (Obs env U registry Γ locals σ f
      (Profile.fn (domainKey lambdaKey domain) output) outside) := by
  obtain ⟨origin, ⟨path⟩, hbody⟩ := body.application_factor output rfl
  obtain ⟨required, ⟨reflected⟩, hrequired⟩ :=
    origin.function.reflectSource (.skip .refl) lift_eq_lift' locals
  change Obs env U registry Γ locals σ f (Profile.fn origin.key origin.output) required at reflected
  rw [hbody, hrequired] at pack
  let argument := VariableTrace.ofObs origin.argument
  obtain ⟨hinput, hbounds, houtside⟩ := pack.etaFootprint argument
  let N := max path.height argument.height
  have hp : path.height ≤ N := Nat.le_max_left _ _
  have ha : argument.height ≤ N := Nat.le_max_right _ _
  have hn : n ≤ N := Nat.le_trans path.bounds.2 hp
  have hr : origin.rank ≤ N := Nat.le_trans path.bounds.1 hp
  let targetKey := domainKey lambdaKey origin.key.domain
  let highKey := raiseKey N hn targetKey
  have admission : Admitted env U registry Γ origin.key lambdaKey.anchor lambdaKey.anchor :=
    origin.admitted
  have anchored := Obs.view reflected (AtomView.reanchor (output := origin.output) admission)
  have lifted := anchored.raise (Nat.succ_le_succ hr)
  rw [raiseProfile_singleton] at lifted
  have exposed := Obs.view lifted
    (functionGradeView hr (reanchorKey origin.key lambdaKey.anchor) origin.output)
  have forward : ProfileView env U registry Γ highKey.input
      (raiseKey N hr (reanchorKey origin.key lambdaKey.anchor)).input := by
    simpa only [highKey, targetKey, raiseKey, domainKey, reanchorKey,
      hinput, Footprint.atGrade_raise hn hbounds] using argument.normalize N ha
  have adapted := Obs.view exposed (AtomView.input forward (forward.inverse henv))
  have hkey : inputKey (raiseKey N hr (reanchorKey origin.key lambdaKey.anchor))
      highKey.input = highKey := by
    cases lambdaKey
    rfl
  rw [hkey] at adapted
  have changed := Obs.view adapted (AtomView.fn highKey (path.normalize N hp))
  have lowered := Obs.view changed ((functionGradeView hn targetKey output).inverse henv)
  refine ⟨origin.key.domain, ⟨Obs.lower (Nat.succ_le_succ hn) ?_⟩⟩
  simpa only [targetKey, Profile.fn, raiseProfile_singleton, houtside] using lowered

/-- The original function-typing child's joint result supplies the remaining
domain alignment. It is applied to the normalized observation just constructed,
at the unchanged external valuation. No adequacy theorem is called on a new
raw typing derivation or conversion path. -/
theorem Obs.eta_body_of_joint {lambdaKey : Key n} {output : Atom n}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (originalFunction : Joint env U registry source f f (.forallE A B))
    (hΓ : OnCtx Γ (env.IsType U))
    (substitutions : Ctx.SubstEq env U Γ σ τ source)
    (fits : Fits env U registry source Γ locals σ τ available)
    (guard : LambdaGuard env U registry Γ σ A lambdaKey lambdaSupport)
    (body : Obs env U registry Γ (Locals.push locals) (σ.cons lambdaKey.anchor)
      (.app f.lift (.bvar 0)) (.singleton output) bodyFootprint)
    (pack : BinderPack n lambdaKey.input bodyFootprint outside)
    (resources : outside.Available available) :
    Nonempty (Obs env U registry Γ locals σ f (Profile.fn lambdaKey output) outside) := by
  obtain ⟨domain, ⟨normalized⟩⟩ := body.eta_body henv pack
  obtain ⟨transferred⟩ :=
    (originalFunction Γ locals σ τ available hΓ substitutions fits).1 normalized resources
  obtain ⟨support, typed, _, path, bridge⟩ :=
    transferred.related.fn_domain_alignment henv hscoped hΓ
  obtain ⟨selected, minimal, selectedTyped, _, selectedBridge⟩ :=
    TypeRelated.compose_support henv typed guard.inputTyped bridge
      (guard.domains.symm henv guard.inputTyped.wf_type)
  have change := AtomView.domainRekey (key := domainKey lambdaKey domain) (output := output)
    (path.trans guard.path.symm) selectedTyped minimal.formation selectedBridge
  simpa only [Profile.fn, domainKey] using Nonempty.intro (Obs.view normalized change)

/-- Source eta contraction at the original demand, under the fixed valuation.
All outer observation closures are retained. A lambda's domain-certificate
leaves may be discarded, while no new source resources are requested. The
only induction premise is the original function child's concrete joint result. -/
theorem Obs.eta_contract
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (originalFunction : Joint env U registry source f f (.forallE A B))
    (hΓ : OnCtx Γ (env.IsType U))
    (substitutions : Ctx.SubstEq env U Γ σ τ source)
    (fits : Fits env U registry source Γ locals σ τ available)
    (observation : Obs env U registry Γ locals σ (.lam A (.app f.lift (.bvar 0))) demand footprint)
    (resources : footprint.Available available) :
    ∃ required, Nonempty (Obs env U registry Γ locals σ f demand required) ∧
      required.Available available := by
  match observation with
  | .empty => exact ⟨[], ⟨.empty⟩, fun _ _ h => by cases h⟩
  | .lam domain guard body pack =>
    have outsideAvailable := fun j need hm => resources j need (List.mem_append_right _ hm)
    exact ⟨_, body.eta_body_of_joint henv hscoped originalFunction hΓ substitutions fits
      guard pack outsideAvailable, outsideAvailable⟩
  | .union left right =>
    obtain ⟨fl, ⟨hl⟩, hfl⟩ := left.eta_contract henv hscoped originalFunction hΓ substitutions fits
      (fun j need hm => resources j need (List.mem_append_left _ hm))
    obtain ⟨fr, ⟨hr⟩, hfr⟩ := right.eta_contract henv hscoped originalFunction hΓ substitutions fits
      (fun j need hm => resources j need (List.mem_append_right _ hm))
    refine ⟨fl ++ fr, ⟨.union hl hr⟩, ?_⟩
    intro j need hm
    exact (List.mem_append.mp hm).elim (hfl j need) (hfr j need)
  | .view source change =>
    obtain ⟨required, ⟨result⟩, available⟩ :=
      source.eta_contract henv hscoped originalFunction hΓ substitutions fits resources
    exact ⟨required, ⟨.view result change⟩, available⟩
  | .pad source =>
    obtain ⟨required, ⟨result⟩, available⟩ :=
      source.eta_contract henv hscoped originalFunction hΓ substitutions fits resources
    exact ⟨required, ⟨.pad result⟩, available⟩
  | .unpad source =>
    obtain ⟨required, ⟨result⟩, available⟩ :=
      source.eta_contract henv hscoped originalFunction hΓ substitutions fits resources
    exact ⟨required, ⟨.unpad result⟩, available⟩
  | .rowShift source =>
    obtain ⟨required, ⟨result⟩, available⟩ :=
      source.eta_contract henv hscoped originalFunction hΓ substitutions fits resources
    exact ⟨required, ⟨.rowShift result⟩, available⟩
termination_by sizeOf observation

end Lean4Lean.AnchoredSource
