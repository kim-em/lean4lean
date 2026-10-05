import Lean4Lean.Theory.Typing.AnchoredNativeRhsBeta
import Lean4Lean.Theory.Typing.AnchoredNativeDeclaredBody
import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceBetaExpansion
import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceVariableRule
import Lean4Lean.Theory.Typing.AnchoredBetaContraction
import Lean4Lean.Theory.Typing.NativeTelescope

/-! Opening a native RHS adds only formal-variable applications. The finite
head-beta trace retains those lookups explicitly. Its observation expansion
uses the original body observations and the existing fitting entries; it does
not introduce a new opaque source head. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

private theorem expand_app
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {target : List VExpr} {locals : List Nat} {σ : Subst} {available : Valuation}
    {f g argument : VExpr}
    (changeHead : ∀ {n} {p : Profile n} {footprint},
      Obs env U registry target locals σ g p footprint → footprint.Available available →
      ∃ required, Nonempty (Obs env U registry target locals σ f p required) ∧ required.Available available)
    {n : Nat} {p : Profile n} {footprint : Footprint}
    (observation : Obs env U registry target locals σ (.app g argument) p footprint)
    (resources : footprint.Available available) :
    ∃ required, Nonempty (Obs env U registry target locals σ (.app f argument) p required) ∧
      required.Available available := by
  match observation with
  | .empty => exact ⟨[], ⟨.empty⟩, fun _ _ h => nomatch h⟩
  | .app fn arg adapter admitted =>
    obtain ⟨required, ⟨fn'⟩, fresh⟩ := changeHead fn
      (fun i need hm => resources i need (List.mem_append_left _ hm))
    exact ⟨_, ⟨.app fn' arg adapter admitted⟩,
      fun i need hm => (List.mem_append.mp hm).elim (fresh i need)
        (fun h => resources i need (List.mem_append_right _ h))⟩
  | .union left right =>
    obtain ⟨lf, ⟨l⟩, hl⟩ := expand_app changeHead left
      (fun i need hm => resources i need (List.mem_append_left _ hm))
    obtain ⟨rf, ⟨r⟩, hr⟩ := expand_app changeHead right
      (fun i need hm => resources i need (List.mem_append_right _ hm))
    exact ⟨lf ++ rf, ⟨.union l r⟩, fun i need hm =>
      (List.mem_append.mp hm).elim (hl i need) (hr i need)⟩
  | .view child view =>
    obtain ⟨required, ⟨next⟩, fresh⟩ := expand_app changeHead child resources
    exact ⟨required, ⟨.view next view⟩, fresh⟩
  | .pad child =>
    obtain ⟨required, ⟨next⟩, fresh⟩ := expand_app changeHead child resources
    exact ⟨required, ⟨.pad next⟩, fresh⟩
  | .unpad child =>
    obtain ⟨required, ⟨next⟩, fresh⟩ := expand_app changeHead child resources
    exact ⟨required, ⟨.unpad next⟩, fresh⟩
  | .rowShift child =>
    obtain ⟨required, ⟨next⟩, fresh⟩ := expand_app changeHead child resources
    exact ⟨required, ⟨.rowShift next⟩, fresh⟩
termination_by sizeOf observation
decreasing_by all_goals simp_wf; omega

/-- The predecessor theorem is used only on the formal argument's lookup
formation. In the intended native use, its finite observations come from the
stored fitting certificates of the constructor-capture telescope. -/
theorem FormalHeadBeta.expand
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hsource : sourceEnv.Ordered)
    (hle : sourceEnv ≤ env)
    (earlier : ∀ {Γ e e' A}, sourceEnv.IsDefEqStrong U Γ e e' A →
      GradedJoint env U registry Γ e e' A)
    {source target : List VExpr} (hSource : OnCtx source (sourceEnv.IsType U))
    {locals : List Nat} {σ : Subst} {available : Valuation}
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (fits : PairedFits env U registry source target locals σ σ available)
    {left right : VExpr} (step : FormalHeadBeta source left right)
    {demand : Profile n} {footprint : Footprint}
    (observation : Obs env U registry target locals σ right demand footprint)
    (resources : footprint.Available available) :
    ∃ required, Nonempty (Obs env U registry target locals σ left demand required) ∧
      required.Available available := by
  induction step generalizing n footprint with
  | @beta index A body lookup =>
    have typed : sourceEnv.HasType U source (.bvar index) A := .bvar lookup
    obtain ⟨level, formed⟩ := typed.isType hsource hSource
    have joint := GradedJoint.bvar henv hscoped lookup (earlier (formed.strong hsource hSource))
    exact observation.betaExpand henv joint (typed.mono hle) closed hTarget substitutions fits resources
  | app head ih => exact expand_app (fun obs res => ih obs res) observation resources

theorem FormalBetaTrace.expand
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hsource : sourceEnv.Ordered)
    (hle : sourceEnv ≤ env)
    (earlier : ∀ {Γ e e' A}, sourceEnv.IsDefEqStrong U Γ e e' A →
      GradedJoint env U registry Γ e e' A)
    {source target : List VExpr} (hSource : OnCtx source (sourceEnv.IsType U))
    {locals : List Nat} {σ : Subst} {available : Valuation}
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (fits : PairedFits env U registry source target locals σ σ available)
    {left right : VExpr} (trace : FormalBetaTrace source left right)
    {demand : Profile n} {footprint : Footprint}
    (observation : Obs env U registry target locals σ right demand footprint)
    (resources : footprint.Available available) :
    ∃ required, Nonempty (Obs env U registry target locals σ left demand required) ∧
      required.Available available := by
  induction trace generalizing footprint with
  | refl => exact ⟨footprint, ⟨observation⟩, resources⟩
  | next head tail ih =>
    obtain ⟨required, ⟨middle⟩, hm⟩ := ih observation resources
    exact head.expand henv hscoped hsource hle earlier hSource closed hTarget substitutions fits middle hm

end Lean4Lean.AnchoredSource.Adapted

namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles
set_option backward.isDefEq.respectTransparency false

theorem TypedBetaTrace.contractLeft (henv : env.Ordered)
    (trace : TypedBetaTrace env U Γ type first last)
    (otherTyped : env.HasType U Γ other type)
    (related : Related env U registry Γ first other type value support) :
    Related env U registry Γ last other type value support := by
  induction trace with
  | refl => exact related
  | next head equal _ ih =>
    exact ih (Related.contractHeadBeta henv head .refl equal otherTyped related)

theorem TypedBetaTrace.contractRight (henv : env.Ordered)
    (trace : TypedBetaTrace env U Γ type first last)
    (otherTyped : env.HasType U Γ other type)
    (related : Related env U registry Γ other first type value support) :
    Related env U registry Γ other last type value support := by
  induction trace with
  | refl => exact related
  | next head equal _ ih =>
    exact ih (Related.contractHeadBeta henv .refl head otherTyped equal related)

end Lean4Lean.AnchoredSemantics

namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

/-- The actual source result remains the eta-applied RHS. The separately
named `related` field is the target semantics of the contracted literal RHS.
There is no claim of source-observation contraction in this package. -/
structure DeclaredRhsResult (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (locals : List Nat) (σ τ : Subst) (available : Valuation)
    (domains : List VExpr) (body result : VExpr) (demand : Profile n) where
  opened : GradedTransferResult env U registry target locals σ τ available
    (nativeEtaBody domains.length (wrapLams domains body))
    (nativeEtaBody domains.length (wrapLams domains body)) result demand
  related : Related env U registry target (body.subst σ) (body.subst τ) (result.subst σ)
    (raiseProfile opened.rank opened.bound demand) opened.support

private theorem resultFormation {env : VEnv} {U : Nat} {source domains : List VExpr} {result : VExpr}
    (henv : env.Ordered)
    (formation : env.IsType U source (wrapForalls domains result)) :
    env.IsType U (domains.reverse ++ source) result := by
  induction domains generalizing source with
  | nil => exact formation
  | cons A domains ih =>
    have next := (formation.forallE_inv henv).2
    simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using ih next

/-- Interpret a freshly assembled eta-applied RHS at the strict predecessor
rule stage, then contract its finite typed beta trace. Only formal-variable
arguments are added to the source observations. Existing body and capture
certificate dependencies remain in the same fitting valuation. -/
theorem HasTypeStrong.declaredRhs
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hsource : sourceEnv.Ordered)
    (hle : sourceEnv ≤ env)
    (earlier : ∀ {Γ left right type}, sourceEnv.IsDefEqStrong U Γ left right type →
      GradedJoint env U registry Γ left right type)
    {source target : List VExpr} {domains : List VExpr} {body result : VExpr}
    (hSource : OnCtx source (sourceEnv.IsType U))
    (original : sourceEnv.HasTypeStrong U source (wrapLams domains body)
      (wrapForalls domains result) structural)
    (formation : sourceEnv.IsDefEqStrong U source (wrapForalls domains result)
      (wrapForalls domains result) (.sort level))
    {locals : List Nat} {σ τ : Subst} {available : Valuation}
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ (domains.reverse ++ source))
    (fits : PairedFits env U registry (domains.reverse ++ source) target locals σ τ available)
    {demand : Profile n} {footprint : Footprint}
    (observation : Obs env U registry target locals σ body demand footprint)
    (resources : footprint.Available available) :
    Nonempty (DeclaredRhsResult env U registry target locals σ τ available domains body result demand) := by
  obtain ⟨hFullSource, openedTyping⟩ := HasType.native_open hsource hSource original.refl.defeq
  have openedStrong := openedTyping.strong hsource hFullSource
  obtain ⟨expandedFootprint, ⟨expanded⟩, expandedAvailable⟩ :=
    (FormalBetaTrace.nativeRhs domains body source).expand henv hscoped hsource hle earlier
      hFullSource closed hTarget substitutions.left fits.left observation resources
  obtain ⟨opened⟩ := (earlier openedStrong target locals σ τ available closed hTarget
    substitutions fits).1 expanded expandedAvailable
  obtain ⟨leftNatural, leftOriginal, _, leftPath, leftBodyTyped⟩ :=
    HasTypeStrong.declaredBody henv hscoped hle earlier original formation σ hTarget substitutions.left
  obtain ⟨rightNatural, rightOriginal, _, rightPath, rightBodyTyped⟩ :=
    HasTypeStrong.declaredBody henv hscoped hle earlier original formation τ hTarget
      (substitutions.right henv hTarget)
  have hFull := substitutions.wf
  have leftTrace := (TypedBetaTrace.nativeRhs henv domains hFull
    (leftOriginal.defeq.mono hle)).subst henv hTarget substitutions.left |>.cast leftPath
  have rightTrace := (TypedBetaTrace.nativeRhs henv domains hFull
    (rightOriginal.defeq.mono hle)).subst henv hTarget
      (substitutions.right henv hTarget) |>.cast rightPath
  obtain ⟨resultLevel, formedResult⟩ := resultFormation hsource ⟨level, formation.defeq⟩
  have resultPair := (formedResult.mono hle).substDF henv hFull hTarget substitutions
  have rightTrace := rightTrace.cast (TypeConversion.single resultPair.symm)
  have rightBodyTyped := (TypeConversion.single resultPair.symm).cast rightBodyTyped
  have next := leftTrace.contractLeft henv rightTrace.firstTyped opened.related
  exact ⟨{ opened := opened
           related := rightTrace.contractRight henv leftBodyTyped next }⟩

end Lean4Lean.AnchoredSource.Adapted
