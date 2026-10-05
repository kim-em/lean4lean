import Lean4Lean.Theory.Typing.AnchoredBoundedBetaExpansion
import Lean4Lean.Theory.Typing.AnchoredBoundedDeclaredBody
import Lean4Lean.Theory.Typing.AnchoredNativeRhsOpening

/-! Native RHS opening at fixed stage fuel. Formal-variable beta expansion,
the actual predecessor Strong call, and exact declared-body conversion all
consume and return bounded source observations/certificates. -/
namespace Lean4Lean.AnchoredSource.Adapted.Staged
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

private theorem expand_app
    {current : Name → Bool} {fuel : Nat}
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {target : List VExpr} {locals : List Nat} {σ : Subst} {available : Valuation}
    {f g argument : VExpr}
    (changeHead : ∀ {n} {p : Profile n} {footprint},
      ∀ observation : Obs env U registry target locals σ g p footprint,
      observation.nativeDepth current ≤ fuel → footprint.Available available →
      ∃ required, ∃ result : Obs env U registry target locals σ f p required,
        required.Available available ∧ result.nativeDepth current ≤ fuel)
    {n : Nat} {p : Profile n} {footprint : Footprint}
    (observation : Obs env U registry target locals σ (.app g argument) p footprint)
    (bound : observation.nativeDepth current ≤ fuel)
    (resources : footprint.Available available) :
    ∃ required, ∃ result : Obs env U registry target locals σ (.app f argument) p required,
      required.Available available ∧ result.nativeDepth current ≤ fuel := by
  match observation with
  | .empty => exact ⟨[], .empty, (fun _ _ h => nomatch h), by simp only [Obs.nativeDepth]; omega⟩
  | .app fn arg adapter admitted =>
    have bounds := Nat.max_le.mp (show max _ _ ≤ fuel from by simpa only [Obs.nativeDepth] using bound)
    obtain ⟨required, fn', fresh, fnBound⟩ := changeHead fn bounds.1
      (fun i need hm => resources i need (List.mem_append_left _ hm))
    exact ⟨_, .app fn' arg adapter admitted,
      (fun i need hm => (List.mem_append.mp hm).elim (fresh i need)
        (fun h => resources i need (List.mem_append_right _ h))),
      by simpa only [Obs.nativeDepth] using Nat.max_le.mpr ⟨fnBound, bounds.2⟩⟩
  | .union left right =>
    have bounds := Nat.max_le.mp (show max _ _ ≤ fuel from by simpa only [Obs.nativeDepth] using bound)
    obtain ⟨lf, l, hl, lb⟩ := expand_app changeHead left bounds.1
      (fun i need hm => resources i need (List.mem_append_left _ hm))
    obtain ⟨rf, r, hr, rb⟩ := expand_app changeHead right bounds.2
      (fun i need hm => resources i need (List.mem_append_right _ hm))
    exact ⟨lf ++ rf, .union l r, (fun i need hm =>
      (List.mem_append.mp hm).elim (hl i need) (hr i need)),
      by simpa only [Obs.nativeDepth] using Nat.max_le.mpr ⟨lb, rb⟩⟩
  | .view child view =>
    obtain ⟨required, next, fresh, nextBound⟩ := expand_app changeHead child
      (by simpa only [Obs.nativeDepth] using bound) resources
    exact ⟨required, .view next view, fresh, by simpa only [Obs.nativeDepth] using nextBound⟩
  | .pad child =>
    obtain ⟨required, next, fresh, nextBound⟩ := expand_app changeHead child
      (by simpa only [Obs.nativeDepth] using bound) resources
    exact ⟨required, .pad next, fresh, by simpa only [Obs.nativeDepth] using nextBound⟩
  | .unpad child =>
    obtain ⟨required, next, fresh, nextBound⟩ := expand_app changeHead child
      (by simpa only [Obs.nativeDepth] using bound) resources
    exact ⟨required, .unpad next, fresh, by simpa only [Obs.nativeDepth] using nextBound⟩
  | .rowShift child =>
    obtain ⟨required, next, fresh, nextBound⟩ := expand_app changeHead child
      (by simpa only [Obs.nativeDepth] using bound) resources
    exact ⟨required, .rowShift next, fresh, by simpa only [Obs.nativeDepth] using nextBound⟩
termination_by sizeOf observation
decreasing_by all_goals simp_wf; omega

/-- The predecessor theorem is used only on the formal argument's lookup
formation. In the intended native use, its finite observations come from the
stored fitting certificates of the constructor-capture telescope. -/
theorem FormalHeadBeta.expand
    {current : Name → Bool} {fuel : Nat}
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hsource : sourceEnv.Ordered)
    (hle : sourceEnv ≤ env)
    (earlier : ∀ {Γ e e' A}, sourceEnv.IsDefEqStrong U Γ e e' A →
      Joint current fuel env U registry Γ e e' A)
    {source target : List VExpr} (hSource : OnCtx source (sourceEnv.IsType U))
    {locals : List Nat} {σ : Subst} {available : Valuation}
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (fits : PairedFits current fuel env U registry source target locals σ σ available)
    {left right : VExpr} (step : FormalHeadBeta source left right)
    {demand : Profile n} {footprint : Footprint}
    (observation : Obs env U registry target locals σ right demand footprint)
    (bound : observation.nativeDepth current ≤ fuel)
    (resources : footprint.Available available) :
    ∃ required, ∃ result : Obs env U registry target locals σ left demand required,
      required.Available available ∧ result.nativeDepth current ≤ fuel := by
  induction step generalizing n footprint with
  | @beta index A body lookup =>
    have typed : sourceEnv.HasType U source (.bvar index) A := .bvar lookup
    obtain ⟨level, formed⟩ := typed.isType hsource hSource
    have transfer : Transfer current fuel env U registry target locals σ σ available
        (.bvar index) (.bvar index) A := fun obs bounded fresh =>
      bvarTransfer henv hscoped lookup (earlier (formed.strong hsource hSource)) closed hTarget
        substitutions fits obs bounded fresh
    exact observation.betaExpandBounded henv transfer (typed.mono hle) closed hTarget
      substitutions fits bound resources
  | app head ih => exact expand_app (fun obs bounded res => ih obs bounded res) observation bound resources

theorem FormalBetaTrace.expand
    {current : Name → Bool} {fuel : Nat}
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hsource : sourceEnv.Ordered)
    (hle : sourceEnv ≤ env)
    (earlier : ∀ {Γ e e' A}, sourceEnv.IsDefEqStrong U Γ e e' A →
      Joint current fuel env U registry Γ e e' A)
    {source target : List VExpr} (hSource : OnCtx source (sourceEnv.IsType U))
    {locals : List Nat} {σ : Subst} {available : Valuation}
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (fits : PairedFits current fuel env U registry source target locals σ σ available)
    {left right : VExpr} (trace : FormalBetaTrace source left right)
    {demand : Profile n} {footprint : Footprint}
    (observation : Obs env U registry target locals σ right demand footprint)
    (bound : observation.nativeDepth current ≤ fuel)
    (resources : footprint.Available available) :
    ∃ required, ∃ result : Obs env U registry target locals σ left demand required,
      required.Available available ∧ result.nativeDepth current ≤ fuel := by
  induction trace generalizing footprint with
  | refl => exact ⟨footprint, observation, resources, bound⟩
  | next head tail ih =>
    obtain ⟨required, middle, hm, middleBound⟩ := ih observation bound resources
    exact FormalHeadBeta.expand henv hscoped hsource hle earlier hSource closed hTarget substitutions fits head middle middleBound hm

structure DeclaredRhsResult (current : Name → Bool) (fuel : Nat) (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (locals : List Nat) (σ τ : Subst) (available : Valuation)
    (domains : List VExpr) (body result : VExpr) (demand : Profile n) where
  opened : Result current fuel env U registry target locals σ τ available
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
    {current : Name → Bool} {fuel : Nat}
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hsource : sourceEnv.Ordered)
    (hle : sourceEnv ≤ env)
    (earlier : ∀ {Γ left right type}, sourceEnv.IsDefEqStrong U Γ left right type →
      Joint current fuel env U registry Γ left right type)
    {source target : List VExpr} {domains : List VExpr} {body result : VExpr}
    (hSource : OnCtx source (sourceEnv.IsType U))
    (original : sourceEnv.HasTypeStrong U source (wrapLams domains body)
      (wrapForalls domains result) structural)
    (formation : sourceEnv.IsDefEqStrong U source (wrapForalls domains result)
      (wrapForalls domains result) (.sort level))
    {locals : List Nat} {σ τ : Subst} {available : Valuation}
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ (domains.reverse ++ source))
    (fits : PairedFits current fuel env U registry (domains.reverse ++ source) target locals σ τ available)
    {demand : Profile n} {footprint : Footprint}
    (observation : Obs env U registry target locals σ body demand footprint)
    (observationBound : observation.nativeDepth current ≤ fuel)
    (resources : footprint.Available available) :
    Nonempty (DeclaredRhsResult current fuel env U registry target locals σ τ available domains body result demand) := by
  obtain ⟨hFullSource, openedTyping⟩ := HasType.native_open hsource hSource original.refl.defeq
  have openedStrong := openedTyping.strong hsource hFullSource
  obtain ⟨expandedFootprint, expanded, expandedAvailable, expandedBound⟩ :=
    FormalBetaTrace.expand henv hscoped hsource hle earlier hFullSource closed hTarget
      substitutions.left fits.left (FormalBetaTrace.nativeRhs domains body source)
      observation observationBound resources
  obtain ⟨opened⟩ := (earlier openedStrong target locals σ τ available closed hTarget
    substitutions fits).1 expanded expandedBound expandedAvailable
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


end Lean4Lean.AnchoredSource.Adapted.Staged
