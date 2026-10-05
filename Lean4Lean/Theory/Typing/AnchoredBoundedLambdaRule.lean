import Lean4Lean.Theory.Typing.AnchoredBoundedLambdaTransfer
import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceGradedClosures
import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceGradedEmpty

/-! The original lambda-rule children handle every finite observation of
the source lambda, including views and changes of grade. -/
namespace Lean4Lean.AnchoredSource.Adapted.Staged
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false
variable {current : Name → Bool} {fuel : Nat}

private theorem lambda_observer
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {source target : List VExpr} {locals : List Nat} {σ τ : Subst}
    {available : Valuation} {A A' B body other : VExpr}
    {domainLevel bodyLevel : VLevel} {demand : Profile n} {footprint : Footprint}
    (originalDomain : Joint current fuel env U registry source A A' (.sort domainLevel))
    (originalBody : Joint current fuel env U registry (A :: source) body other B)
    (originalCodomain : Joint current fuel env U registry (A :: source) B B (.sort bodyLevel))
    (domains : env.IsDefEq U source A A' (.sort domainLevel))
    (codomain : env.HasType U (A :: source) B (.sort bodyLevel))
    (bodies : env.IsDefEq U (A :: source) body other B)
    (rightBody : env.HasType U (A' :: source) other B)
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (fits : PairedFits current fuel env U registry source target locals σ τ available)
    (observation : Obs env U registry target locals σ (.lam A body) demand footprint)
    (bound : observation.nativeDepth current ≤ fuel)
    (resources : footprint.Available available) :
    Nonempty (Result current fuel env U registry target locals σ τ available
      (.lam A body) (.lam A' other) (.forallE A B) demand) := by
  match observation with
  | .empty => exact ⟨.empty⟩
  | .lam domain guard body pack covered =>
    have bounds := Nat.max_le.mp (show max (domain.nativeDepth current) (body.nativeDepth current) ≤ fuel by simpa only [Obs.nativeDepth] using bound)
    exact Obs.lam_transfer henv hscoped domain guard body pack covered
      originalDomain originalBody originalCodomain closed domains codomain bodies rightBody
      hTarget substitutions fits bounds.1 bounds.2
      (fun i need hm => resources i need (List.mem_append_left _ hm))
      (fun i need hm => resources i need (List.mem_append_right _ hm))
  | .union left right =>
    have bounds := Nat.max_le.mp (show max (left.nativeDepth current) (right.nativeDepth current) ≤ fuel by simpa only [Obs.nativeDepth] using bound)
    obtain ⟨a⟩ := lambda_observer henv hscoped originalDomain originalBody originalCodomain
      domains codomain bodies rightBody closed hTarget substitutions fits left bounds.1
      (fun i need hm => resources i need (List.mem_append_left _ hm))
    obtain ⟨b⟩ := lambda_observer henv hscoped originalDomain originalBody originalCodomain
      domains codomain bodies rightBody closed hTarget substitutions fits right bounds.2
      (fun i need hm => resources i need (List.mem_append_right _ hm))
    exact ⟨a.union henv hscoped hTarget b⟩
  | .view source change =>
    obtain ⟨a⟩ := lambda_observer henv hscoped originalDomain originalBody originalCodomain
      domains codomain bodies rightBody closed hTarget substitutions fits source (by simpa only [Obs.nativeDepth] using bound) resources
    exact ⟨a.view henv hscoped hTarget change⟩
  | .pad source =>
    obtain ⟨a⟩ := lambda_observer henv hscoped originalDomain originalBody originalCodomain
      domains codomain bodies rightBody closed hTarget substitutions fits source (by simpa only [Obs.nativeDepth] using bound) resources
    exact ⟨a.pad henv hscoped hTarget⟩
  | .unpad source =>
    obtain ⟨a⟩ := lambda_observer henv hscoped originalDomain originalBody originalCodomain
      domains codomain bodies rightBody closed hTarget substitutions fits source (by simpa only [Obs.nativeDepth] using bound) resources
    exact ⟨a.unpad⟩
  | @Obs.rowShift _ _ _ _ _ _ _ _ key output _ source =>
    obtain ⟨a⟩ := lambda_observer henv hscoped originalDomain originalBody originalCodomain
      domains codomain bodies rightBody closed hTarget substitutions fits source (by simpa only [Obs.nativeDepth] using bound) resources
    have padded := a.pad henv hscoped hTarget
    simp only [Profile.fn, Profile.pad_singleton] at padded
    exact ⟨padded.view henv hscoped hTarget (AtomView.commutePadFn key output)⟩
termination_by sizeOf observation
decreasing_by all_goals simp_wf; omega

theorem Transfer.lamDF
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {source target : List VExpr} {locals : List Nat} {σ τ : Subst}
    {available : Valuation} {A A' B body other : VExpr}
    {domainLevel bodyLevel : VLevel}
    (originalDomain : Joint current fuel env U registry source A A' (.sort domainLevel))
    (originalBody : Joint current fuel env U registry (A :: source) body other B)
    (originalCodomain : Joint current fuel env U registry (A :: source) B B (.sort bodyLevel))
    (domains : env.IsDefEq U source A A' (.sort domainLevel))
    (codomain : env.HasType U (A :: source) B (.sort bodyLevel))
    (bodies : env.IsDefEq U (A :: source) body other B)
    (rightBody : env.HasType U (A' :: source) other B)
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (fits : PairedFits current fuel env U registry source target locals σ τ available) :
    Transfer current fuel env U registry target locals σ τ available
      (.lam A body) (.lam A' other) (.forallE A B) :=
  lambda_observer henv hscoped originalDomain originalBody originalCodomain
    domains codomain bodies rightBody closed hTarget substitutions fits

end Lean4Lean.AnchoredSource.Adapted.Staged
