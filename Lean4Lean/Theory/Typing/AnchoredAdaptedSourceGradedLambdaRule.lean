import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceGradedLambdaTransfer
import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceGradedClosures
import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceGradedEmpty

/-! The original lambda-rule children handle every finite observation of
the source lambda, including views and changes of grade. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

private theorem lambda_observer
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {source target : List VExpr} {locals : List Nat} {σ τ : Subst}
    {available : Valuation} {A A' B body other : VExpr}
    {domainLevel bodyLevel : VLevel} {demand : Profile n} {footprint : Footprint}
    (originalDomain : GradedJoint env U registry source A A' (.sort domainLevel))
    (originalBody : GradedJoint env U registry (A :: source) body other B)
    (originalCodomain : GradedJoint env U registry (A :: source) B B (.sort bodyLevel))
    (domains : env.IsDefEq U source A A' (.sort domainLevel))
    (codomain : env.HasType U (A :: source) B (.sort bodyLevel))
    (bodies : env.IsDefEq U (A :: source) body other B)
    (rightBody : env.HasType U (A' :: source) other B)
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (fits : PairedFits env U registry source target locals σ τ available)
    (observation : Obs env U registry target locals σ (.lam A body) demand footprint)
    (resources : footprint.Available available) :
    Nonempty (GradedTransferResult env U registry target locals σ τ available
      (.lam A body) (.lam A' other) (.forallE A B) demand) := by
  match observation with
  | .empty => exact ⟨.empty⟩
  | .lam domain guard body pack covered =>
    exact Obs.graded_lam_transfer henv hscoped domain guard body pack covered
      originalDomain originalBody originalCodomain closed domains codomain bodies rightBody
      hTarget substitutions fits
      (fun i need hm => resources i need (List.mem_append_left _ hm))
      (fun i need hm => resources i need (List.mem_append_right _ hm))
  | .union left right =>
    obtain ⟨a⟩ := lambda_observer henv hscoped originalDomain originalBody originalCodomain
      domains codomain bodies rightBody closed hTarget substitutions fits left
      (fun i need hm => resources i need (List.mem_append_left _ hm))
    obtain ⟨b⟩ := lambda_observer henv hscoped originalDomain originalBody originalCodomain
      domains codomain bodies rightBody closed hTarget substitutions fits right
      (fun i need hm => resources i need (List.mem_append_right _ hm))
    exact ⟨a.union henv hscoped hTarget b⟩
  | .view source change =>
    obtain ⟨a⟩ := lambda_observer henv hscoped originalDomain originalBody originalCodomain
      domains codomain bodies rightBody closed hTarget substitutions fits source resources
    exact ⟨a.view henv hscoped hTarget change⟩
  | .pad source =>
    obtain ⟨a⟩ := lambda_observer henv hscoped originalDomain originalBody originalCodomain
      domains codomain bodies rightBody closed hTarget substitutions fits source resources
    exact ⟨a.pad henv hscoped hTarget⟩
  | .unpad source =>
    obtain ⟨a⟩ := lambda_observer henv hscoped originalDomain originalBody originalCodomain
      domains codomain bodies rightBody closed hTarget substitutions fits source resources
    exact ⟨a.unpad⟩
  | @Obs.rowShift _ _ _ _ _ _ _ _ key output _ source =>
    obtain ⟨a⟩ := lambda_observer henv hscoped originalDomain originalBody originalCodomain
      domains codomain bodies rightBody closed hTarget substitutions fits source resources
    have padded := a.pad henv hscoped hTarget
    simp only [Profile.fn, Profile.pad_singleton] at padded
    exact ⟨padded.view henv hscoped hTarget (AtomView.commutePadFn key output)⟩
termination_by sizeOf observation
decreasing_by all_goals simp_wf; omega

theorem GradedTransfer.lamDF
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {source target : List VExpr} {locals : List Nat} {σ τ : Subst}
    {available : Valuation} {A A' B body other : VExpr}
    {domainLevel bodyLevel : VLevel}
    (originalDomain : GradedJoint env U registry source A A' (.sort domainLevel))
    (originalBody : GradedJoint env U registry (A :: source) body other B)
    (originalCodomain : GradedJoint env U registry (A :: source) B B (.sort bodyLevel))
    (domains : env.IsDefEq U source A A' (.sort domainLevel))
    (codomain : env.HasType U (A :: source) B (.sort bodyLevel))
    (bodies : env.IsDefEq U (A :: source) body other B)
    (rightBody : env.HasType U (A' :: source) other B)
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (fits : PairedFits env U registry source target locals σ τ available) :
    GradedTransfer env U registry target locals σ τ available
      (.lam A body) (.lam A' other) (.forallE A B) :=
  lambda_observer henv hscoped originalDomain originalBody originalCodomain
    domains codomain bodies rightBody closed hTarget substitutions fits

end Lean4Lean.AnchoredSource.Adapted
