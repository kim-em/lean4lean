import Lean4Lean.Theory.Typing.AnchoredBoundedPi
import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceGradedClosures
import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceGradedEmpty
import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceGradedSort

/-! The original Pi-rule children handle every finite observation of
the source Pi, including views and changes of grade. -/
namespace Lean4Lean.AnchoredSource.Adapted.Staged
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false
variable {current : Name → Bool} {fuel : Nat}

private theorem pi_observer
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {source target : List VExpr} {locals : List Nat} {σ τ : Subst}
    {available : Valuation} {A A' B B' : VExpr}
    {domainLevel bodyLevel : VLevel} {demand : Profile n} {footprint : Footprint}
    (originalDomain : Joint current fuel env U registry source A A' (.sort domainLevel))
    (originalBody : Joint current fuel env U registry (A :: source) B B' (.sort bodyLevel))
    (domains : env.IsDefEq U source A A' (.sort domainLevel))
    (bodies : env.IsDefEq U (A :: source) B B' (.sort bodyLevel))
    (rightBody : env.HasType U (A' :: source) B' (.sort bodyLevel))
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (fits : PairedFits current fuel env U registry source target locals σ τ available)
    (observation : Obs env U registry target locals σ (.forallE A B) demand footprint)
    (bound : observation.nativeDepth current ≤ fuel)
    (resources : footprint.Available available) :
    Nonempty (Result current fuel env U registry target locals σ τ available
      (.forallE A B) (.forallE A' B') (.sort (.imax domainLevel bodyLevel)) demand) := by
  match observation with
  | .empty => exact ⟨.empty⟩
  | .pi domain guard body =>
    have bounds := Nat.max_le.mp (show max (domain.nativeDepth current) (body.nativeDepth current) ≤ fuel by simpa only [Obs.nativeDepth] using bound)
    exact Obs.pi_transfer henv hscoped originalDomain originalBody domains bodies rightBody
      closed hTarget substitutions fits domain guard body bounds.1 bounds.2
      (fun i need hm => resources i need (List.mem_append_left _ hm))
      (fun i need hm => resources i need (List.mem_append_right _ hm))
  | .union left right =>
    have bounds := Nat.max_le.mp (show max (left.nativeDepth current) (right.nativeDepth current) ≤ fuel by simpa only [Obs.nativeDepth] using bound)
    obtain ⟨a⟩ := pi_observer henv hscoped originalDomain originalBody
      domains bodies rightBody closed hTarget substitutions fits left bounds.1
      (fun i need hm => resources i need (List.mem_append_left _ hm))
    obtain ⟨b⟩ := pi_observer henv hscoped originalDomain originalBody
      domains bodies rightBody closed hTarget substitutions fits right bounds.2
      (fun i need hm => resources i need (List.mem_append_right _ hm))
    exact ⟨a.union henv hscoped hTarget b⟩
  | .view source change =>
    obtain ⟨a⟩ := pi_observer henv hscoped originalDomain originalBody
      domains bodies rightBody closed hTarget substitutions fits source (by simpa only [Obs.nativeDepth] using bound) resources
    exact ⟨a.view henv hscoped hTarget change⟩
  | .pad source =>
    obtain ⟨a⟩ := pi_observer henv hscoped originalDomain originalBody
      domains bodies rightBody closed hTarget substitutions fits source (by simpa only [Obs.nativeDepth] using bound) resources
    exact ⟨a.pad henv hscoped hTarget⟩
  | .unpad source =>
    obtain ⟨a⟩ := pi_observer henv hscoped originalDomain originalBody
      domains bodies rightBody closed hTarget substitutions fits source (by simpa only [Obs.nativeDepth] using bound) resources
    exact ⟨a.unpad⟩
  | @Obs.rowShift _ _ _ _ _ _ _ _ key output _ source =>
    obtain ⟨a⟩ := pi_observer henv hscoped originalDomain originalBody
      domains bodies rightBody closed hTarget substitutions fits source (by simpa only [Obs.nativeDepth] using bound) resources
    have padded := a.pad henv hscoped hTarget
    simp only [Profile.fn, Profile.pad_singleton] at padded
    exact ⟨padded.view henv hscoped hTarget (AtomView.commutePadFn key output)⟩
termination_by sizeOf observation
decreasing_by all_goals simp_wf; omega

theorem Transfer.forallEDF
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {source target : List VExpr} {locals : List Nat} {σ τ : Subst}
    {available : Valuation} {A A' B B' : VExpr}
    {domainLevel bodyLevel : VLevel}
    (originalDomain : Joint current fuel env U registry source A A' (.sort domainLevel))
    (originalBody : Joint current fuel env U registry (A :: source) B B' (.sort bodyLevel))
    (domains : env.IsDefEq U source A A' (.sort domainLevel))
    (bodies : env.IsDefEq U (A :: source) B B' (.sort bodyLevel))
    (rightBody : env.HasType U (A' :: source) B' (.sort bodyLevel))
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (fits : PairedFits current fuel env U registry source target locals σ τ available) :
    Transfer current fuel env U registry target locals σ τ available
      (.forallE A B) (.forallE A' B') (.sort (.imax domainLevel bodyLevel)) :=
  pi_observer henv hscoped originalDomain originalBody
    domains bodies rightBody closed hTarget substitutions fits

theorem Joint.forallEDF
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {source : List VExpr} {A A' B B' : VExpr} {domainLevel bodyLevel : VLevel}
    (originalDomain : Joint current fuel env U registry source A A' (.sort domainLevel))
    (originalBody : Joint current fuel env U registry (A :: source) B B' (.sort bodyLevel))
    (originalBody' : Joint current fuel env U registry (A' :: source) B B' (.sort bodyLevel))
    (domains : env.IsDefEq U source A A' (.sort domainLevel))
    (bodies : env.IsDefEq U (A :: source) B B' (.sort bodyLevel))
    (bodies' : env.IsDefEq U (A' :: source) B B' (.sort bodyLevel)) :
    Joint current fuel env U registry source (.forallE A B) (.forallE A' B')
      (.sort (.imax domainLevel bodyLevel)) := by
  apply Joint.of_transfers henv
  intro target locals σ τ available closed hTarget substitutions fits
  exact ⟨Transfer.forallEDF henv hscoped originalDomain originalBody
      domains bodies bodies'.hasType.2 closed hTarget substitutions fits,
    Transfer.forallEDF henv hscoped originalDomain.symm originalBody'.symm
      domains.symm bodies'.symm bodies.hasType.1 closed hTarget substitutions fits⟩

end Lean4Lean.AnchoredSource.Adapted.Staged
