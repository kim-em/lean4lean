import Lean4Lean.Theory.Typing.Strengthening.GuardedKComputation
import Lean4Lean.Theory.Typing.Strengthening.HybridAlgebra

/-! # Finite recursive certificates for computational K matching

At depth zero, endpoints have a hybrid normal comparison. Each further depth
allows compatible computations on both endpoints before that comparison; K
steps in these computations use certificates from the preceding depth. Thus
nested computational alignment descends without an arbitrary-conversion oracle.
Full-conversion completeness and general indexed-prefix coverage remain open.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
open PureObservation (Definitions)
variable [Params]

/-- A finite comparison certificate, allowing recursively guarded computations
before its final eta-aware normal comparison. The depth bounds nested K guards,
not the number of ordinary computation steps. -/
def KCertificate (D : Definitions) : Nat → List VExpr → VExpr → VExpr → Prop
  | 0, Γ, a, b => ∃ n, HybridNormal n Γ a b
  | depth + 1, Γ, a, b => ∃ a' b' n,
      GuardedKCompute D (KCertificate D depth) Γ a a' ∧
      GuardedKCompute D (KCertificate D depth) Γ b b' ∧ HybridNormal n Γ a' b'

/-- Compatible computation using certificates with bounded recursive depth. -/
abbrev CertifiedKCompute (D : Definitions) (depth : Nat) :=
  GuardedKCompute D (KCertificate D depth)

/-- A normal comparison gives a certificate at any positive or zero depth. -/
theorem KCertificate.normal (H : HybridNormal n Γ a b) : KCertificate D depth Γ a b := by
  cases depth with
  | zero => exact ⟨n, H⟩
  | succ depth => exact ⟨a, b, n, .base .refl, .base .refl, H⟩

/-- A completed computation becomes an endpoint certificate at the next depth.
Only its target typing is needed to certify the final reflexive comparison. -/
theorem KCertificate.of_compute (R : CertifiedKCompute D depth Γ a b)
    (hb : env.HasType univs Γ b T) : KCertificate D (depth + 1) Γ a b :=
  ⟨b, b, 0, R, .base .refl, .refl hb⟩

/-- All finite certificate depths reflect common-typed endpoints through lifts.
The induction replays the endpoint computations below before applying hybrid
normal descent; no intermediate lower-context typing is postulated. -/
theorem KCertificate.descends (heq : env.HasCanonicalEq) (hs : D.Sound env univs) :
    ∀ depth, EndpointDescent (KCertificate D depth) := by
  intro depth
  induction depth with
  | zero =>
    intro ρ Γ Γ' a b α W hΓ hΓ' ha hb H
    obtain ⟨n, H⟩ := H
    obtain ⟨u, hα⟩ := ha.isType henv hΓ
    exact (HybridNormal.descend n W hΓ hΓ' ha hb H).1 ⟨_, hα⟩
  | succ depth ih =>
    intro ρ Γ Γ' a b α W hΓ hΓ' ha hb H
    obtain ⟨a', b', n, Ra, Rb, H⟩ := H
    obtain ⟨a₀, rfl, Ea⟩ := Ra.descend heq hs ih W hΓ hΓ'
    obtain ⟨b₀, rfl, Eb⟩ := Rb.descend heq hs ih W hΓ hΓ'
    have Ea := Ea _ ha
    have Eb := Eb _ hb
    obtain ⟨u, hα⟩ := ha.isType henv hΓ
    have E := (HybridNormal.descend n W hΓ hΓ' Ea.hasType.2 Eb.hasType.2 H).1 ⟨_, hα⟩
    exact ⟨_, Ea.trans ((E.of_l henv hΓ Ea.hasType.2).trans Eb.symm)⟩

/-- Recursive certificates remain available after context insertion. -/
theorem KCertificate.weakN (W : Ctx.LiftN n k Γ Γ') (H : KCertificate D depth Γ a b) :
    KCertificate D depth Γ' (a.liftN n k) (b.liftN n k) := by
  induction depth generalizing n k Γ Γ' a b with
  | zero =>
    obtain ⟨i, H⟩ := H
    exact ⟨i, H.weakN W⟩
  | succ depth ih =>
    obtain ⟨a', b', i, Ra, Rb, H⟩ := H
    exact ⟨_, _, i, Ra.weakN (fun W H => ih W H) W,
      Rb.weakN (fun W H => ih W H) W, H.weakN W⟩

/-- No additional matching hypothesis is needed to replay certified paths. -/
theorem CertifiedKCompute.descend (R : CertifiedKCompute D depth Γ' (e.lift' ρ) target)
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (W : Ctx.Lift' ρ Γ Γ') (hΓ : OnCtx Γ (env.IsType univs))
    (hΓ' : OnCtx Γ' (env.IsType univs)) :
    ∃ out, target = out.lift' ρ ∧ env.SimAt univs Γ e out :=
  GuardedKCompute.descend R heq hs (KCertificate.descends heq hs depth) W hΓ hΓ'

/-- Pi exposure is recovered below for arbitrarily nested certified K guards. -/
theorem CertifiedKCompute.pi_exposure_below
    (R : CertifiedKCompute D depth Γ' (e.lift' ρ) (.forallE A B))
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (W : Ctx.Lift' ρ Γ Γ') (hΓ : OnCtx Γ (env.IsType univs))
    (hΓ' : OnCtx Γ' (env.IsType univs)) (ht : env.HasType univs Γ e T) :
    ∃ A₀ B₀, env.IsDefEq univs Γ e (.forallE A₀ B₀) T :=
  GuardedKCompute.pi_exposure_below R heq hs (KCertificate.descends heq hs depth) W hΓ hΓ' ht

/-- Function eta is a supported matching certificate at every depth. -/
theorem KCertificate.eta (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (.forallE A B)) :
    KCertificate D depth Γ f (.lam A (.app f.lift (.bvar 0))) := by
  obtain ⟨_, T, hb⟩ := (IsDefEq.eta hf).hasType.1.lam_inv henv.orderedStrong hΓ
  exact KCertificate.normal (.etaR hf (.refl hb))

end Lean4Lean.VEnv.Strengthening
