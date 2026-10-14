import Lean4Lean.Theory.Typing.Strengthening.WitnessedTermDescent

/-! # Witnessed descent is exactly source-typed K replay

The lower-witness premise is necessary, not just sufficient, for compatible K
computation descent. One Eq.rec with the equality-family motive already tests it.
This identifies a concrete local obligation, without claiming that all
strengthening reduces to it.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params]

/-- The motive returning the equality family at its supplied endpoint. -/
def identityEqMotive (u : VLevel) (A a : VExpr) : VExpr :=
  .lam A (.lam (eqApp u A.lift a.lift (.bvar 0))
    (eqApp u A.lift.lift a.lift.lift (.bvar 1)))

theorem identityEqMotive_typed (heq : env.HasCanonicalEq) (hu : u.WF univs)
    (hA : env.HasType univs Γ A (.sort u)) (ha : env.HasType univs Γ a A) :
    env.HasType univs Γ (identityEqMotive u A a)
      (.forallE A (.forallE (eqApp u A.lift a.lift (.bvar 0)) (.sort .zero))) := by
  have hE := HasType.eqApp heq hu (hA.weak henv) (ha.weak henv) (.bvar .zero)
  have hA2 := (hA.weak henv (B := A)).weak henv (B := eqApp u A.lift a.lift (.bvar 0))
  have ha2 := (ha.weak henv (B := A)).weak henv (B := eqApp u A.lift a.lift (.bvar 0))
  have hb : env.HasType univs (eqApp u A.lift a.lift (.bvar 0) :: A :: Γ)
      (.bvar 1) A.lift.lift := .bvar (.succ .zero)
  exact .lam hA (.lam hE (HasType.eqApp heq hu hA2 ha2 hb))

theorem identityEqMotive_beta (hΓ : OnCtx Γ (env.IsType univs)) :
    env.SimAt univs Γ (.app (.app (identityEqMotive u A a) b) witness) (eqApp u A a b) := by
  have H := SimAt.mkApps_wrapLams henv hΓ
    (args := [b, witness]) (doms := [A, eqApp u A.lift a.lift (.bvar 0)])
    (body := eqApp u A.lift.lift a.lift.lift (.bvar 1)) rfl
  simpa [identityEqMotive, mkApps, wrapLams, eqApp, instOuter, inst,
    instVar, liftN, inst_lift, inst_liftN_lo, liftN_liftN] using H

/-- The source proof is typed before assuming any definitional equality of its
endpoints. Only the supplied object Eq witness is needed. -/
theorem identityEqRec_typed (heq : env.HasCanonicalEq)
    (hΓ : OnCtx Γ (env.IsType univs)) (hu : u.WF univs)
    (hA : env.HasType univs Γ A (.sort u)) (ha : env.HasType univs Γ a A)
    (hb : env.HasType univs Γ b A) (hw : env.HasType univs Γ witness (eqApp u A a b)) :
    env.HasType univs Γ
      (eqRecApp .zero u A a (identityEqMotive u A a) (eqReflApp u A a) b witness)
      (eqApp u A a b) := by
  let M := identityEqMotive u A a
  have hM := identityEqMotive_typed heq hu hA ha
  have hMA {y p : VExpr} (hy : env.HasType univs Γ y A)
      (hp : env.HasType univs Γ p (eqApp u A a y)) :
      env.HasType univs Γ (.app (.app M y) p) (.sort .zero) := by
    have hMy := hM.app hy
    have hMy' : env.HasType univs Γ (.app M y) (.forallE (eqApp u A a y) (.sort .zero)) := by
      simpa [M, eqApp, inst, instVar, inst_lift] using hMy
    exact hMy'.app hp
  have href := HasType.eqReflApp heq hu hA ha
  have hm := (identityEqMotive_beta hΓ _ (hMA ha href)).symm.defeq href
  have hr := HasType.eqRecApp heq (by trivial) hu hA ha hM hm hb hw
  exact (identityEqMotive_beta hΓ _ (hMA hb hw)).defeq hr

/-- Descent of all compatible K paths entails the witnessed endpoint front;
the proof needs just one root K step at the equality-family motive. -/
theorem witnessedTermDescent_of_K (heq : env.HasCanonicalEq)
    (H : ComputeDescent (GuardedKCompute D Cmp)) : WitnessedTermDescent Cmp := by
  intro ρ Γ Γ' u A a b witness W hΓ hΓ' hu hA ha hb hw HE
  let source := eqRecApp .zero u A a (identityEqMotive u A a) (eqReflApp u A a) b witness
  have hsource : env.HasType univs Γ source (eqApp u A a b) :=
    identityEqRec_typed heq hΓ hu hA ha hb hw
  have R : GuardedKCompute D Cmp Γ' (source.lift' ρ) ((eqReflApp u A a).lift' ρ) := by
    rw [show source.lift' ρ = eqRecApp .zero u (A.lift' ρ) (a.lift' ρ)
      ((identityEqMotive u A a).lift' ρ) ((eqReflApp u A a).lift' ρ) (b.lift' ρ) (witness.lift' ρ)
      from eqRecApp_lift']
    exact .eqRec HE
  obtain ⟨out, hout, hproof⟩ := H R W hΓ hΓ' hsource
  have hout : out = eqReflApp u A a := lift'_inj.1 hout.symm
  subst out
  exact ⟨_, (eqRefl_typed_iff_endpoint_eq henv heq hu hΓ hA ha).1 hproof.hasType.2⟩

/-- The witnessed front is the exact assumption for this whole compatible
computation interface; it is not an artifact of a particular descent proof. -/
theorem witnessedTermDescent_iff_K (heq : env.HasCanonicalEq) (hs : D.Sound env univs) :
    WitnessedTermDescent Cmp ↔ ComputeDescent (GuardedKCompute D Cmp) :=
  ⟨GuardedKCompute.computeDescent_witnessed heq hs, witnessedTermDescent_of_K heq⟩

/-- In the actual-conversion instance, compatible K and every registered prefix
have exactly the same sufficient lower-witness front. Only K is needed for the
converse. Global equality coverage remains a separate, unproved requirement. -/
theorem witnessedPropDescent_iff_K_and_prefix (heq : env.HasCanonicalEq) (hs : D.Sound env univs) :
    GuardedSingleton.WitnessedPropDescent (fun Δ a b => env.IsDefEqU univs Δ a b) ↔
      ComputeDescent (GuardedKCompute D (fun Δ a b => env.IsDefEqU univs Δ a b)) ∧
      ComputeDescent (GuardedSingleton.PrefixStep (fun Δ a b => env.IsDefEqU univs Δ a b)) := by
  constructor
  · exact witnessed_compute_descent heq hs
  · intro H
    exact (witnessedTermDescent_iff_prop heq).1 (witnessedTermDescent_of_K heq H.1)

end Lean4Lean.VEnv.Strengthening
