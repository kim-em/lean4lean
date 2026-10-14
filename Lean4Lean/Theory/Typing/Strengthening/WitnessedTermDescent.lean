import Lean4Lean.Theory.Typing.Strengthening.WitnessedPrefixDescent
import Lean4Lean.Theory.Typing.Strengthening.SingletonIndexAlignmentBoundary

/-! # Typed endpoint descent with an equality witness below

The restricted proposition front can be applied to arbitrary typed endpoints
whose object-language equality already has a lower-context witness. Canonical
Eq maps that witness to an equality of the two inhabited diagonal families.
This does not supply the restricted front or prove global strengthening.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params]

/-- Equality of the diagonal family and the family at a varying right endpoint. -/
def diagonalFamilyMotive (u : VLevel) (A a : VExpr) : VExpr :=
  .lam A (.lam (eqApp u A.lift a.lift (.bvar 0))
    (eqApp (.succ .zero) (.sort .zero)
      (eqApp u A.lift.lift a.lift.lift a.lift.lift)
      (eqApp u A.lift.lift a.lift.lift (.bvar 1))))

theorem diagonalFamilyMotive_typed (heq : env.HasCanonicalEq) (hu : u.WF univs)
    (hA : env.HasType univs Γ A (.sort u)) (ha : env.HasType univs Γ a A) :
    env.HasType univs Γ (diagonalFamilyMotive u A a)
      (.forallE A (.forallE (eqApp u A.lift a.lift (.bvar 0)) (.sort .zero))) := by
  have hE := HasType.eqApp heq hu (hA.weak henv) (ha.weak henv) (.bvar .zero)
  have hA2 := (hA.weak henv (B := A)).weak henv (B := eqApp u A.lift a.lift (.bvar 0))
  have ha2 := (ha.weak henv (B := A)).weak henv (B := eqApp u A.lift a.lift (.bvar 0))
  have hb : env.HasType univs (eqApp u A.lift a.lift (.bvar 0) :: A :: Γ)
      (.bvar 1) A.lift.lift := .bvar (.succ .zero)
  have hP := HasType.eqApp heq hu hA2 ha2 ha2
  have hQ := HasType.eqApp heq hu hA2 ha2 hb
  exact .lam hA (.lam hE (HasType.eqApp heq (by trivial) (.sort (by trivial)) hP hQ))

/-- The motive's two beta steps are independent of endpoint conversion. -/
theorem diagonalFamilyMotive_beta (hΓ : OnCtx Γ (env.IsType univs)) :
    env.SimAt univs Γ (.app (.app (diagonalFamilyMotive u A a) b) witness)
      (eqApp (.succ .zero) (.sort .zero) (eqApp u A a a) (eqApp u A a b)) := by
  have H := SimAt.mkApps_wrapLams henv hΓ
    (args := [b, witness]) (doms := [A, eqApp u A.lift a.lift (.bvar 0)])
    (body := eqApp (.succ .zero) (.sort .zero)
      (eqApp u A.lift.lift a.lift.lift a.lift.lift)
      (eqApp u A.lift.lift a.lift.lift (.bvar 1))) rfl
  simpa [diagonalFamilyMotive, mkApps, wrapLams, eqApp, instOuter, inst,
    instVar, liftN, inst_lift, inst_liftN_lo, liftN_liftN] using H

/-- An object equality between arbitrary endpoints gives an object equality
between their diagonal and mixed Eq-family propositions in the same context. -/
theorem diagonalFamily_witness (heq : env.HasCanonicalEq)
    (hΓ : OnCtx Γ (env.IsType univs)) (hu : u.WF univs)
    (hA : env.HasType univs Γ A (.sort u)) (ha : env.HasType univs Γ a A)
    (hb : env.HasType univs Γ b A) (hw : env.HasType univs Γ witness (eqApp u A a b)) :
    ∃ proof, env.HasType univs Γ proof
      (eqApp (.succ .zero) (.sort .zero) (eqApp u A a a) (eqApp u A a b)) := by
  let M := diagonalFamilyMotive u A a
  have hM := diagonalFamilyMotive_typed heq hu hA ha
  have hMA {y p : VExpr} (hy : env.HasType univs Γ y A)
      (hp : env.HasType univs Γ p (eqApp u A a y)) :
      env.HasType univs Γ (.app (.app M y) p) (.sort .zero) := by
    have hMy := hM.app hy
    have hMy' : env.HasType univs Γ (.app M y) (.forallE (eqApp u A a y) (.sort .zero)) := by
      simpa [M, eqApp, inst, instVar, inst_lift] using hMy
    exact hMy'.app hp
  have href := HasType.eqReflApp heq hu hA ha
  have hP := HasType.eqApp heq hu hA ha ha
  have hm := HasType.eqReflApp heq (by trivial) (.sort (by trivial)) hP
  have hβa := diagonalFamilyMotive_beta hΓ _ (hMA ha href)
  have hm' := hβa.symm.defeq hm
  have hr := HasType.eqRecApp heq (by trivial) hu hA ha hM hm' hb hw
  exact ⟨_, (diagonalFamilyMotive_beta hΓ _ (hMA hb hw)).defeq hr⟩

/-- With actual conversion as the comparison, the witnessed proposition front
handles arbitrary universes and arbitrary common endpoint types. -/
theorem witnessedTermDescent_of_prop (heq : env.HasCanonicalEq)
    (H : GuardedSingleton.WitnessedPropDescent (fun Δ a b => env.IsDefEqU univs Δ a b)) :
    WitnessedTermDescent (fun Δ a b => env.IsDefEqU univs Δ a b) := by
  intro ρ Γ Γ' u A a b witness W hΓ hΓ' hu hA ha hb hw HE
  have hP := HasType.eqApp heq hu hA ha ha
  have hQ := HasType.eqApp heq hu hA ha hb
  obtain ⟨w, hW⟩ := diagonalFamily_witness heq hΓ hu hA ha hb hw
  have ha' := ha.weak' henv W
  have Hfamily := IsDefEq.eqApp_r heq hu (hA.weak' henv W) ha' (HE.of_l henv hΓ' ha')
  have Hfamily' : env.IsDefEqU univs Γ' ((eqApp u A a a).lift' ρ) ((eqApp u A a b).lift' ρ) := by
    simpa only [eqApp, lift'] using (show env.IsDefEqU univs Γ' _ _ from ⟨_, Hfamily⟩)
  have hPQ := H W hΓ hΓ' hP hQ (HasType.eqReflApp heq hu hA ha) hw hW Hfamily'
  have hPQ' : env.IsDefEqU univs Γ
      (mkApps (.const ``Eq [u]) [A, a, a]) (mkApps (.const ``Eq [u]) [A, a, b]) := hPQ
  obtain ⟨_, hargs⟩ := hPQ'.rigidApp_inv henv hΓ (heq.rigid henv) hP
  cases hargs with | cons _ hargs =>
  cases hargs with | cons _ hargs =>
  cases hargs with | cons hab _ => exact hab

/-- The inhabited proposition restriction and arbitrary witnessed endpoints are
equivalent local fronts. This does not identify either with PropositionFront. -/
theorem witnessedTermDescent_iff_prop (heq : env.HasCanonicalEq) :
    WitnessedTermDescent (fun Δ a b => env.IsDefEqU univs Δ a b) ↔
      GuardedSingleton.WitnessedPropDescent (fun Δ a b => env.IsDefEqU univs Δ a b) := by
  constructor
  · intro H ρ Γ Γ' P Q p q witness W hΓ hΓ' hP hQ _ _ hw HE
    exact H W hΓ hΓ' (by trivial) (.sort (by trivial)) hP hQ hw HE
  · exact witnessedTermDescent_of_prop heq

/-- Full compatible K computation only needs the witnessed endpoint interface;
each source recursor supplies its witness below before replaying the guard. -/
theorem GuardedKCompute.computeDescent_witnessed (heq : env.HasCanonicalEq)
    (hs : D.Sound env univs) (H : WitnessedTermDescent Cmp) :
    ComputeDescent (GuardedKCompute D Cmp) := by
  intro ρ Γ Γ' e target T R W hΓ hΓ' ht
  obtain ⟨out, hout, hsim⟩ := R.descend_witnessed heq hs H W hΓ hΓ'
  exact ⟨out, hout, hsim _ ht⟩

/-- One lower-witness front suffices for both compatible K and every registered
singleton-prefix check with actual ambient conversion guards. No finite guard
certificate coverage assumption is used here. Global equality completeness is
not asserted for this pair of computation relations. -/
theorem witnessed_compute_descent (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (H : GuardedSingleton.WitnessedPropDescent (fun Δ a b => env.IsDefEqU univs Δ a b)) :
    ComputeDescent (GuardedKCompute D (fun Δ a b => env.IsDefEqU univs Δ a b)) ∧
    ComputeDescent (GuardedSingleton.PrefixStep (fun Δ a b => env.IsDefEqU univs Δ a b)) :=
  ⟨GuardedKCompute.computeDescent_witnessed heq hs (witnessedTermDescent_of_prop heq H),
    GuardedSingleton.PrefixStep.computeDescent_witnessed heq H⟩

/-- A concrete unproved front: strengthening only a comparison between a supplied
Eq proof and reflexivity at its fixed left endpoint. The proof and the carrier
typing already exist below; the right endpoint need not be convertible below.
This is more restricted than arbitrary proof equality strengthening. -/
def ReflexivityProofFront : Prop :=
  ∀ {ρ Γ Γ' u A a b witness}, Ctx.Lift' ρ Γ Γ' →
    OnCtx Γ (env.IsType univs) → OnCtx Γ' (env.IsType univs) →
    u.WF univs → env.HasType univs Γ A (.sort u) →
    env.HasType univs Γ a A → env.HasType univs Γ b A →
    env.HasType univs Γ witness (eqApp u A a b) →
    env.IsDefEqU univs Γ' (witness.lift' ρ) ((eqReflApp u A a).lift' ρ) →
    env.IsDefEqU univs Γ witness (eqReflApp u A a)

/-- This single reflexivity-proof front is equivalent to the lower-witness term
front. The reverse direction uses proof irrelevance only above, then rigid Eq
inversion below; it does not assume equality reflection for object Eq. -/
theorem reflexivityProofFront_iff_witnessedTerm (heq : env.HasCanonicalEq) :
    ReflexivityProofFront ↔ WitnessedTermDescent (fun Δ a b => env.IsDefEqU univs Δ a b) := by
  constructor
  · intro H ρ Γ Γ' u A a b witness W hΓ hΓ' hu hA ha hb hw HE
    have hA' := hA.weak' henv W
    have ha' := ha.weak' henv W
    have hb' := hb.weak' henv W
    have hw' := hw.weak' henv W
    have href := HasType.eqReflApp heq hu hA' ha'
    have href' := (IsDefEq.eqApp_r heq hu hA' ha' (HE.of_l henv hΓ' ha')).defeq href
    have hproof := IsDefEq.proofIrrel (HasType.eqApp heq hu hA' ha' hb') hw' href'
    have hproof' : env.IsDefEqU univs Γ' (witness.lift' ρ) ((eqReflApp u A a).lift' ρ) := by
      simpa only [eqApp, eqReflApp, lift'] using (show env.IsDefEqU univs Γ' _ _ from ⟨_, hproof⟩)
    have hbelow := H W hΓ hΓ' hu hA ha hb hw hproof'
    have hrefBelow := (hbelow.of_l henv hΓ hw).hasType.2
    exact ⟨_, (eqRefl_typed_iff_endpoint_eq henv heq hu hΓ hA ha).1 hrefBelow⟩
  · intro H ρ Γ Γ' u A a b witness W hΓ hΓ' hu hA ha hb hw HE
    have hw' := hw.weak' henv W
    have href' := (HE.of_l henv hΓ' hw').hasType.2
    have href'' : env.HasType univs Γ' (eqReflApp u (A.lift' ρ) (a.lift' ρ))
        (eqApp u (A.lift' ρ) (a.lift' ρ) (b.lift' ρ)) := by
      simpa only [eqApp, eqReflApp, lift'] using href'
    have hab' := (eqRefl_typed_iff_endpoint_eq henv heq hu hΓ'
      (hA.weak' henv W) (ha.weak' henv W)).1 href''
    have hab := H W hΓ hΓ' hu hA ha hb hw ⟨_, hab'⟩
    have href := (IsDefEq.eqApp_r heq hu hA ha (hab.of_l henv hΓ ha)).defeq
      (HasType.eqReflApp heq hu hA ha)
    exact ⟨_, IsDefEq.proofIrrel (HasType.eqApp heq hu hA ha hb) hw href⟩

/-- The generated-prefix lower-witness front has a concrete Eq-proof formulation.
Strictness relative to PropositionFront and sufficiency for all strengthening
remain unproved. -/
theorem reflexivityProofFront_iff_witnessedProp (heq : env.HasCanonicalEq) :
    ReflexivityProofFront ↔
      GuardedSingleton.WitnessedPropDescent (fun Δ a b => env.IsDefEqU univs Δ a b) :=
  (reflexivityProofFront_iff_witnessedTerm heq).trans (witnessedTermDescent_iff_prop heq)

end Lean4Lean.VEnv.Strengthening
