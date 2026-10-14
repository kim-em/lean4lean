import Lean4Lean.Theory.Typing.Strengthening.FreshPrefixReflection
import Lean4Lean.Theory.Typing.Strengthening.NormalSpineExposure
import Lean4Lean.Theory.Typing.Strengthening.PatternSpineTransport

/-! # Normal transport of actual prefixes without eta expansion

A checked prefix transports through normal comparison at any application spine.
Beta-only exposure retains extensional comparisons; finite fresh reflection
handles those under the explicit witnessed proposition front. This does not
prove that front or descend opaque normal-domain conversions.
-/
namespace Lean4Lean.VEnv.Strengthening.PureObservation
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params] {D : Definitions}
local notation:65 Γ " ⊢ " e " : " A:36 => HasType env univs Γ e A

/-- Compatible computation extends over a supplied argument spine. -/
theorem PrefixCompute.mkApps (R : PrefixCompute D Γ f f')
    (HA : List.Forall₂ (PrefixCompute D Γ) args args') :
    PrefixCompute D Γ (mkApps f args) (mkApps f' args') := by
  induction HA generalizing f f' with
  | nil => exact R
  | cons H _ ih => exact ih (.app R H)

private theorem compute_spine (R : PrefixCompute D Γ f f') (args : List VExpr) :
    PrefixCompute D Γ (mkApps f args) (mkApps f' args) := by
  apply R.mkApps
  induction args with
  | nil => exact .nil
  | cons _ _ ih => exact .cons .refl ih

private theorem split_normal_spine (H : List.Forall₂ (NormalEq Γ) xs (as ++ bs)) :
    ∃ as' bs', xs = as' ++ bs' ∧ List.Forall₂ (NormalEq Γ) as' as ∧
      List.Forall₂ (NormalEq Γ) bs' bs := by
  induction as generalizing xs with
  | nil => exact ⟨[], xs, rfl, .nil, H⟩
  | cons a as ih =>
    cases H with
    | cons h H =>
      obtain ⟨as', bs', rfl, hA, hB⟩ := ih H
      exact ⟨_ :: as', bs', rfl, .cons h hA, hB⟩

/-- A constant rule with normal argument congruence transports through arbitrary
normal comparison and extra arguments. Exact fresh reflection is the only use
of the witnessed front. The rule interface retains an actual checked step. -/
theorem normal_prefix_spine_rule (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hfront : GuardedSingleton.WitnessedPropDescent (fun Δ a b => env.IsDefEqU univs Δ a b))
    {name : Name} (Rule : List VExpr → List VLevel → List VExpr → VExpr → Prop)
    (step : ∀ {Γ ls args rhs}, Rule Γ ls args rhs →
      PrefixCompute D Γ (mkApps (.const name ls) args) rhs)
    (weak : ∀ {Γ ls args rhs A}, Rule Γ ls args rhs →
      Rule (A :: Γ) ls (args.map VExpr.lift) rhs.lift)
    (congr : ∀ {Γ ls ls' args args' rhs}, OnCtx Γ (env.IsType univs) → Rule Γ ls args rhs →
      List.Forall₂ (· ≈ ·) ls ls' → (∀ l ∈ ls', l.WF univs) →
      List.Forall₂ (NormalEq Γ) args args' → (∀ a ∈ args', ∃ A, Γ ⊢ a : A) →
      ∃ rhs', Rule Γ ls' args' rhs' ∧ NormalEq Γ rhs' rhs) :
    ∀ n {Γ ls args rhs bs x}, OnCtx Γ (env.IsType univs) →
      NormalEqN true n Γ x (mkApps (.const name ls) (args ++ bs)) → Rule Γ ls args rhs →
      ∃ out, PrefixCompute D Γ x out ∧ NormalEq Γ out (mkApps rhs bs) := by
  intro n
  induction n using Nat.strongRecOn with | _ n ih => ?_
  intro Γ ls args rhs bs x hΓ H hr
  obtain ⟨T, hd⟩ := H.defeq hΓ
  have hsource : Γ ⊢ mkApps (mkApps (.const name ls) args) bs : T := by
    simpa only [mkApps_append] using hd.hasType.2
  have htarget := (compute_spine (step hr) bs).simAt hs hΓ _ hsource |>.hasType.2
  have fire {ls' args' bs' T'} (hls : List.Forall₂ (· ≈ ·) ls' ls)
      (hargs : List.Forall₂ (NormalEq Γ) args' args)
      (hbs : List.Forall₂ (NormalEq Γ) bs' bs)
      (ht : Γ ⊢ mkApps (.const name ls') (args' ++ bs') : T') :
      ∃ rhs', Rule Γ ls' args' rhs' ∧ NormalEq Γ (mkApps rhs' bs') (mkApps rhs bs) := by
    have ht' : Γ ⊢ mkApps (mkApps (.const name ls') args') bs' : T' := by
      simpa only [mkApps_append] using ht
    obtain ⟨_, hhead⟩ := mkApps_head_type hΓ ht'
    obtain ⟨_, hc⟩ := mkApps_head_type hΓ hhead
    obtain ⟨_, _, hw, _⟩ := hc.const_inv henv hΓ
    obtain ⟨rhs', hr', hn⟩ := congr hΓ hr
      (hls.flip.imp (fun _ _ h => h.symm)) hw
      (hargs.flip.imp (fun _ _ (h : NormalEq Γ _ _) => h.symm hΓ))
      (fun a ha => mkApps_arg_type hΓ hhead ha)
    have hrhs' := (compute_spine (step hr') bs').simAt hs hΓ _ ht' |>.hasType.2
    exact ⟨rhs', hr', NormalEq.mkApps_spine hΓ hn hbs hrhs'⟩
  rcases normal_spine_expose_beta hΓ .const n H (bs := []) .nil hd.hasType.1 with
    hp | ⟨head, xs, hh, RB, hx⟩ | ⟨A, body, m, xs, B, hm, RB, HB, hx, ht⟩ |
      ⟨z, A, B, m, xs, hm, RB, hz, HB, hx, ht⟩
  · exact ⟨_, .refl, .proofIrrel hp hd.hasType.1 htarget⟩
  · obtain ⟨ls', rfl, hls⟩ : ∃ ls', head = .const name ls' ∧ List.Forall₂ (· ≈ ·) ls' ls := by
      cases hh with | const h => exact ⟨_, rfl, h⟩
    simp only [List.append_nil, mkApps, List.foldl_nil] at RB hx
    obtain ⟨args', bs', rfl, ha, hb⟩ := split_normal_spine hx
    have RC : PrefixCompute D Γ x (mkApps (.const name ls') (args' ++ bs')) :=
      .base (.of_beta RB)
    have ht := (RC.simAt hs hΓ _ hd.hasType.1).hasType.2
    obtain ⟨rhs', hr', hn⟩ := fire hls ha hb ht
    refine ⟨_, RC.trans ?_, hn⟩
    simpa only [mkApps_append] using compute_spine (step hr') bs'
  · simp only [List.append_nil, mkApps, List.foldl_nil] at RB hx
    obtain ⟨args', bs', rfl, ha, hb⟩ := split_normal_spine hx
    obtain ⟨rhs', hr', hn⟩ := fire (VLevel.forall₂_equiv_refl ls) ha hb ht
    have hA := (ht.isType henv hΓ).forallE_inv henv |>.1
    have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, hA⟩
    have HB' : NormalEqN true m (A :: Γ) body
        (mkApps (.const name ls) (args'.map VExpr.lift ++ (bs'.map VExpr.lift ++ [.bvar 0]))) := by
      rw [← List.append_assoc, mkApps_snoc]
      simpa only [lift, liftN_mkApps, liftN, Nat.zero_add, List.map_append] using HB
    obtain ⟨Y, RY, HY⟩ := ih m hm hΓA HB' (weak hr')
    have hrhs' := (compute_spine (step hr') bs').simAt hs hΓ _ (by
      simpa only [mkApps_append] using ht) |>.hasType.2
    have HY' : NormalEq (A :: Γ) Y (.app (mkApps rhs' bs').lift (.bvar 0)) := by
      simpa only [mkApps_snoc, lift, liftN_mkApps] using HY
    exact ⟨_, (PrefixCompute.base (.of_beta RB)).trans (.lam .refl RY),
      (NormalEq.etaL hrhs' HY').trans hΓ hn⟩
  · simp only [List.append_nil, mkApps, List.foldl_nil] at RB hx
    obtain ⟨args', bs', rfl, ha, hb⟩ := split_normal_spine hx
    obtain ⟨rhs', hr', hn⟩ := fire (VLevel.forall₂_equiv_refl ls) ha hb ht
    have hA := (ht.isType henv hΓ).forallE_inv henv |>.1
    have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, hA⟩
    have HB' : NormalEqN true m (A :: Γ) (.app z.lift (.bvar 0))
        (mkApps (.const name ls) (args'.map VExpr.lift ++ (bs'.map VExpr.lift ++ [.bvar 0]))) := by
      rw [← List.append_assoc, mkApps_snoc]
      simpa only [lift, liftN_mkApps, liftN, Nat.zero_add, List.map_append] using HB
    obtain ⟨Y, RY, HY⟩ := ih m hm hΓA HB' (weak hr')
    obtain ⟨z', Rz, HZ⟩ := RY.eta_body_reflection heq hs hfront hΓ hz
    have hrhs' := (compute_spine (step hr') bs').simAt hs hΓ _ (by
      simpa only [mkApps_append] using ht) |>.hasType.2
    have HY' : NormalEq (A :: Γ) Y (.app (mkApps rhs' bs').lift (.bvar 0)) := by
      simpa only [mkApps_snoc, lift, liftN_mkApps] using HY
    exact ⟨_, (PrefixCompute.base (.of_beta RB)).trans Rz,
      HZ.trans hΓ ((NormalEq.etaL hrhs' HY').trans hΓ hn)⟩

/-- An actual registered singleton prefix transports at every extra application
spine, with no function-eta step in the resulting computation. -/
theorem normal_singleton_prefix_spine (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hfront : GuardedSingleton.WitnessedPropDescent (fun Δ a b => env.IsDefEqU univs Δ a b))
    (hΓ : OnCtx Γ (env.IsType univs))
    (H : NormalEq Γ x (mkApps (.const name ls) (args ++ bs)))
    (R : PrefixUnfold env univs recursorData Γ name ls args rhs) :
    ∃ out, PrefixCompute D Γ x out ∧ NormalEq Γ out (mkApps rhs bs) := by
  obtain ⟨n, H⟩ := H
  exact normal_prefix_spine_rule heq hs hfront
    (fun Γ ls args rhs => PrefixUnfold env univs recursorData Γ name ls args rhs)
    (fun h => .singleton h) (fun h => h.weakN henv .one)
    (fun hΓ h hls hw hargs hT => by
      obtain ⟨rhs₁, hr₁, hn₁⟩ := PrefixUnfold.congr_normal hΓ h hargs
      obtain ⟨rhs₂, hr₂, hu⟩ := PrefixUnfold.congr_levels henv hΓ hr₁ hw hls
        (eqUpToLevels_forall₂_rfl hΓ hT)
      have ht₁ := (Exists.choose_spec (PrefixUnfold.defeq henv hΓ hr₁)).hasType.2
      exact ⟨rhs₂, hr₂, ((NormalEq.of_levelEquiv hΓ (.of_eqUpToLevels hu) ht₁).symm hΓ).trans
        hΓ (hn₁.symm hΓ)⟩) n hΓ H R

/-- The primitive quotient prefix has the same conditional spine transport. -/
theorem normal_quotient_prefix_spine (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hfront : GuardedSingleton.WitnessedPropDescent (fun Δ a b => env.IsDefEqU univs Δ a b))
    (hΓ : OnCtx Γ (env.IsType univs))
    (H : NormalEq Γ x (mkApps (.const ``Quot.lift ls) (args ++ bs)))
    (R : QuotPrefixUnfold env univs Γ ls args rhs) :
    ∃ out, PrefixCompute D Γ x out ∧ NormalEq Γ out (mkApps rhs bs) := by
  obtain ⟨n, H⟩ := H
  exact normal_prefix_spine_rule heq hs hfront
    (fun Γ ls args rhs => QuotPrefixUnfold env univs Γ ls args rhs)
    (fun h => .quotient h) (fun h => h.weakN henv .one)
    (fun hΓ h hls hw hargs hT => by
      obtain ⟨rhs₁, hr₁, hn₁⟩ := QuotPrefixUnfold.congr_normal hΓ h hargs
      obtain ⟨rhs₂, hr₂, hu⟩ := QuotPrefixUnfold.congr_levels henv hΓ hr₁ hw hls
        (eqUpToLevels_forall₂_rfl hΓ hT)
      have ht₁ := (Exists.choose_spec (QuotPrefixUnfold.defeq henv hΓ hr₁)).hasType.2
      exact ⟨rhs₂, hr₂, ((NormalEq.of_levelEquiv hΓ (.of_eqUpToLevels hu) ht₁).symm hΓ).trans
        hΓ (hn₁.symm hΓ)⟩) n hΓ H R

/-- Root specialization of singleton transport. -/
theorem normal_singleton_prefix (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hfront : GuardedSingleton.WitnessedPropDescent (fun Δ a b => env.IsDefEqU univs Δ a b))
    (hΓ : OnCtx Γ (env.IsType univs))
    (H : NormalEq Γ x (mkApps (.const name ls) args))
    (R : PrefixUnfold env univs recursorData Γ name ls args rhs) :
    ∃ out, PrefixCompute D Γ x out ∧ NormalEq Γ out rhs := by
  simpa only [mkApps, List.foldl_nil] using
    normal_singleton_prefix_spine heq hs hfront hΓ (bs := []) (by simpa using H) R

/-- Root specialization of quotient transport. -/
theorem normal_quotient_prefix (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hfront : GuardedSingleton.WitnessedPropDescent (fun Δ a b => env.IsDefEqU univs Δ a b))
    (hΓ : OnCtx Γ (env.IsType univs))
    (H : NormalEq Γ x (mkApps (.const ``Quot.lift ls) args))
    (R : QuotPrefixUnfold env univs Γ ls args rhs) :
    ∃ out, PrefixCompute D Γ x out ∧ NormalEq Γ out rhs := by
  simpa only [mkApps, List.foldl_nil] using
    normal_quotient_prefix_spine heq hs hfront hΓ (bs := []) (by simpa using H) R

end Lean4Lean.VEnv.Strengthening.PureObservation
