import Lean4Lean.Theory.Typing.Strengthening.CertifiedKSubstitution

/-! # Recovering a particular type from source well-formedness

These certificates reconstruct a chosen type from the term's syntax, variable
lookup, constant declarations, and certified computation on already recovered
types. They require only source well-formedness at replay. Application recovers
its argument type by uniqueness, so it needs no assumed conversion check below.
The current syntax covers sorts, constants, variables, lambdas, applications and
Pis. Projection recovery and completeness for arbitrary typing are not asserted.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
open PureObservation (Definitions)
variable [Params]

/-- A finite source-typed reconstruction of a particular type. The Pi rule
records only universe choices, which uniqueness reflects without strengthening.
Conversion uses the explicit finite computational certificate relation. -/
inductive TypeRecovery (D : Definitions) (depth : Nat) : List VExpr → VExpr → VExpr → Prop where
  | sort : u.WF univs → TypeRecovery D depth Γ (.sort u) (.sort (.succ u))
  | const : env.constants c = some ci → (∀ l ∈ ls, l.WF univs) → ls.length = ci.uvars →
      TypeRecovery D depth Γ (.const c ls) (ci.type.instL ls)
  | bvar : Lookup Γ i A → TypeRecovery D depth Γ (.bvar i) A
  | lam : TypeRecovery D depth (A :: Γ) b B → TypeRecovery D depth Γ (.lam A b) (.forallE A B)
  | app : TypeRecovery D depth Γ f (.forallE A B) →
      TypeRecovery D depth Γ (.app f a) (B.inst a)
  | forallE : env.HasType univs Γ A (.sort u) → env.HasType univs (A :: Γ) B (.sort v) →
      TypeRecovery D depth Γ (.forallE A B) (.sort (.imax u v))
  | convert : TypeRecovery D depth Γ e T → CertifiedKCompute D depth Γ T T' →
      TypeRecovery D depth Γ e T'

/-- Recovery certificates survive finite binder insertion, including computation
of inferred types and the universe choices in Pi formation. -/
theorem TypeRecovery.weakN (W : Ctx.LiftN n k Γ Γ') (R : TypeRecovery D depth Γ e T) :
    TypeRecovery D depth Γ' (e.liftN n k) (T.liftN n k) := by
  induction R generalizing k Γ' with
  | sort hu => exact .sort hu
  | const hc hl hn =>
    rw [((henv.ordered.closedC hc).instL).liftN_eq (Nat.zero_le _)]
    exact .const hc hl hn
  | bvar hl => exact .bvar (hl.weakN W)
  | lam _ ih => exact .lam (ih W.succ)
  | app _ ih =>
    simpa only [liftN, liftN_inst_hi] using TypeRecovery.app (ih W)
  | forallE hA hB => exact .forallE (hA.weakN henv.ordered W) (hB.weakN henv.ordered W.succ)
  | convert _ R ih => exact .convert (ih W) (R.weakN (fun W H => KCertificate.weakN W H) W)

/-- A known function type retypes the argument of a well-formed application,
using ordinary uniqueness of the function's two Pi typings. -/
theorem application_at_recovered_pi (hΓ : OnCtx Γ (env.IsType univs))
    (ht : VExpr.WF env univs Γ (.app f a))
    (hf : env.HasType univs Γ f (.forallE A B)) :
    env.HasType univs Γ (.app f a) (B.inst a) := by
  obtain ⟨A₀, B₀, hf₀, ha⟩ := ht.app_inv henv hΓ
  obtain ⟨⟨_, hA⟩, _⟩ := (hf₀.uniqU henv hΓ hf).forallE_inv henv hΓ
  exact .app hf (hA.defeq ha)

/-- Reconstruction is sound at every well-formed source, without assuming a
typing at its displayed result type in advance. -/
theorem TypeRecovery.hasType (R : TypeRecovery D depth Γ e T)
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : VExpr.WF env univs Γ e) :
    env.HasType univs Γ e T := by
  induction R with
  | sort hu => exact .sort hu
  | const hc hl hn => exact .const hc hl hn
  | bvar hl => exact .bvar hl
  | lam _ ih =>
    obtain ⟨⟨u, hA⟩, hb⟩ := ht.lam_inv henv hΓ
    exact .lam hA (ih ⟨hΓ, _, hA⟩ hb)
  | app _ ih =>
    obtain ⟨_, _, hf, _⟩ := ht.app_inv henv hΓ
    exact application_at_recovered_pi hΓ ht (ih hΓ ⟨_, hf⟩)
  | forallE hA hB => exact .forallE hA hB
  | convert _ R ih =>
    have ht := ih hΓ ht
    obtain ⟨u, hT⟩ := ht.isType henv hΓ
    exact (R.simAt heq hs (KCertificate.descends heq hs depth) hΓ _ hT).defeq ht

/-- A type-recovery certificate above a binder insertion reconstructs its
entire output type below, as well as its typing. Lambda annotations come from
the source syntax; computation steps supply their own scoped result and replay. -/
theorem TypeRecovery.descend (R : TypeRecovery D depth Γ' (e.lift' ρ) T)
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (W : Ctx.Lift' ρ Γ Γ') (hΓ : OnCtx Γ (env.IsType univs))
    (hΓ' : OnCtx Γ' (env.IsType univs)) (ht : VExpr.WF env univs Γ e) :
    ∃ T₀, T = T₀.lift' ρ ∧ env.HasType univs Γ e T₀ := by
  generalize hsource : e.lift' ρ = source at R
  induction R generalizing ρ Γ e with
  | sort hu =>
    cases lift'_eq_sort hsource
    exact ⟨_, rfl, .sort hu⟩
  | const hc hl hn =>
    cases lift'_eq_const hsource
    refine ⟨_, ?_, .const hc hl hn⟩
    exact ((henv.ordered.closedC hc).instL.lift'_eq .zero).symm
  | bvar hl =>
    cases e <;> cases hsource
    obtain ⟨A, hA, hl⟩ := hl.weakU_inv W
    exact ⟨A, hA, .bvar hl⟩
  | lam _ ih =>
    obtain ⟨A, b, rfl, rfl, rfl⟩ := lift'_eq_lam hsource
    obtain ⟨⟨u, hA⟩, hb⟩ := ht.lam_inv henv hΓ
    have hA' := hA.weak' henv.ordered W
    obtain ⟨B, rfl, hB⟩ := ih W.cons ⟨hΓ, _, hA⟩ ⟨hΓ', _, hA'⟩ hb rfl
    exact ⟨.forallE A B, rfl, .lam hA hB⟩
  | app _ ih =>
    obtain ⟨f, a, rfl, rfl, rfl⟩ := lift'_eq_app hsource
    obtain ⟨_, _, hf, _⟩ := ht.app_inv henv hΓ
    obtain ⟨T, hT, hf⟩ := ih W hΓ hΓ' ⟨_, hf⟩ rfl
    obtain ⟨A, B, rfl, rfl, rfl⟩ := lift'_eq_forallE hT.symm
    exact ⟨B.inst a, (lift'_inst_hi _ _ _).symm, application_at_recovered_pi hΓ ht hf⟩
  | forallE hAu hBv =>
    obtain ⟨A, B, rfl, rfl, rfl⟩ := lift'_eq_forallE hsource
    obtain ⟨_, ht⟩ := ht
    obtain ⟨⟨u₀, hA⟩, ⟨v₀, hB⟩⟩ := HasType.forallE_inv henv.ordered ht
    have hA' := hA.weak' henv.ordered W
    have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, _, hA⟩
    have hΓA' : OnCtx (_ :: _) (env.IsType univs) := ⟨hΓ', _, hA'⟩
    have hu := (hA'.uniqU henv hΓ' hAu).sort_inv henv hΓ'
    have hv := ((hB.weak' henv.ordered W.cons).uniqU henv hΓA' hBv).sort_inv henv hΓA'
    have hAu₀ := (IsDefEq.sortDF (hA.sort_r henv hΓ) (hAu.sort_r henv hΓ') hu).defeq hA
    have hBv₀ := (IsDefEq.sortDF (hB.sort_r henv hΓA)
      (hBv.sort_r henv hΓA') hv).defeq hB
    exact ⟨_, rfl, .forallE hAu₀ hBv₀⟩
  | convert _ R ih =>
    obtain ⟨T, rfl, heT⟩ := ih W hΓ hΓ' ht hsource
    obtain ⟨T', hT', H⟩ := CertifiedKCompute.descend R heq hs W hΓ hΓ'
    obtain ⟨u, hT⟩ := heT.isType henv hΓ
    exact ⟨T', hT', (H _ hT).defeq heT⟩

/-- A recovered Pi typing determines scoped eta annotations below. -/
theorem TypeRecovery.pi_below (R : TypeRecovery D depth Γ' (e.lift' ρ) (.forallE A B))
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (W : Ctx.Lift' ρ Γ Γ') (hΓ : OnCtx Γ (env.IsType univs))
    (hΓ' : OnCtx Γ' (env.IsType univs)) (ht : VExpr.WF env univs Γ e) :
    ∃ A₀ B₀, A = A₀.lift' ρ ∧ B = B₀.lift' ρ.cons ∧ env.HasType univs Γ e (.forallE A₀ B₀) := by
  obtain ⟨T, hT, ht⟩ := R.descend heq hs W hΓ hΓ' ht
  obtain ⟨A₀, B₀, rfl, hA, hB⟩ := lift'_eq_forallE hT.symm
  exact ⟨A₀, B₀, hA, hB, ht⟩

end Lean4Lean.VEnv.Strengthening
