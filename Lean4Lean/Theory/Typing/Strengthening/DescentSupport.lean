import Lean4Lean.Theory.Typing.ChurchRosser
import Lean4Lean.Theory.Typing.ProjectionProofResult

/-! # Shared facts for descent of comparisons

These proofness and lift-inversion lemmas are reused from route A's
`NormalDescent.lean`, without importing its front predicates or strict comparison
relation. They use only `Params` and well-formedness, not the open strengthening
statement. The new domain-sensitive comparison uses them with an independent mode
that permits lambdas as well as neutral terms.
-/

namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean.VExpr VEnv.Params
variable [VEnv.Params]

local notation:65 Γ " ⊢ " e " : " A:36 => HasType Params.env univs Γ e A
local notation:65 Γ " ⊢ " e1 " ≡ " e2:36 " : " A:36 => IsDefEq Params.env univs Γ e1 e2 A
local notation:65 Γ " ⊢ " e1 " ≡ " e2:36 => IsDefEqU Params.env univs Γ e1 e2
local notation:65 Γ " ⊢ " e1 " ≡ₚ[" n "] " e2:30 => NormalEqN true n Γ e1 e2

/-! ## Syntactic predicates -/

/-- The term is a lambda. -/
def IsLam : VExpr → Prop
  | .lam .. => True
  | _ => False

/-- The term is a proof in `Γ`: typed at a proposition. -/
def IsProof (Γ : List VExpr) (e : VExpr) : Prop :=
  ∃ P, Γ ⊢ e : P ∧ Γ ⊢ P : .sort .zero

omit [VEnv.Params] in
theorem IsLam.lift'_iff {e : VExpr} {ρ : Lift} : IsLam (e.lift' ρ) ↔ IsLam e := by
  cases e <;> simp [IsLam, lift']

/-! ## Shape inversion of lifts -/

omit [VEnv.Params] in
theorem lift'_eq_app {e f a : VExpr} {ρ : Lift} (h : e.lift' ρ = .app f a) :
    ∃ f₀ a₀, e = .app f₀ a₀ ∧ f = f₀.lift' ρ ∧ a = a₀.lift' ρ := by
  cases e <;> simp [lift'] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨_, _, rfl, rfl, rfl⟩

omit [VEnv.Params] in
theorem lift'_eq_lam {e A b : VExpr} {ρ : Lift} (h : e.lift' ρ = .lam A b) :
    ∃ A₀ b₀, e = .lam A₀ b₀ ∧ A = A₀.lift' ρ ∧ b = b₀.lift' ρ.cons := by
  cases e <;> simp [lift'] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨_, _, rfl, rfl, rfl⟩

omit [VEnv.Params] in
theorem lift'_eq_forallE {e A B : VExpr} {ρ : Lift} (h : e.lift' ρ = .forallE A B) :
    ∃ A₀ B₀, e = .forallE A₀ B₀ ∧ A = A₀.lift' ρ ∧ B = B₀.lift' ρ.cons := by
  cases e <;> simp [lift'] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨_, _, rfl, rfl, rfl⟩

omit [VEnv.Params] in
theorem lift'_eq_proj {e m : VExpr} {S : Name} {i : Nat} {ρ : Lift}
    (h : e.lift' ρ = .proj S i m) : ∃ m₀, e = .proj S i m₀ ∧ m = m₀.lift' ρ := by
  cases e <;> simp [lift'] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  exact ⟨_, rfl, rfl⟩

omit [VEnv.Params] in
theorem lift'_eq_sort {e : VExpr} {u : VLevel} {ρ : Lift} (h : e.lift' ρ = .sort u) :
    e = .sort u := by
  cases e <;> simp [lift'] at h
  subst h; rfl

omit [VEnv.Params] in
theorem lift'_eq_const {e : VExpr} {c : Name} {ls : List VLevel} {ρ : Lift}
    (h : e.lift' ρ = .const c ls) : e = .const c ls := by
  cases e <;> simp [lift'] at h
  obtain ⟨rfl, rfl⟩ := h; rfl

omit [VEnv.Params] in
theorem lift_lift'_cons (e : VExpr) (ρ : Lift) : e.lift.lift' ρ.cons = (e.lift' ρ).lift := by
  rw [lift_eq_lift', ← lift'_comp, lift_eq_lift', ← lift'_comp]
  simp [Lift.comp]

/-! ## Proofs, sorts and lifts -/

/-- Sort levels are context-free: a type typed below whose lift is a proposition above is a
proposition below. -/
theorem HasType.prop_of_lift_prop (hΓ : OnCtx Γ (Params.env.IsType univs))
    (hΓ' : OnCtx Γ' (Params.env.IsType univs)) (W : Ctx.Lift' ρ Γ Γ')
    (hA : Γ ⊢ A : .sort u) (hP : Γ' ⊢ P : .sort .zero) (h : Γ' ⊢ A.lift' ρ ≡ P) :
    Γ ⊢ A : .sort .zero := by
  have hA' : Γ' ⊢ A.lift' ρ : .sort u := hA.weak' henv W
  have hu := (h.of_l henv hΓ' hA' |>.uniqU henv hΓ' hP).sort_inv henv hΓ'
  exact (IsDefEq.sortDF (hA.sort_r henv.ordered hΓ) (by trivial) hu).defeq hA

/-- A term typed below whose lift is a proof above is a proof below. -/
theorem IsProof.of_lift (hΓ : OnCtx Γ (Params.env.IsType univs))
    (hΓ' : OnCtx Γ' (Params.env.IsType univs)) (W : Ctx.Lift' ρ Γ Γ')
    (he : Γ ⊢ e : A) (hP : Γ' ⊢ P : .sort .zero) (hp : Γ' ⊢ e.lift' ρ : P) : IsProof Γ e := by
  have he' : Γ' ⊢ e.lift' ρ : A.lift' ρ := he.weak' henv W
  obtain ⟨u, hA⟩ := he.isType henv.ordered hΓ
  exact ⟨A, he, HasType.prop_of_lift_prop hΓ hΓ' W hA hP (he'.uniqU henv hΓ' hp)⟩

/-- A proof below is a proof above. -/
theorem IsProof.lift' (W : Ctx.Lift' ρ Γ Γ') (h : IsProof Γ e) : IsProof Γ' (e.lift' ρ) :=
  let ⟨P, he, hP⟩ := h
  ⟨P.lift' ρ, he.weak' henv W, hP.weak' henv W⟩

/-- Proofness transfers across a conversion with a term typed below. -/
theorem IsProof.transfer (hΓ : OnCtx Γ (Params.env.IsType univs))
    (hΓ' : OnCtx Γ' (Params.env.IsType univs)) (W : Ctx.Lift' ρ Γ Γ')
    (ha : IsProof Γ a) (hb : Γ ⊢ b : B) (hab : Γ' ⊢ a.lift' ρ ≡ b.lift' ρ) : IsProof Γ b := by
  obtain ⟨P, haP, hP⟩ := ha
  have haP' : Γ' ⊢ a.lift' ρ : P.lift' ρ := haP.weak' henv W
  have hP' : Γ' ⊢ P.lift' ρ : .sort .zero := hP.weak' henv W
  exact IsProof.of_lift hΓ hΓ' W hb hP' (hab.of_l henv hΓ' haP').hasType.2

/-- A pair of proofs typed below at convertible types is convertible below. -/
theorem IsProof.descend (hΓ : OnCtx Γ (Params.env.IsType univs))
    (ha : IsProof Γ a) (haA : Γ ⊢ a : A) (hb : Γ ⊢ b : B) (hAB : Γ ⊢ A ≡ B) : Γ ⊢ a ≡ b := by
  obtain ⟨P, haP, hP⟩ := ha
  have hAP := haA.uniqU henv hΓ haP
  have hbP : Γ ⊢ b : P := hb.defeqU_r henv hΓ (hAB.symm.trans henv hΓ hAP)
  exact ⟨_, .proofIrrel hP haP hbP⟩

/-- The function of a non-proof application is not a proof. -/
theorem IsProof.app_fn (hΓ : OnCtx Γ (Params.env.IsType univs))
    (hf : Γ ⊢ f : .forallE A B) (ha : Γ ⊢ a : A) (hp : IsProof Γ f) :
    IsProof Γ (.app f a) := by
  obtain ⟨P, hfP, hP⟩ := hp
  obtain ⟨⟨u, hA⟩, v, hB⟩ := (hf.isType henv.ordered hΓ).forallE_inv henv.ordered
  have hPi : Γ ⊢ .forallE A B : .sort (.imax u v) := .forallE hA hB
  have hPiP : Γ ⊢ .forallE A B : .sort .zero := hP.defeqU_l henv hΓ (hfP.uniqU henv hΓ hf)
  have huv := (hPi.uniqU henv hΓ hPiP).sort_inv henv hΓ
  have hv : v ≈ .zero := VLevel.imax_eq_zero.1 huv
  have hBa : Γ ⊢ B.inst a : .sort v := hB.instN henv.ordered Ctx.InstN.zero ha
  have hΓA : OnCtx (A :: Γ) (Params.env.IsType univs) := ⟨hΓ, u, hA⟩
  exact ⟨_, hf.app ha, (IsDefEq.sortDF (hB.sort_r henv.ordered hΓA) (by trivial) hv).defeq hBa⟩

theorem not_isProof_fn (hΓ : OnCtx Γ (Params.env.IsType univs))
    (hf : Γ ⊢ f : .forallE A B) (ha : Γ ⊢ a : A) (hn : ¬ IsProof Γ (.app f a)) : ¬ IsProof Γ f :=
  fun h => hn (IsProof.app_fn hΓ hf ha h)

/-- The major of a non-proof projection is not a proof. -/
theorem not_isProof_major (hΓ : OnCtx Γ (Params.env.IsType univs))
    (hp : Γ ⊢ .proj S i m : T) (hn : ¬ IsProof Γ (.proj S i m)) : ¬ IsProof Γ m :=
  fun ⟨_, hmP, hP⟩ => hn ⟨T, hp, hp.proj_result_prop_of_major_proof henv hΓ hP hmP⟩

/-- A lambda is not typed at a rigid structure family. -/
theorem not_isLam_major (hΓ : OnCtx Γ (Params.env.IsType univs))
    (hp : Γ ⊢ .proj S i m : T) : ¬ IsLam m := by
  intro hl
  obtain ⟨A, b, rfl⟩ : ∃ A b, m = .lam A b := by cases m <;> simp [IsLam] at hl; exact ⟨_, _, rfl⟩
  obtain ⟨info, levels, params, indexArgs, sourceMajor, _, _, hinfo, _, _, _, _, _, _, hmajor, _, _⟩ :=
    hp.proj_inv henv hΓ
  obtain ⟨B, hPi, -⟩ := hmajor.hasType.2.lam_inv_forallE henv hΓ
  have hS : Γ ⊢ VExpr.mkApps (.const S levels) (params ++ indexArgs) : .sort _ :=
    (hmajor.isType henv.ordered hΓ).choose_spec
  exact IsDefEqU.rigidApp_forallE_inv henv hΓ (henv.projectionRigid hinfo) hS hPi.symm


/-- A term typed at a sort cannot itself be a proof. -/
theorem not_isProof_of_sort (hΓ : OnCtx Γ (Params.env.IsType univs))
    (he : Γ ⊢ e : .sort u) : ¬ IsProof Γ e := by
  rintro ⟨P, heP, hP⟩
  have h1 : Γ ⊢ .sort u ≡ P := he.uniqU henv hΓ heP
  have h2 : Γ ⊢ .sort u : .sort .zero := hP.defeqU_l henv hΓ h1.symm
  have h3 : Γ ⊢ .sort u : .sort (.succ u) := HasType.sort (he.sort_r henv.ordered hΓ)
  have hu := (h3.uniqU henv hΓ h2).sort_inv henv hΓ
  have := congrFun hu []
  simp [VLevel.eval] at this

/-- A lambda with a proof body is a proof, by impredicativity. -/
theorem IsProof.lam (hΓ : OnCtx Γ (Params.env.IsType univs))
    (hA : Γ ⊢ A : .sort u) (hp : IsProof (A :: Γ) b) :
    IsProof Γ (.lam A b) := by
  obtain ⟨P, hb, hP⟩ := hp
  refine ⟨.forallE A P, .lam hA hb, ?_⟩
  have hPi : Γ ⊢ .forallE A P : .sort (.imax u .zero) := .forallE hA hP
  exact (IsDefEq.sortDF (hPi.sort_r henv.ordered hΓ) (by trivial)
    VLevel.imax_zero).defeq hPi

end Lean4Lean.VEnv.Strengthening
