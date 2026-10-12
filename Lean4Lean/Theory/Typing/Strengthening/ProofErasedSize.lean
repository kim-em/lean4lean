import Lean4Lean.Theory.Typing.Strengthening.NormalDescent

/-! # The proof-erased size

`μ Γ e`: the number of nodes of `e` outside its proof subterms (`IsProof Γ e`, a term typed at
a proposition, counts `0`; every other node counts `1` plus its immediate subterms, binders
extending the context). It is the outer component of the lexicographic measure `(μ, n)` of the
normal-equality descent: the comparison index `n` is not preserved by the contraction of a
matched β-redex pair with proof arguments (`NormalEqF.contract_proofArgs`), but `μ` strictly
drops there, since the λ and application nodes disappear and substituting a proof for a proof
variable leaves `μ` unchanged (`μ_inst_proof`). Context conversion (`μ_defeqDFC`) and the
computation rules for non-proof nodes (`μ_app`, `μ_lam`, `μ_forallE`, `μ_proj`) are what the
descent needs under binders. -/

namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean.VExpr VEnv.Params Classical
variable [VEnv.Params]

local notation:65 Γ " ⊢ " e " : " A:36 => HasType Params.env univs Γ e A
local notation:65 Γ " ⊢ " e1 " ≡ " e2:36 " : " A:36 => IsDefEq Params.env univs Γ e1 e2 A
local notation:65 Γ " ⊢ " e1 " ≡ " e2:36 => IsDefEqU Params.env univs Γ e1 e2

/-- The proof-erased size: nodes inside proof subterms count `0`. -/
noncomputable def μ : List VExpr → VExpr → Nat
  | Γ, e@(.bvar _) => if IsProof Γ e then 0 else 1
  | Γ, e@(.sort _) => if IsProof Γ e then 0 else 1
  | Γ, e@(.const ..) => if IsProof Γ e then 0 else 1
  | Γ, e@(.app f a) => if IsProof Γ e then 0 else μ Γ f + μ Γ a + 1
  | Γ, e@(.lam A b) => if IsProof Γ e then 0 else μ Γ A + μ (A :: Γ) b + 1
  | Γ, e@(.forallE A B) => if IsProof Γ e then 0 else μ Γ A + μ (A :: Γ) B + 1
  | Γ, e@(.proj _ _ m) => if IsProof Γ e then 0 else μ Γ m + 1

theorem μ_proof (h : IsProof Γ e) : μ Γ e = 0 := by
  cases e <;> simp [μ, h]

theorem μ_bvar (h : ¬ IsProof Γ (.bvar i)) : μ Γ (.bvar i) = 1 := by simp [μ, h]
theorem μ_sort (h : ¬ IsProof Γ (.sort u)) : μ Γ (.sort u) = 1 := by simp [μ, h]
theorem μ_const (h : ¬ IsProof Γ (.const c ls)) : μ Γ (.const c ls) = 1 := by simp [μ, h]

theorem μ_app (h : ¬ IsProof Γ (.app f a)) : μ Γ (.app f a) = μ Γ f + μ Γ a + 1 := by
  simp [μ, h]

theorem μ_lam (h : ¬ IsProof Γ (.lam A b)) : μ Γ (.lam A b) = μ Γ A + μ (A :: Γ) b + 1 := by
  simp [μ, h]

theorem μ_proj (h : ¬ IsProof Γ (.proj S i m)) : μ Γ (.proj S i m) = μ Γ m + 1 := by
  simp [μ, h]

/-- A term typed at a sort is not a proof (its type's sort is a successor, not `0`). -/
theorem not_isProof_of_sort (hΓ : OnCtx Γ (Params.env.IsType univs)) (he : Γ ⊢ e : .sort u) :
    ¬ IsProof Γ e := by
  rintro ⟨P, heP, hP⟩
  have h1 : Γ ⊢ .sort u ≡ P := he.uniqU henv hΓ heP
  have h2 : Γ ⊢ .sort u : .sort .zero := hP.defeqU_l henv hΓ h1.symm
  have h3 : Γ ⊢ .sort u : .sort (.succ u) := HasType.sort (he.sort_r henv.ordered hΓ)
  have hu := (h3.uniqU henv hΓ h2).sort_inv henv hΓ
  have := congrFun hu []
  simp [VLevel.eval] at this

/-- A `Π` is never a proof. -/
theorem not_isProof_forallE (hΓ : OnCtx Γ (Params.env.IsType univs)) :
    ¬ IsProof Γ (.forallE A B) := by
  rintro ⟨P, hP, hP0⟩
  obtain ⟨⟨u, hA⟩, v, hB⟩ := hP.forallE_inv henv.ordered
  exact not_isProof_of_sort hΓ (HasType.forallE hA hB) ⟨P, hP, hP0⟩

theorem μ_forallE (hΓ : OnCtx Γ (Params.env.IsType univs)) :
    μ Γ (.forallE A B) = μ Γ A + μ (A :: Γ) B + 1 := by
  simp [μ, not_isProof_forallE hΓ]

/-! ## Context conversion -/

theorem IsDefEqCtx.symm' (W : IsDefEqCtx Params.env univs Γ₀ Γ₁ Γ₂) :
    IsDefEqCtx Params.env univs Γ₀ Γ₂ Γ₁ := by
  induction W with
  | zero => exact .zero
  | succ W h ih => exact .succ ih (h.symm.defeqDFC henv.ordered W)

theorem IsProof.defeqDFC (W : IsDefEqCtx Params.env univs Γ₀ Γ₁ Γ₂) (h : IsProof Γ₁ e) :
    IsProof Γ₂ e :=
  let ⟨P, heP, hP⟩ := h
  ⟨P, heP.defeqDFC henv.ordered W, hP.defeqDFC henv.ordered W⟩

theorem IsProof.defeqDFC_iff (W : IsDefEqCtx Params.env univs Γ₀ Γ₁ Γ₂) :
    IsProof Γ₁ e ↔ IsProof Γ₂ e :=
  ⟨IsProof.defeqDFC W, IsProof.defeqDFC (IsDefEqCtx.symm' W)⟩

/-- `μ` is invariant under conversion of the context, for typed terms. -/
theorem μ_defeqDFC (hΓ₁ : OnCtx Γ₁ (Params.env.IsType univs))
    (W : IsDefEqCtx Params.env univs Γ₀ Γ₁ Γ₂) (he : Γ₁ ⊢ e : T) : μ Γ₁ e = μ Γ₂ e := by
  induction e generalizing Γ₁ Γ₂ T with
  | bvar i => simp only [μ, IsProof.defeqDFC_iff W]
  | sort u => simp only [μ, IsProof.defeqDFC_iff W]
  | const c ls => simp only [μ, IsProof.defeqDFC_iff W]
  | app f a ihf iha =>
    obtain ⟨_, _, hf, ha⟩ := he.app_inv henv hΓ₁
    simp only [μ, IsProof.defeqDFC_iff W, ihf hΓ₁ W hf, iha hΓ₁ W ha]
  | lam A b ihA ihb =>
    obtain ⟨⟨u, hA⟩, _, hb⟩ := he.lam_inv henv hΓ₁
    have hΓ₁' : OnCtx (A :: Γ₁) (Params.env.IsType univs) := ⟨hΓ₁, u, hA⟩
    simp only [μ, IsProof.defeqDFC_iff W, ihA hΓ₁ W hA, ihb hΓ₁' (W.succ hA) hb]
  | forallE A B ihA ihB =>
    obtain ⟨⟨u, hA⟩, _, hB⟩ := he.forallE_inv henv.ordered
    have hΓ₁' : OnCtx (A :: Γ₁) (Params.env.IsType univs) := ⟨hΓ₁, u, hA⟩
    simp only [μ, IsProof.defeqDFC_iff W, ihA hΓ₁ W hA, ihB hΓ₁' (W.succ hA) hB]
  | proj S i m ih =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hmajor, _, _⟩ := he.proj_inv henv hΓ₁
    simp only [μ, IsProof.defeqDFC_iff W, ih hΓ₁ W hmajor.hasType.2]

/-! ## Substitution of a proof for a proof variable -/

/-- Proofness is invariant under instantiation, for typed terms: the type's sort is
unchanged by substitution. -/
theorem IsProof.instN_iff (hΓ₁ : OnCtx Γ₁ (Params.env.IsType univs)) (h₀ : Γ₀ ⊢ x : A₀)
    (W : Ctx.InstN Γ₀ x A₀ k Γ₁ Γ) (hs : Γ₁ ⊢ s : T) :
    IsProof Γ (s.inst x k) ↔ IsProof Γ₁ s := by
  have hΓ := (W.wf henv.ordered h₀ hΓ₁).2
  constructor
  · rintro ⟨P, hsP, hP⟩
    obtain ⟨u, hT⟩ := hs.isType henv.ordered hΓ₁
    have hs' : Γ ⊢ s.inst x k : T.inst x k := hs.instN henv.ordered W h₀
    have hT' : Γ ⊢ T.inst x k : .sort u := hT.instN henv.ordered W h₀
    have h1 : Γ ⊢ T.inst x k ≡ P := hs'.uniqU henv hΓ hsP
    have h2 : Γ ⊢ T.inst x k : .sort .zero := hP.defeqU_l henv hΓ h1.symm
    have hu := (hT'.uniqU henv hΓ h2).sort_inv henv hΓ
    exact ⟨T, hs, (IsDefEq.sortDF (hT.sort_r henv.ordered hΓ₁) (by trivial) hu).defeq hT⟩
  · rintro ⟨P, hsP, hP⟩
    exact ⟨P.inst x k, hsP.instN henv.ordered W h₀, hP.instN henv.ordered W h₀⟩

/-- Substituting a proof for a proof variable does not change `μ`, at any depth. -/
theorem μ_instN_proof (hΓ₁ : OnCtx Γ₁ (Params.env.IsType univs))
    (hA₀ : Γ₀ ⊢ A₀ : .sort .zero) (h₀ : Γ₀ ⊢ x : A₀)
    (W : Ctx.InstN Γ₀ x A₀ k Γ₁ Γ) (hs : Γ₁ ⊢ s : T) : μ Γ (s.inst x k) = μ Γ₁ s := by
  induction s generalizing Γ₁ Γ k T with
  | bvar i =>
    by_cases hp : IsProof Γ₁ (.bvar i)
    · rw [μ_proof hp, μ_proof ((IsProof.instN_iff hΓ₁ h₀ W hs).2 hp)]
    · have hp' : ¬ IsProof Γ (VExpr.inst (.bvar i) x k) := fun h =>
        hp ((IsProof.instN_iff hΓ₁ h₀ W hs).1 h)
      rw [μ_bvar hp]
      -- the substituted variable is a proof (its type is `A₀` lifted), so `i ≠ k`
      have hk : IsProof Γ₁ (.bvar k) := by
        clear hp hp' hs
        induction W with
        | zero => exact ⟨_, .bvar .zero, hA₀.weak henv.ordered⟩
        | @succ _ _ _ A W ih =>
          obtain ⟨P, hb, hP⟩ := ih hΓ₁.1
          refine ⟨P.lift, ?_, hP.weak henv.ordered⟩
          have h := hb.weak (B := A) henv.ordered
          simp only [lift, liftN, liftVar, Nat.add_comm, Nat.not_lt_zero, if_false] at h
          exact h
      have hik : i ≠ k := fun h => hp (h ▸ hk)
      simp only [inst, instVar] at hp' ⊢
      rcases Nat.lt_or_ge i k with hlt | hge
      · rw [if_pos hlt] at hp' ⊢; exact μ_bvar hp'
      · rw [if_neg (Nat.not_lt.mpr hge), if_neg hik] at hp' ⊢; exact μ_bvar hp'
  | sort u =>
    by_cases hp : IsProof Γ₁ (.sort u)
    · rw [μ_proof hp, μ_proof ((IsProof.instN_iff hΓ₁ h₀ W hs).2 hp)]
    · rw [μ_sort hp]; exact μ_sort (fun h => hp ((IsProof.instN_iff hΓ₁ h₀ W hs).1 h))
  | const c ls =>
    by_cases hp : IsProof Γ₁ (.const c ls)
    · rw [μ_proof hp, μ_proof ((IsProof.instN_iff hΓ₁ h₀ W hs).2 hp)]
    · rw [μ_const hp]; exact μ_const (fun h => hp ((IsProof.instN_iff hΓ₁ h₀ W hs).1 h))
  | app f a ihf iha =>
    obtain ⟨_, _, hf, ha⟩ := hs.app_inv henv hΓ₁
    by_cases hp : IsProof Γ₁ (.app f a)
    · rw [μ_proof hp, μ_proof ((IsProof.instN_iff hΓ₁ h₀ W hs).2 hp)]
    · have hp' := fun h => hp ((IsProof.instN_iff hΓ₁ h₀ W hs).1 h)
      simp only [inst] at hp' ⊢
      rw [μ_app hp, μ_app hp', ihf hΓ₁ W hf, iha hΓ₁ W ha]
  | lam A b ihA ihb =>
    obtain ⟨⟨u, hA⟩, _, hb⟩ := hs.lam_inv henv hΓ₁
    have hΓ₁' : OnCtx (A :: Γ₁) (Params.env.IsType univs) := ⟨hΓ₁, u, hA⟩
    by_cases hp : IsProof Γ₁ (.lam A b)
    · rw [μ_proof hp, μ_proof ((IsProof.instN_iff hΓ₁ h₀ W hs).2 hp)]
    · have hp' := fun h => hp ((IsProof.instN_iff hΓ₁ h₀ W hs).1 h)
      simp only [inst] at hp' ⊢
      rw [μ_lam hp, μ_lam hp', ihA hΓ₁ W hA, ihb hΓ₁' W.succ hb]
  | forallE A B ihA ihB =>
    obtain ⟨⟨u, hA⟩, _, hB⟩ := hs.forallE_inv henv.ordered
    have hΓ₁' : OnCtx (A :: Γ₁) (Params.env.IsType univs) := ⟨hΓ₁, u, hA⟩
    have hΓ := (W.wf henv.ordered h₀ hΓ₁).2
    simp only [inst]
    rw [μ_forallE hΓ₁, μ_forallE hΓ, ihA hΓ₁ W hA, ihB hΓ₁' W.succ hB]
  | proj S i m ih =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hmajor, _, _⟩ := hs.proj_inv henv hΓ₁
    by_cases hp : IsProof Γ₁ (.proj S i m)
    · rw [μ_proof hp, μ_proof ((IsProof.instN_iff hΓ₁ h₀ W hs).2 hp)]
    · have hp' := fun h => hp ((IsProof.instN_iff hΓ₁ h₀ W hs).1 h)
      simp only [inst] at hp' ⊢
      rw [μ_proj hp, μ_proj hp', ih hΓ₁ W hmajor.hasType.2]

/-- The depth-`0` form: substituting a proof `x : A` for the variable of `A :: Γ`. -/
theorem μ_inst_proof (hΓ : OnCtx Γ (Params.env.IsType univs)) (hA : Γ ⊢ A : .sort .zero)
    (hx : Γ ⊢ x : A) (hs : A :: Γ ⊢ s : T) : μ Γ (s.inst x) = μ (A :: Γ) s :=
  μ_instN_proof ⟨hΓ, _, hA⟩ hA hx .zero hs

/-! ## Renaming -/

/-- Proofness is invariant under renaming, for typed terms. -/
theorem IsProof.lift'_iff (hΓ : OnCtx Γ (Params.env.IsType univs))
    (hΓ' : OnCtx Γ' (Params.env.IsType univs)) (W : Ctx.Lift' ρ Γ Γ') (he : Γ ⊢ e : T) :
    IsProof Γ' (e.lift' ρ) ↔ IsProof Γ e :=
  ⟨fun ⟨_, hp, hP⟩ => IsProof.of_lift hΓ hΓ' W he hP hp, IsProof.lift' W⟩

/-- `μ` is invariant under renaming, for typed terms. -/
theorem μ_lift' (hΓ : OnCtx Γ (Params.env.IsType univs))
    (hΓ' : OnCtx Γ' (Params.env.IsType univs)) (W : Ctx.Lift' ρ Γ Γ') (he : Γ ⊢ e : T) :
    μ Γ' (e.lift' ρ) = μ Γ e := by
  have hp := IsProof.lift'_iff hΓ hΓ' W he
  induction e generalizing Γ Γ' ρ T with
  | bvar i =>
    simp only [lift'] at hp; simp only [lift', μ, hp]
  | sort u =>
    simp only [lift'] at hp; simp only [lift', μ, hp]
  | const c ls =>
    simp only [lift'] at hp; simp only [lift', μ, hp]
  | app f a ihf iha =>
    obtain ⟨_, _, hf, ha⟩ := he.app_inv henv hΓ
    simp only [lift'] at hp
    simp only [lift', μ, hp, ihf hΓ hΓ' W hf (IsProof.lift'_iff hΓ hΓ' W hf),
      iha hΓ hΓ' W ha (IsProof.lift'_iff hΓ hΓ' W ha)]
  | lam A b ihA ihb =>
    obtain ⟨⟨u, hA⟩, _, hb⟩ := he.lam_inv henv hΓ
    have hΓA : OnCtx (A :: Γ) (Params.env.IsType univs) := ⟨hΓ, u, hA⟩
    have hΓA' : OnCtx (A.lift' ρ :: Γ') (Params.env.IsType univs) :=
      ⟨hΓ', u, hA.weak' henv.ordered W⟩
    simp only [lift'] at hp
    simp only [lift', μ, hp, ihA hΓ hΓ' W hA (IsProof.lift'_iff hΓ hΓ' W hA),
      ihb hΓA hΓA' W.cons hb (IsProof.lift'_iff hΓA hΓA' W.cons hb)]
  | forallE A B ihA ihB =>
    obtain ⟨⟨u, hA⟩, _, hB⟩ := he.forallE_inv henv.ordered
    have hΓA : OnCtx (A :: Γ) (Params.env.IsType univs) := ⟨hΓ, u, hA⟩
    have hΓA' : OnCtx (A.lift' ρ :: Γ') (Params.env.IsType univs) :=
      ⟨hΓ', u, hA.weak' henv.ordered W⟩
    simp only [lift'] at hp
    simp only [lift', μ, hp, ihA hΓ hΓ' W hA (IsProof.lift'_iff hΓ hΓ' W hA),
      ihB hΓA hΓA' W.cons hB (IsProof.lift'_iff hΓA hΓA' W.cons hB)]
  | proj S i m ih =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hmajor, _, _⟩ := he.proj_inv henv hΓ
    simp only [lift'] at hp
    simp only [lift', μ, hp, ih hΓ hΓ' W hmajor.hasType.2
      (IsProof.lift'_iff hΓ hΓ' W hmajor.hasType.2)]

end Lean4Lean.VEnv.Strengthening
