import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStageSubstitution

/-! # Reflecting ordinary computation through atomic substitutions

Variables, sorts and proof markers introduce no lambda, constant or projection
head. Substituting these atoms therefore creates no ordinary redex. This is a
backward path theorem, distinct from substitution's usual forward closure.
-/
namespace Lean4Lean.VEnv.Strengthening.ProofShape
open _root_.Lean4Lean
variable {e : ProofShape}

/-- Raw substitution images that cannot introduce an ordinary redex head. -/
inductive SubstitutionAtom : ProofShape → Prop where
  | bvar : SubstitutionAtom (.bvar i)
  | sort : SubstitutionAtom (.sort u)
  | proof : SubstitutionAtom .proof

/-- Every image is a variable, sort or proof marker. No injectivity is needed. -/
def AtomicSubstitution (σ : Subst) : Prop := ∀ i, SubstitutionAtom (σ i)

/-- Binder insertion preserves the three possible atomic shapes. -/
theorem SubstitutionAtom.liftN (H : SubstitutionAtom a) : SubstitutionAtom (a.liftN n k) := by
  cases H <;> constructor

/-- Entering a binder preserves atomic images. -/
theorem AtomicSubstitution.lift (H : AtomicSubstitution σ) : AtomicSubstitution σ.lift := by
  intro i
  cases i with
  | zero => exact .bvar
  | succ i => exact (H i).liftN

/-- A single atomic argument, with older variables retained, is atomic. -/
theorem SubstitutionAtom.one (H : SubstitutionAtom a) : AtomicSubstitution (Subst.one a) := by
  intro i
  cases i with
  | zero => exact H
  | succ i => exact .bvar

/-- Atomic images cannot create an application node. -/
theorem AtomicSubstitution.app_inv (H : AtomicSubstitution σ) (E : e.subst σ = .app f a) :
    ∃ f₀ a₀, e = .app f₀ a₀ ∧ f₀.subst σ = f ∧ a₀.subst σ = a := by
  cases e <;> simp only [subst] at E
  case bvar i =>
    have HA := H i
    generalize σ i = x at HA E
    cases HA <;> cases E
  all_goals first | cases E; exact ⟨_, _, rfl, rfl, rfl⟩ | cases E

/-- Atomic images cannot create a lambda node. -/
theorem AtomicSubstitution.lam_inv (H : AtomicSubstitution σ) (E : e.subst σ = .lam A b) :
    ∃ A₀ b₀, e = .lam A₀ b₀ ∧ A₀.subst σ = A ∧ b₀.subst σ.lift = b := by
  cases e <;> simp only [subst] at E
  case bvar i =>
    have HA := H i
    generalize σ i = x at HA E
    cases HA <;> cases E
  all_goals first | cases E; exact ⟨_, _, rfl, rfl, rfl⟩ | cases E

/-- Atomic images cannot create a Pi node. -/
theorem AtomicSubstitution.pi_inv (H : AtomicSubstitution σ) (E : e.subst σ = .forallE A B) :
    ∃ A₀ B₀, e = .forallE A₀ B₀ ∧ A₀.subst σ = A ∧ B₀.subst σ.lift = B := by
  cases e <;> simp only [subst] at E
  case bvar i =>
    have HA := H i
    generalize σ i = x at HA E
    cases HA <;> cases E
  all_goals first | cases E; exact ⟨_, _, rfl, rfl, rfl⟩ | cases E

/-- Atomic images cannot create a projection node. -/
theorem AtomicSubstitution.proj_inv (H : AtomicSubstitution σ) (E : e.subst σ = .proj s i m) :
    ∃ m₀, e = .proj s i m₀ ∧ m₀.subst σ = m := by
  cases e <;> simp only [subst] at E
  case bvar i =>
    have HA := H i
    generalize σ i = x at HA E
    cases HA <;> cases E
  all_goals first | cases E; exact ⟨_, rfl, rfl⟩ | cases E

/-- Atomic images cannot create a constant or change its universe arguments. -/
theorem AtomicSubstitution.const_inv (H : AtomicSubstitution σ) (E : e.subst σ = .const c ls) :
    e = .const c ls := by
  cases e <;> simp only [subst] at E
  case bvar i =>
    have HA := H i
    generalize σ i = x at HA E
    cases HA <;> cases E
  all_goals cases E <;> rfl

/-- A whole constant spine reflects, retaining the exact original arguments. -/
theorem AtomicSubstitution.const_spine_inv (H : AtomicSubstitution σ)
    (E : e.subst σ = mkApps (.const c ls) args) :
    ∃ args₀, e = mkApps (.const c ls) args₀ ∧ args₀.map (·.subst σ) = args := by
  induction args using List.snoc_induction generalizing e with
  | nil => exact ⟨[], H.const_inv E, rfl⟩
  | snoc args a ih =>
    rw [mkApps_snoc] at E
    obtain ⟨f₀, a₀, rfl, EF, EA⟩ := H.app_inv E
    obtain ⟨args₀, rfl, Eargs⟩ := ih EF
    exact ⟨args₀ ++ [a₀], mkApps_snoc.symm, by simp only [List.map_append, List.map_cons, List.map_nil, Eargs, EA]⟩

/-- Every beta path after atomic substitution is the exact image of a beta
path before substitution, including all computation under binders. -/
theorem BetaRed.atomic_subst_inv (H : AtomicSubstitution σ) (R : BetaRed (e.subst σ) out) :
    ∃ e', BetaRed e e' ∧ e'.subst σ = out := by
  generalize E : e.subst σ = source at R
  induction R generalizing e σ with
  | refl => exact ⟨e, .refl, E⟩
  | trans _ _ ih₁ ih₂ =>
    obtain ⟨mid, RM, EM⟩ := ih₁ H E
    obtain ⟨out, RO, EO⟩ := ih₂ H EM
    exact ⟨out, RM.trans RO, EO⟩
  | app _ _ ihf iha =>
    obtain ⟨f, a, rfl, EF, EA⟩ := H.app_inv E
    obtain ⟨f', RF, rfl⟩ := ihf H EF
    obtain ⟨a', RA, rfl⟩ := iha H EA
    exact ⟨_, .app RF RA, rfl⟩
  | proj _ ih =>
    obtain ⟨m, rfl, EM⟩ := H.proj_inv E
    obtain ⟨m', RM, rfl⟩ := ih H EM
    exact ⟨_, .proj RM, rfl⟩
  | lam _ _ ihA ihb =>
    obtain ⟨A, b, rfl, EA, EB⟩ := H.lam_inv E
    obtain ⟨A', RA, rfl⟩ := ihA H EA
    obtain ⟨b', RB, rfl⟩ := ihb H.lift EB
    exact ⟨_, .lam RA RB, rfl⟩
  | forallE _ _ ihA ihB =>
    obtain ⟨A, B, rfl, EA, EB⟩ := H.pi_inv E
    obtain ⟨A', RA, rfl⟩ := ihA H EA
    obtain ⟨B', RB, rfl⟩ := ihB H.lift EB
    exact ⟨_, .forallE RA RB, rfl⟩
  | beta =>
    obtain ⟨f, a, rfl, EF, rfl⟩ := H.app_inv E
    obtain ⟨A, b, rfl, rfl, rfl⟩ := H.lam_inv EF
    exact ⟨b.inst a, .beta, by rw [subst_inst]⟩

/-- Reflection of primitive roots extends to all compatible computation.
The hypothesis is an ordinary raw root property, independent of source typing. -/
theorem Compute.atomic_subst_inv
    (hroot : ∀ {σ a b}, AtomicSubstitution σ → Step (a.subst σ) b →
      ∃ a', Step a a' ∧ a'.subst σ = b)
    (H : AtomicSubstitution σ) (R : Compute Step (e.subst σ) out) :
    ∃ e', Compute Step e e' ∧ e'.subst σ = out := by
  generalize E : e.subst σ = source at R
  induction R generalizing e σ with
  | base R =>
    obtain ⟨e', RE, EE⟩ := hroot H (E.symm ▸ R)
    exact ⟨e', .base RE, EE⟩
  | beta R =>
    obtain ⟨e', RE, EE⟩ := (E.symm ▸ R).atomic_subst_inv H
    exact ⟨e', .beta RE, EE⟩
  | trans _ _ ih₁ ih₂ =>
    obtain ⟨mid, RM, EM⟩ := ih₁ H E
    obtain ⟨out, RO, EO⟩ := ih₂ H EM
    exact ⟨out, RM.trans RO, EO⟩
  | app _ _ ihf iha =>
    obtain ⟨f, a, rfl, EF, EA⟩ := H.app_inv E
    obtain ⟨f', RF, rfl⟩ := ihf H EF
    obtain ⟨a', RA, rfl⟩ := iha H EA
    exact ⟨_, .app RF RA, rfl⟩
  | proj _ ih =>
    obtain ⟨m, rfl, EM⟩ := H.proj_inv E
    obtain ⟨m', RM, rfl⟩ := ih H EM
    exact ⟨_, .proj RM, rfl⟩
  | lam _ _ ihA ihb =>
    obtain ⟨A, b, rfl, EA, EB⟩ := H.lam_inv E
    obtain ⟨A', RA, rfl⟩ := ihA H EA
    obtain ⟨b', RB, rfl⟩ := ihb H.lift EB
    exact ⟨_, .lam RA RB, rfl⟩
  | forallE _ _ ihA ihB =>
    obtain ⟨A, B, rfl, EA, EB⟩ := H.pi_inv E
    obtain ⟨A', RA, rfl⟩ := ihA H EA
    obtain ⟨B', RB, rfl⟩ := ihB H.lift EB
    exact ⟨_, .forallE RA RB, rfl⟩

end Lean4Lean.VEnv.Strengthening.ProofShape
