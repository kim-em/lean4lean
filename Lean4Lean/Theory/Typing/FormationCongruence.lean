import Lean4Lean.Theory.Typing.Strong

/-! Formation-directed congruence, parameterized by independently established
assigned-type compatibility. No use of UniqueTyping or field inversion. -/
namespace Lean4Lean.VEnv
open VExpr

def AssignedTypeCompatibility (env : VEnv) (U : Nat) : Prop :=
  ∀ {Γ e A B}, OnCtx Γ (env.IsType U) →
    env.HasType U Γ e A → env.HasType U Γ e B → ∃ u, env.IsDefEq U Γ A B (.sort u)

theorem IsDefEqU.atLeftTypeOfCompatibility
    (compatible : AssignedTypeCompatibility env U)
    (formed : OnCtx Γ (env.IsType U))
    (typed : env.HasType U Γ left A)
    (equal : env.IsDefEqU U Γ left right) : env.IsDefEq U Γ left right A := by
  obtain ⟨_, equal⟩ := equal
  obtain ⟨_, types⟩ := compatible formed equal.hasType.1 typed
  exact .defeqDF types equal

theorem projectionCongruenceOfTyping
    (ordered : env.Ordered) (compatible : AssignedTypeCompatibility env U)
    (formed : OnCtx Γ (env.IsType U))
    (typed : env.HasType U Γ (.proj name index major) assigned)
    (majorEqual : env.IsDefEqU U Γ major other) :
    env.IsDefEqU U Γ (.proj name index major) (.proj name index other) := by
  obtain ⟨info, levels, params, indices, sourceMajor, field, level,
    registered, levelsWF, levelCount, paramCount, indexCount, selected,
    fieldTyped, sourcePath, closed, guard⟩ := typed.proj_inv ordered formed
  have majorPath := majorEqual.atLeftTypeOfCompatibility compatible formed sourcePath.hasType.2
  exact ⟨_, .projDF registered levelsWF levelCount paramCount indexCount selected
    fieldTyped sourcePath (sourcePath.trans majorPath) closed guard⟩

/-- A finite syntactic comparison tree. Only cuts carry equalities; compound
nodes must be justified from the actual left formation. Binder children live
in the actual LEFT domain context, so no total typed substitution is assumed. -/
inductive FormationComparison (env : VEnv) (U : Nat) : List VExpr → VExpr → VExpr → Prop where
  | cut : env.IsDefEqU U Γ left right → FormationComparison env U Γ left right
  | app : FormationComparison env U Γ f f' → FormationComparison env U Γ a a' →
      FormationComparison env U Γ (.app f a) (.app f' a')
  | proj : FormationComparison env U Γ major other →
      FormationComparison env U Γ (.proj name index major) (.proj name index other)
  | lam : FormationComparison env U Γ A A' → FormationComparison env U (A :: Γ) b b' →
      FormationComparison env U Γ (.lam A b) (.lam A' b')
  | pi : FormationComparison env U Γ A A' → FormationComparison env U (A :: Γ) B B' →
      FormationComparison env U Γ (.forallE A B) (.forallE A' B')

theorem FormationComparison.defeq
    (ordered : env.Ordered) (compatible : AssignedTypeCompatibility env U)
    (comparison : FormationComparison env U Γ left right)
    (formed : OnCtx Γ (env.IsType U)) (typed : env.HasType U Γ left assigned) :
    env.IsDefEqU U Γ left right := by
  induction comparison generalizing assigned with
  | cut equal => exact equal
  | app function argument ihf iha =>
    obtain ⟨A, B, hf, ha⟩ := typed.app_inv ordered formed
    exact ⟨_, .appDF ((ihf formed hf).atLeftTypeOfCompatibility compatible formed hf)
      ((iha formed ha).atLeftTypeOfCompatibility compatible formed ha)⟩
  | proj major ih =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, sourcePath, _, _⟩ :=
      typed.proj_inv ordered formed
    exact projectionCongruenceOfTyping ordered compatible formed typed
      (ih formed sourcePath.hasType.2)
  | lam domain body ihA ihB =>
    obtain ⟨⟨u, hA⟩, _, hB⟩ := typed.lam_inv ordered formed
    have domainEqual := (ihA formed hA).atLeftTypeOfCompatibility compatible formed hA
    have contextWF : OnCtx (_ :: _) (env.IsType U) := ⟨formed, _, hA⟩
    have bodyEqual := (ihB contextWF hB).atLeftTypeOfCompatibility
      compatible contextWF hB
    exact ⟨_, .lamDF domainEqual bodyEqual⟩
  | pi domain body ihA ihB =>
    obtain ⟨⟨u, hA⟩, ⟨v, hB⟩⟩ := typed.forallE_inv ordered
    exact ⟨_, .forallEDF ((ihA formed hA).atLeftTypeOfCompatibility compatible formed hA)
      ((ihB ⟨formed, _, hA⟩ hB).atLeftTypeOfCompatibility compatible ⟨formed, _, hA⟩ hB)⟩

/-- Only occurrences in the selected template request cut equalities. A cut
is demanded only when its actual instantiated occurrence is typed. Binder
demands use the left instantiated domain and lifted substitutions. -/
def FormationSubstitutionCuts (env : VEnv) (U : Nat)
    (Γ : List VExpr) (σ τ : Subst) : VExpr → Prop
  | .bvar i => OnCtx Γ (env.IsType U) → ∀ assigned, env.HasType U Γ (σ i) assigned → env.IsDefEqU U Γ (σ i) (τ i)
  | .sort _ | .const .. | .elim .. => True
  | .app f a => FormationSubstitutionCuts env U Γ σ τ f ∧ FormationSubstitutionCuts env U Γ σ τ a
  | .proj _ _ major => FormationSubstitutionCuts env U Γ σ τ major
  | .lam A body | .forallE A body =>
      FormationSubstitutionCuts env U Γ σ τ A ∧
      FormationSubstitutionCuts env U (A.subst σ :: Γ) σ.lift τ.lift body

theorem FormationSubstitutionCuts.defeq
    (ordered : env.Ordered) (compatible : AssignedTypeCompatibility env U)
    (template : VExpr) (cuts : FormationSubstitutionCuts env U Γ σ τ template)
    (formed : OnCtx Γ (env.IsType U))
    (typed : env.HasType U Γ (template.subst σ) assigned) :
    env.IsDefEqU U Γ (template.subst σ) (template.subst τ) := by
  induction template generalizing Γ σ τ assigned with
  | bvar i => exact cuts formed assigned typed
  | sort | const | elim => exact ⟨_, typed⟩
  | app f a ihf iha =>
    obtain ⟨A, B, hf, ha⟩ := typed.app_inv ordered formed
    exact ⟨_, .appDF ((ihf cuts.1 formed hf).atLeftTypeOfCompatibility compatible formed hf)
      ((iha cuts.2 formed ha).atLeftTypeOfCompatibility compatible formed ha)⟩
  | proj name index major ih =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, sourcePath, _, _⟩ :=
      typed.proj_inv ordered formed
    exact projectionCongruenceOfTyping ordered compatible formed typed
      (ih cuts formed sourcePath.hasType.2)
  | lam A body ihA ihB =>
    obtain ⟨⟨u, hA⟩, _, hB⟩ := typed.lam_inv ordered formed
    have contextWF : OnCtx (A.subst σ :: Γ) (env.IsType U) := ⟨formed, _, hA⟩
    exact ⟨_, .lamDF ((ihA cuts.1 formed hA).atLeftTypeOfCompatibility compatible formed hA)
      ((ihB cuts.2 contextWF hB).atLeftTypeOfCompatibility compatible contextWF hB)⟩
  | forallE A body ihA ihB =>
    obtain ⟨⟨u, hA⟩, ⟨v, hB⟩⟩ := typed.forallE_inv ordered
    have contextWF : OnCtx (A.subst σ :: Γ) (env.IsType U) := ⟨formed, _, hA⟩
    exact ⟨_, .forallEDF ((ihA cuts.1 formed hA).atLeftTypeOfCompatibility compatible formed hA)
      ((ihB cuts.2 contextWF hB).atLeftTypeOfCompatibility compatible contextWF hB)⟩

end Lean4Lean.VEnv
