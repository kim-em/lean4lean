import Lean4Lean.Theory.Typing.AnchoredSortableHeadDepth
import Lean4Lean.Theory.Typing.AnchoredOriginalProjectionSortableSyntax

/-! Finite depth with an explicit computational-head policy. Every actual
source query/certificate child is traversed; only a named delta/native head
can mask its recursively computed child depth. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

noncomputable def RecipeResourceTransfer.headDepth (policy : Name → Nat → Nat)
    (transfer : RecipeResourceTransfer env U registry target locals σ required footprint) : Nat :=
  match transfer with
  | .nil => 0
  | .cons query tail => max (query.headDepth policy) (tail.headDepth policy)

theorem RecipeResourceTransfer.headDepth_zero (policy : Name → Nat → Nat)
    (zero : ∀ name, policy name 0 = 0)
    (transfer : RecipeResourceTransfer env U registry target locals σ required footprint) :
    transfer.headDepth policy = 0 := by
  induction transfer with
  | nil => rfl
  | cons query tail ih =>
    simp only [RecipeResourceTransfer.headDepth, query.headDepth_zero policy zero, ih, Nat.max_self]


mutual
noncomputable def RichCert.headDepth (policy : Name → Nat → Nat)
    (certificate : RichCert sourceEnv env U registry target node locals σ relevant profile footprint) : Nat :=
  match certificate with
  | .legacy source => source.headDepth policy
  | .recipe recipe => recipe.headDepth policy
  | .observe source _ => source.headDepth policy
  | .pi _ _ domain _ rows => max (domain.headDepth policy) (rows.headDepth policy)
  | .route _ source | .pad source | .down source | .map _ source | .support _ source
  | .select source _ => source.headDepth policy
  | .union first second => max (first.headDepth policy) (second.headDepth policy)
termination_by sizeOf certificate
decreasing_by all_goals simp_wf <;> omega

noncomputable def RichRows.headDepth (policy : Name → Nat → Nat)
    (rows : RichRows sourceEnv env U registry target domain body locals σ relevant ambient values footprint) : Nat :=
  match rows with
  | .nil => 0
  | .cons _ certificate _ _ tail => max (certificate.headDepth policy) (tail.headDepth policy)
termination_by sizeOf rows
decreasing_by all_goals simp_wf <;> omega

noncomputable def RichObs.headDepth (policy : Name → Nat → Nat)
    (observation : RichObs sourceEnv env U registry target node locals σ profile footprint) : Nat :=
  match observation with
  | .rigidFamily (name := name) (levels := levels) (node := node) _ _ _ _ _ _ _ _ _ _ _ certificate _ _ => certificate.headDepth policy
  | .family (name := name) (levels := levels) (node := node) _ _ _ _ _ _ _ _ _ _ _ certificate _ tree =>
    max (tree.headDepth policy) (certificate.headDepth policy)
  | .constructor (name := name) (levels := levels) (node := node) _ _ _ _ _ _ _ _ _ _ _ certificate _ tree =>
    max (tree.headDepth policy) (certificate.headDepth policy)
  | .canonicalDelta (name := name) (levels := levels) (node := node) _ _ _ _ _ _ _ _ _ certificate _ body =>
    policy name (max (body.headDepth policy) (certificate.headDepth policy))
  | .canonicalConst (name := name) (levels := levels) (node := node) origin _ child _ => policy origin.ownerName (child.headDepth policy)
  | .legacy source => source.headDepth policy
  | .code source => source.headDepth policy
  | .projection _ _ _ major field _ _ => max (major.headDepth policy) (field.headDepth policy)
  | .projectionSortable _ _ _ major _ _ _ field _ => max (major.headDepth policy) (field.headDepth policy)
  | .app _ _ fn arg _ _ => max (fn.headDepth policy) (arg.headDepth policy)
  | .lam _ _ domain _ body _ _ => max (domain.headDepth policy) (body.headDepth policy)
  | .route _ source | .view source _ | .action source _ | .select source _
  | .pad source | .unpad source => source.headDepth policy
  | .union first second => max (first.headDepth policy) (second.headDepth policy)
termination_by sizeOf observation
decreasing_by all_goals simp_wf <;> omega

noncomputable def RichFamilyPlan.headDepth (policy : Name → Nat → Nat)
    (plan : RichFamilyPlan env U registry target header name levels signature context σ arguments profile footprint) : Nat :=
  match plan with
  | .terminal _ _ _ captures => captures.headDepth policy
  | .binder _ _ _ _ domain _ body _ _ => max (domain.headDepth policy) (body.headDepth policy)
  | .view source _ | .pad source => source.headDepth policy
termination_by sizeOf plan
decreasing_by all_goals simp_wf <;> omega

noncomputable def RichConstructorPlan.headDepth (policy : Name → Nat → Nat)
    (plan : RichConstructorPlan env U registry target header name levels signature context σ arguments profile footprint) : Nat :=
  match plan with
  | .terminal _ _ _ _ _ _ captures resultCode => max (captures.headDepth policy) (resultCode.headDepth policy)
  | .terminalRecord _ _ _ _ _ _ _ _ _ captures resultCode _ =>
    max (captures.headDepth policy) (resultCode.headDepth policy)
  | .binder _ _ _ _ domain _ body _ _ => max (domain.headDepth policy) (body.headDepth policy)
  | .view source _ | .pad source => source.headDepth policy
termination_by sizeOf plan
decreasing_by all_goals simp_wf <;> omega

noncomputable def RichCodeRecipe.headDepth (policy : Name → Nat → Nat)
    (recipe : RichCodeRecipe env U registry target source locals σ expression relevant profile footprint) : Nat :=
  match recipe with
  | .root (name := name) _ _ _ _ _ _ _ _ certificate _ => policy name (certificate.headDepth policy)
  | .domain parent | .body parent _ _ | .fixedBody parent _ _ | .action _ parent => parent.headDepth policy
  | .resources parent transfer => max (parent.headDepth policy) (transfer.headDepth policy)
termination_by sizeOf recipe
decreasing_by all_goals simp_wf <;> omega

end

mutual
theorem RichCert.headDepth_zero (policy : Name → Nat → Nat) (zero : ∀ name, policy name 0 = 0)
    (certificate : RichCert sourceEnv env U registry target node locals σ relevant profile footprint) : certificate.headDepth policy = 0 := by
  match certificate with
  | .legacy source =>
    rw [RichCert.headDepth]
    change source.headDepth policy = 0
    simp only [source.headDepth_zero policy zero, Nat.max_self, zero]
  | .recipe recipe =>
    rw [RichCert.headDepth]
    exact recipe.headDepth_zero policy zero
  | .observe source _ =>
    rw [RichCert.headDepth]
    change source.headDepth policy = 0
    simp only [source.headDepth_zero policy zero, Nat.max_self, zero]
  | .pi _ _ domain _ rows =>
    rw [RichCert.headDepth]
    change max (domain.headDepth policy) (rows.headDepth policy) = 0
    simp only [domain.headDepth_zero policy zero, rows.headDepth_zero policy zero, Nat.max_self, zero]
  | .route _ source | .pad source | .down source | .map _ source | .support _ source
  | .select source _ =>
    rw [RichCert.headDepth]
    change source.headDepth policy = 0
    simp only [source.headDepth_zero policy zero, Nat.max_self, zero]
  | .union first second =>
    rw [RichCert.headDepth]
    change max (first.headDepth policy) (second.headDepth policy) = 0
    simp only [first.headDepth_zero policy zero, second.headDepth_zero policy zero, Nat.max_self, zero]
termination_by sizeOf certificate
decreasing_by all_goals simp_wf <;> omega

theorem RichRows.headDepth_zero (policy : Name → Nat → Nat) (zero : ∀ name, policy name 0 = 0)
    (rows : RichRows sourceEnv env U registry target domain body locals σ relevant ambient values footprint) : rows.headDepth policy = 0 := by
  match rows with
  | .nil => simp only [RichRows.headDepth]
  | .cons _ certificate _ _ tail =>
    rw [RichRows.headDepth]
    change max (certificate.headDepth policy) (tail.headDepth policy) = 0
    simp only [certificate.headDepth_zero policy zero, tail.headDepth_zero policy zero, Nat.max_self, zero]
termination_by sizeOf rows
decreasing_by all_goals simp_wf <;> omega

theorem RichObs.headDepth_zero (policy : Name → Nat → Nat) (zero : ∀ name, policy name 0 = 0)
    (observation : RichObs sourceEnv env U registry target node locals σ profile footprint) : observation.headDepth policy = 0 := by
  match observation with
  | .rigidFamily (name := name) (levels := levels) (node := node) _ _ _ _ _ _ _ _ _ _ _ certificate _ _ =>
    simpa only [RichObs.headDepth] using certificate.headDepth_zero policy zero
  | .family (name := name) (levels := levels) (node := node) _ _ _ _ _ _ _ _ _ _ _ certificate _ tree =>
    rw [RichObs.headDepth]
    change max (tree.headDepth policy) (certificate.headDepth policy) = 0
    simp only [tree.headDepth_zero policy zero, certificate.headDepth_zero policy zero, Nat.max_self, zero]
  | .constructor (name := name) (levels := levels) (node := node) _ _ _ _ _ _ _ _ _ _ _ certificate _ tree =>
    rw [RichObs.headDepth]
    change max (tree.headDepth policy) (certificate.headDepth policy) = 0
    simp only [tree.headDepth_zero policy zero, certificate.headDepth_zero policy zero, Nat.max_self, zero]
  | .canonicalDelta (name := name) (levels := levels) (node := node) _ _ _ _ _ _ _ _ _ certificate _ body =>
    rw [RichObs.headDepth]
    change policy name (max (body.headDepth policy) (certificate.headDepth policy)) = 0
    simp only [body.headDepth_zero policy zero, certificate.headDepth_zero policy zero, Nat.max_self, zero]
  | .canonicalConst (name := name) (levels := levels) (node := node) origin realization child resources =>
    rw [RichObs.headDepth]
    rw [child.headDepth_zero policy zero]
    exact zero origin.ownerName
  | .legacy source =>
    rw [RichObs.headDepth]
    change source.headDepth policy = 0
    simp only [source.headDepth_zero policy zero, Nat.max_self, zero]
  | .code source =>
    rw [RichObs.headDepth]
    change source.headDepth policy = 0
    simp only [source.headDepth_zero policy zero, Nat.max_self, zero]
  | .projection _ _ _ major field _ _ =>
    rw [RichObs.headDepth]
    change max (major.headDepth policy) (field.headDepth policy) = 0
    simp only [major.headDepth_zero policy zero, field.headDepth_zero policy zero, Nat.max_self, zero]
  | .projectionSortable _ _ _ major _ _ _ field _ =>
    rw [RichObs.headDepth]
    change max (major.headDepth policy) (field.headDepth policy) = 0
    simp only [major.headDepth_zero policy zero, field.headDepth_zero policy zero, Nat.max_self, zero]
  | .app _ _ fn arg _ _ =>
    rw [RichObs.headDepth]
    change max (fn.headDepth policy) (arg.headDepth policy) = 0
    simp only [fn.headDepth_zero policy zero, arg.headDepth_zero policy zero, Nat.max_self, zero]
  | .lam _ _ domain _ body _ _ =>
    rw [RichObs.headDepth]
    change max (domain.headDepth policy) (body.headDepth policy) = 0
    simp only [domain.headDepth_zero policy zero, body.headDepth_zero policy zero, Nat.max_self, zero]
  | .route _ source | .view source _ | .action source _ | .select source _
  | .pad source | .unpad source =>
    rw [RichObs.headDepth]
    change source.headDepth policy = 0
    simp only [source.headDepth_zero policy zero, Nat.max_self, zero]
  | .union first second =>
    rw [RichObs.headDepth]
    change max (first.headDepth policy) (second.headDepth policy) = 0
    simp only [first.headDepth_zero policy zero, second.headDepth_zero policy zero, Nat.max_self, zero]
termination_by sizeOf observation
decreasing_by all_goals simp_wf <;> omega

theorem RichFamilyPlan.headDepth_zero (policy : Name → Nat → Nat) (zero : ∀ name, policy name 0 = 0)
    (plan : RichFamilyPlan env U registry target header name levels signature context σ arguments profile footprint) : plan.headDepth policy = 0 := by
  match plan with
  | .terminal _ _ _ captures =>
    rw [RichFamilyPlan.headDepth]
    change captures.headDepth policy = 0
    simp only [captures.headDepth_zero policy zero, Nat.max_self, zero]
  | .binder _ _ _ _ domain _ body _ _ =>
    rw [RichFamilyPlan.headDepth]
    change max (domain.headDepth policy) (body.headDepth policy) = 0
    simp only [domain.headDepth_zero policy zero, body.headDepth_zero policy zero, Nat.max_self, zero]
  | .view source _ | .pad source =>
    rw [RichFamilyPlan.headDepth]
    change source.headDepth policy = 0
    simp only [source.headDepth_zero policy zero, Nat.max_self, zero]
termination_by sizeOf plan
decreasing_by all_goals simp_wf <;> omega

theorem RichConstructorPlan.headDepth_zero (policy : Name → Nat → Nat) (zero : ∀ name, policy name 0 = 0)
    (plan : RichConstructorPlan env U registry target header name levels signature context σ arguments profile footprint) : plan.headDepth policy = 0 := by
  match plan with
  | .terminal _ _ _ _ _ _ captures resultCode =>
    rw [RichConstructorPlan.headDepth]
    change max (captures.headDepth policy) (resultCode.headDepth policy) = 0
    simp only [captures.headDepth_zero policy zero, resultCode.headDepth_zero policy zero, Nat.max_self, zero]
  | .terminalRecord _ _ _ _ _ _ _ _ _ captures resultCode _ =>
    rw [RichConstructorPlan.headDepth]
    change max (captures.headDepth policy) (resultCode.headDepth policy) = 0
    simp only [captures.headDepth_zero policy zero, resultCode.headDepth_zero policy zero, Nat.max_self, zero]
  | .binder _ _ _ _ domain _ body _ _ =>
    rw [RichConstructorPlan.headDepth]
    change max (domain.headDepth policy) (body.headDepth policy) = 0
    simp only [domain.headDepth_zero policy zero, body.headDepth_zero policy zero, Nat.max_self, zero]
  | .view source _ | .pad source =>
    rw [RichConstructorPlan.headDepth]
    change source.headDepth policy = 0
    simp only [source.headDepth_zero policy zero, Nat.max_self, zero]
termination_by sizeOf plan
decreasing_by all_goals simp_wf <;> omega

theorem RichCodeRecipe.headDepth_zero (policy : Name → Nat → Nat) (zero : ∀ name, policy name 0 = 0)
    (recipe : RichCodeRecipe env U registry target source locals σ expression relevant profile footprint) :
    recipe.headDepth policy = 0 := by
  match recipe with
  | .root (name := name) _ _ _ _ _ _ _ _ certificate _ =>
    rw [RichCodeRecipe.headDepth]
    rw [certificate.headDepth_zero policy zero, zero]
  | .domain parent | .body parent _ _ | .fixedBody parent _ _ | .action _ parent =>
    rw [RichCodeRecipe.headDepth]
    exact parent.headDepth_zero policy zero
  | .resources parent transfer =>
    simp only [RichCodeRecipe.headDepth, parent.headDepth_zero policy zero,
      transfer.headDepth_zero policy zero, Nat.max_self]
termination_by sizeOf recipe
decreasing_by all_goals simp_wf <;> omega

end

noncomputable def RecipeResourceTransfer.stratifiedDepth (rank : Name → Nat) (control : Nat)
    (transfer : RecipeResourceTransfer env U registry target locals σ required footprint) : Nat :=
  transfer.headDepth (stratifiedHeadPolicy rank control)


noncomputable def RichCert.stratifiedDepth (rank : Name → Nat) (control : Nat)
    (certificate : RichCert sourceEnv env U registry target node locals σ relevant profile footprint) : Nat :=
  certificate.headDepth (stratifiedHeadPolicy rank control)
noncomputable def RichRows.stratifiedDepth (rank : Name → Nat) (control : Nat)
    (rows : RichRows sourceEnv env U registry target domain body locals σ relevant ambient values footprint) : Nat :=
  rows.headDepth (stratifiedHeadPolicy rank control)
noncomputable def RichObs.stratifiedDepth (rank : Name → Nat) (control : Nat)
    (observation : RichObs sourceEnv env U registry target node locals σ profile footprint) : Nat :=
  observation.headDepth (stratifiedHeadPolicy rank control)
noncomputable def RichFamilyPlan.stratifiedDepth (rank : Name → Nat) (control : Nat)
    (plan : RichFamilyPlan env U registry target header name levels signature context σ arguments profile footprint) : Nat :=
  plan.headDepth (stratifiedHeadPolicy rank control)
noncomputable def RichConstructorPlan.stratifiedDepth (rank : Name → Nat) (control : Nat)
    (plan : RichConstructorPlan env U registry target header name levels signature context σ arguments profile footprint) : Nat :=
  plan.headDepth (stratifiedHeadPolicy rank control)

noncomputable def RichCodeRecipe.stratifiedDepth (rank : Name → Nat) (control : Nat)
    (recipe : RichCodeRecipe env U registry target source locals σ expression relevant profile footprint) : Nat :=
  recipe.headDepth (stratifiedHeadPolicy rank control)

theorem RichCert.stratifiedDepth_above {maximum control : Nat} (rank : Name → Nat)
    (rankBound : ∀ name, rank name ≤ maximum) (above : maximum < control)
    (certificate : RichCert sourceEnv env U registry target node locals σ relevant profile footprint) : certificate.stratifiedDepth rank control = 0 := by
  apply certificate.headDepth_zero (stratifiedHeadPolicy rank control)
  intro name
  exact EquationStratifiedFuel.headDepth_above (Nat.lt_of_le_of_lt (rankBound name) above)

theorem RichRows.stratifiedDepth_above {maximum control : Nat} (rank : Name → Nat)
    (rankBound : ∀ name, rank name ≤ maximum) (above : maximum < control)
    (rows : RichRows sourceEnv env U registry target domain body locals σ relevant ambient values footprint) : rows.stratifiedDepth rank control = 0 := by
  apply rows.headDepth_zero (stratifiedHeadPolicy rank control)
  intro name
  exact EquationStratifiedFuel.headDepth_above (Nat.lt_of_le_of_lt (rankBound name) above)

theorem RichObs.stratifiedDepth_above {maximum control : Nat} (rank : Name → Nat)
    (rankBound : ∀ name, rank name ≤ maximum) (above : maximum < control)
    (observation : RichObs sourceEnv env U registry target node locals σ profile footprint) : observation.stratifiedDepth rank control = 0 := by
  apply observation.headDepth_zero (stratifiedHeadPolicy rank control)
  intro name
  exact EquationStratifiedFuel.headDepth_above (Nat.lt_of_le_of_lt (rankBound name) above)

theorem RichFamilyPlan.stratifiedDepth_above {maximum control : Nat} (rank : Name → Nat)
    (rankBound : ∀ name, rank name ≤ maximum) (above : maximum < control)
    (plan : RichFamilyPlan env U registry target header name levels signature context σ arguments profile footprint) : plan.stratifiedDepth rank control = 0 := by
  apply plan.headDepth_zero (stratifiedHeadPolicy rank control)
  intro name
  exact EquationStratifiedFuel.headDepth_above (Nat.lt_of_le_of_lt (rankBound name) above)

theorem RichConstructorPlan.stratifiedDepth_above {maximum control : Nat} (rank : Name → Nat)
    (rankBound : ∀ name, rank name ≤ maximum) (above : maximum < control)
    (plan : RichConstructorPlan env U registry target header name levels signature context σ arguments profile footprint) : plan.stratifiedDepth rank control = 0 := by
  apply plan.headDepth_zero (stratifiedHeadPolicy rank control)
  intro name
  exact EquationStratifiedFuel.headDepth_above (Nat.lt_of_le_of_lt (rankBound name) above)

theorem RichCodeRecipe.stratifiedDepth_above {maximum control : Nat} (rank : Name → Nat)
    (rankBound : ∀ name, rank name ≤ maximum) (above : maximum < control)
    (recipe : RichCodeRecipe env U registry target source locals σ expression relevant profile footprint) :
    recipe.stratifiedDepth rank control = 0 := by
  apply recipe.headDepth_zero (stratifiedHeadPolicy rank control)
  intro name
  exact EquationStratifiedFuel.headDepth_above (Nat.lt_of_le_of_lt (rankBound name) above)

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
