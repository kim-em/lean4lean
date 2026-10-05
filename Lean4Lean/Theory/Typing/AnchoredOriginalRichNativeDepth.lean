import Lean4Lean.Theory.Typing.AnchoredOriginalProjectionSortableSyntax
import Lean4Lean.Theory.Typing.AnchoredSortableNativeDepth

/-! Rich declaration fuel includes recursive queries in their actual earlier
source environments. Declaration metadata and target guards do not consume
fuel; a named delta head adds exactly one unit. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles OriginalClosureMeasure
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

noncomputable def RecipeResourceTransfer.nativeDepth (current : Name → Bool)
    (transfer : RecipeResourceTransfer env U registry target locals σ required footprint) : Nat :=
  match transfer with
  | .nil => 0
  | .cons query tail => max (query.nativeDepth current) (tail.nativeDepth current)


mutual
noncomputable def RichCert.nativeDepth (current : Name → Bool)
    (certificate : RichCert sourceEnv env U registry target node locals σ relevant profile footprint) : Nat :=
  match certificate with
  | .legacy source => source.nativeDepth current
  | .recipe recipe => recipe.nativeDepth current
  | .observe source _ => source.nativeDepth current
  | .pi _ _ domain _ rows => max (domain.nativeDepth current) (rows.nativeDepth current)
  | .route _ source | .pad source | .down source | .map _ source | .support _ source
  | .select source _ => source.nativeDepth current
  | .union first second => max (first.nativeDepth current) (second.nativeDepth current)
termination_by sizeOf certificate
decreasing_by all_goals simp_wf <;> omega

noncomputable def RichRows.nativeDepth (current : Name → Bool)
    (rows : RichRows sourceEnv env U registry target domain body locals σ relevant ambient values footprint) : Nat :=
  match rows with
  | .nil => 0
  | .cons _ certificate _ _ tail => max (certificate.nativeDepth current) (tail.nativeDepth current)
termination_by sizeOf rows
decreasing_by all_goals simp_wf <;> omega

noncomputable def RichObs.nativeDepth (current : Name → Bool)
    (observation : RichObs sourceEnv env U registry target node locals σ profile footprint) : Nat :=
  match observation with
  | .rigidFamily (name := name) (levels := levels) (node := node) _ _ _ _ _ _ _ _ _ _ _ certificate _ _ => certificate.nativeDepth current
  | .family (name := name) (levels := levels) (node := node) _ _ _ _ _ _ _ _ _ _ _ certificate _ tree =>
    max (tree.nativeDepth current) (certificate.nativeDepth current)
  | .constructor (name := name) (levels := levels) (node := node) _ _ _ _ _ _ _ _ _ _ _ certificate _ tree =>
    max (tree.nativeDepth current) (certificate.nativeDepth current)
  | .canonicalDelta (name := name) (levels := levels) (node := node) _ _ _ _ _ _ _ _ _ certificate _ body =>
    max (body.nativeDepth current) (certificate.nativeDepth current) + if current name then 1 else 0
  | .canonicalConst (name := name) (levels := levels) (node := node) origin _ child _ => child.nativeDepth current + if current origin.ownerName then 1 else 0
  | .legacy source => source.nativeDepth current
  | .code source => source.nativeDepth current
  | .projection _ _ _ major field _ _ => max (major.nativeDepth current) (field.nativeDepth current)
  | .projectionSortable _ _ _ major _ _ _ field _ => max (major.nativeDepth current) (field.nativeDepth current)
  | .app _ _ fn arg _ _ => max (fn.nativeDepth current) (arg.nativeDepth current)
  | .lam _ _ domain _ body _ _ => max (domain.nativeDepth current) (body.nativeDepth current)
  | .route _ source | .view source _ | .action source _ | .select source _
  | .pad source | .unpad source => source.nativeDepth current
  | .union first second => max (first.nativeDepth current) (second.nativeDepth current)
termination_by sizeOf observation
decreasing_by all_goals simp_wf <;> omega

noncomputable def RichFamilyPlan.nativeDepth (current : Name → Bool)
    (plan : RichFamilyPlan env U registry target header name levels signature context σ arguments profile footprint) : Nat :=
  match plan with
  | .terminal _ _ _ captures => captures.nativeDepth current
  | .binder _ _ _ _ domain _ body _ _ => max (domain.nativeDepth current) (body.nativeDepth current)
  | .view source _ | .pad source => source.nativeDepth current
termination_by sizeOf plan
decreasing_by all_goals simp_wf <;> omega

noncomputable def RichConstructorPlan.nativeDepth (current : Name → Bool)
    (plan : RichConstructorPlan env U registry target header name levels signature context σ arguments profile footprint) : Nat :=
  match plan with
  | .terminal _ _ _ _ _ _ captures resultCode => max (captures.nativeDepth current) (resultCode.nativeDepth current)
  | .terminalRecord _ _ _ _ _ _ _ _ _ captures resultCode _ =>
    max (captures.nativeDepth current) (resultCode.nativeDepth current)
  | .binder _ _ _ _ domain _ body _ _ => max (domain.nativeDepth current) (body.nativeDepth current)
  | .view source _ | .pad source => source.nativeDepth current
termination_by sizeOf plan
decreasing_by all_goals simp_wf <;> omega

noncomputable def RichCodeRecipe.nativeDepth (current : Name → Bool)
    (recipe : RichCodeRecipe env U registry target source locals σ expression relevant profile footprint) : Nat :=
  match recipe with
  | .root (name := name) _ _ _ _ _ _ _ _ certificate _ =>
      certificate.nativeDepth current + if current name then 1 else 0
  | .domain parent | .body parent _ _ | .fixedBody parent _ _ | .action _ parent => parent.nativeDepth current
  | .resources parent transfer => max (parent.nativeDepth current) (transfer.nativeDepth current)
termination_by sizeOf recipe
decreasing_by all_goals simp_wf <;> omega

end

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
