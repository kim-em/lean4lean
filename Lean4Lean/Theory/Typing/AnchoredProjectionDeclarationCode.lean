import Lean4Lean.Theory.Typing.AnchoredRecordDeclarationPrefix
import Lean4Lean.Theory.Typing.AnchoredProjectionFieldFactor

/-! The record's exact declaration-prefix observations interpret the actual
primitive selector's field type. The two selected types come from the same
registered template, with no arbitrary assigned-type coherence premise. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

theorem FamilySeededCodeRows.recordSelectedFieldCode
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hle : sourceEnv ≤ env)
    {target : List VExpr} (formed : OnCtx target (env.IsType U))
    {info : VProjectionInfo} {domains : List VExpr} {result : VExpr}
    (shape : info.ctorType = wrapForalls domains result)
    {levels : List VLevel} {params indices : List VExpr} {count : Nat}
    (levelCount : levels.length = info.uvars) (paramCount : params.length = info.nparams)
    (fieldBound : info.nparams + count < domains.length)
    {expression : VExpr} {keys : List FamilyKey} {required : Footprint}
    (rows : FamilySeededCodeRows sourceEnv env U registry target required [] []
      (nativeCaptureSubst []) (fun _ => []) expression
      ((domains.map (·.instL levels)).take (info.nparams + count)) keys)
    (N : Nat) (bounded : ∀ key ∈ keys, key.rank ≤ N)
    {left right : VExpr} {demand : RecordData (Profile N)}
    (witness : RankedData.RecordWitness env U registry (relations env U registry N) target left right
      (mkApps (.const demand.family.name levels) (params ++ indices)) demand)
    (positions : (demand.fields.take count).map Prod.fst = List.range count)
    (requests : FamilyKey.uniform N keys bounded =
      demand.family.arguments.take params.length ++ (demand.fields.take count).map Prod.snd)
    {level : VLevel} {support : Profile n}
    (original : OriginalTypePayload sourceEnv env U registry
      ((domains.map (·.instL levels)).take (info.nparams + count)).reverse
      (domains[info.nparams + count].instL levels) (.sort level))
    (certificate : CodeCert env U registry target rows.terminalLocals
      (nativeCaptureSubst (keys.map (·.key.anchor)))
      (domains[info.nparams + count].instL levels) support required)
    {leftField rightField : VExpr}
    (leftSelected : info.fieldType demand.family.name levels params count left = some leftField)
    (rightSelected : info.fieldType demand.family.name levels params count right = some rightField) :
    TypeRelated env U registry target leftField rightField support := by
  obtain ⟨replay⟩ := rows.recordFieldCode henv hscoped hle formed N bounded witness count
    positions requests original certificate
  have left := Option.some.inj (leftSelected.symm.trans
    (info.fieldType_eq_instOuter shape levelCount paramCount fieldBound))
  have right := Option.some.inj (rightSelected.symm.trans
    (info.fieldType_eq_instOuter shape levelCount paramCount fieldBound))
  rw [VExpr.instOuter_eq_subst] at left right
  rw [left, right]
  exact replay.related

end Lean4Lean.AnchoredSource.Adapted
