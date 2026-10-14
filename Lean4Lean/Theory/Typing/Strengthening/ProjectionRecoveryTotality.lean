import Lean4Lean.Theory.Typing.Strengthening.ProjectionTypeRecovery
import Lean4Lean.Theory.Typing.ProjectionIndexBound

/-! # Field selection is total after recovering a projection family

The source projection fixes a valid field index. Rigid-family injectivity fixes
the lengths of the recovered levels and arguments. The registered constructor
shape then supplies a selected field for those recovered parameters.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr
variable {env : VEnv}

/-- Any family typing of the major of a well-formed projection admits field
selection. No separate success premise for the recovered parameters is needed. -/
theorem projection_recovered_field_exists (henv : env.WF)
    (hΓ : OnCtx Γ (env.IsType U)) (hi : env.projections s info)
    (ht : VExpr.WF env U Γ (.proj s i m))
    (hm : env.HasType U Γ m (mkApps (.const s ls) args)) :
    ∃ F, info.fieldType s ls (args.take info.nparams) i m = some F := by
  obtain ⟨_, ht⟩ := ht
  have hidx := HasType.proj_index_lt henv hΓ ht hi
  obtain ⟨info₀, ls₀, ps₀, is₀, sm₀, F₀, u₀, hi₀, hw₀, hl₀, hp₀, hiLen₀,
    hfield₀, hF₀, hm₀, hclosed, hguard⟩ := HasType.proj_inv henv hΓ ht
  obtain rfl := henv.ordered.projections_unique hi₀ hi
  obtain ⟨_, hfamily₀⟩ := hm₀.hasType.2.isType henv hΓ
  obtain ⟨hls, hargs⟩ := (hm₀.hasType.2.uniqU henv hΓ hm).rigidApp_inv
    henv hΓ (henv.projectionRigid hi₀) hfamily₀
  have hlevels : ls.length = info₀.uvars := hls.length_eq.symm.trans hl₀
  have hparams : (args.take info₀.nparams).length = info₀.nparams := by
    have hlen := hargs.length_eq
    simp only [List.length_append] at hlen
    simp only [List.length_take]
    omega
  obtain ⟨decl, type, ctor, _, _, _, _, _, hnparams, _, _, _, hctorType, _, _, _, Hraw, _⟩ :=
    henv.ordered.projectionShape hi₀
  obtain ⟨doms, result, hshape, hle, _, _, harity⟩ := Hraw.forallArity
  have hcount : info₀.numFields = doms.length - info₀.nparams := by
    rw [VProjectionInfo.numFields, ← hctorType, harity]
  have hshape' : info₀.ctorType = wrapForalls doms result := hctorType.symm.trans hshape
  exact ⟨_, info₀.fieldType_eq_instOuter hshape' hlevels hparams (by omega)⟩

/-- Recovering the major's family therefore suffices to recover and type a
projection's selected field; the source typing supplies the elimination guard. -/
theorem projection_at_recovered_family_exists (henv : env.WF)
    (hΓ : OnCtx Γ (env.IsType U)) (hi : env.projections s info)
    (ht : VExpr.WF env U Γ (.proj s i m))
    (hm : env.HasType U Γ m (mkApps (.const s ls) args)) :
    ∃ F, info.fieldType s ls (args.take info.nparams) i m = some F ∧
      env.HasType U Γ (.proj s i m) F := by
  obtain ⟨F, hF⟩ := projection_recovered_field_exists henv hΓ hi ht hm
  exact ⟨F, hF, projection_at_recovered_family henv hΓ hi ht hm hF⟩

end Lean4Lean.VEnv.Strengthening
