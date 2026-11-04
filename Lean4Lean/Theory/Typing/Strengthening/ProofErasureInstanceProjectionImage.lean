import Lean4Lean.Theory.Typing.Strengthening.ProofErasureInstanceProjectionType

/-! # Typed images with instantiated projection trees

Positive unindexed records reconstruct their projections at the original
parameter instance. This supplies the native field typing needed to interpret
the occurrence-specific tree, even when a competing typing uses different
convertible parameters or a different source major.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params]

/-- Reconstruct an actual projection at its native field type from a positive
unindexed major. All earlier projections are typed by structure reconstruction;
no expanded-constructor typing is assumed. -/
theorem StructureReplay.positive_projection_native
    (hΓ : OnCtx Γ (env.IsType univs)) (hi : env.projections c info)
    (hp : ps.length = info.nparams) (hx : info.nindices = 0)
    (hm : env.HasType univs Γ m (mkApps (.const c ls) ps))
    (hpos : (info.resultLevel.inst ls).IsNeverZero)
    (hj : i < info.numFields)
    (hfield : info.fieldType c ls ps i m = some F) :
    env.HasType univs Γ (.proj c i m) F := by
  have hexp := structure_constructor henv hΓ hi hp hx hm (.inl (fun _ _ _ _ _ _ => .inl hpos))
  obtain ⟨decl, family, ctor, _, _, _, _, _, hnparams, _, _, _, hctorType,
    _, _, _, hraw, _⟩ := henv.ordered.projectionShape hi
  obtain ⟨doms, result, hshape, hle, _, _, harity⟩ := hraw.forallArity
  have hlen : doms.length = info.nparams + info.numFields := by
    change doms.length = info.nparams + (info.ctorType.forallArity - info.nparams)
    rw [← hctorType, ← harity]
    omega
  have hs : info.ctorType = wrapForalls doms result := hctorType.symm.trans hshape
  obtain ⟨ci, hci, hw, hl⟩ := (VExpr.WF.of_mkApps henv hΓ ⟨_, hexp⟩).const_inv henv hΓ
  rw [henv.ordered.projectionConstructor hi] at hci
  cases Option.some.inj hci
  have hctor := HasType.const (Γ := Γ) (henv.ordered.projectionConstructor hi) hw hl
  rw [hs, instL_wrapForalls] at hctor
  have hargslen : (ps ++ (List.range info.numFields).map (fun j => VExpr.proj c j m)).length = doms.length := by
    simp [hp, hlen]
  obtain ⟨hargs, _⟩ := HasType.mkApps_wrapForalls henv hΓ hctor ⟨_, hexp⟩ (by simpa using hargslen)
  have harg := hargs (info.nparams + i) (by omega) (by simp; omega)
  simp only [List.getElem_map] at harg
  rw [projection_args_take hp (Nat.le_of_lt hj)] at harg
  have HF := info.fieldType_eq_instOuter (typeName := c) (major := m) hs hl hp
    (by omega : info.nparams + i < doms.length)
  rw [hfield] at HF
  rw [Option.some.inj HF]
  simpa only [List.getElem_append_right (by omega : ps.length ≤ info.nparams + i), hp,
    Nat.add_sub_cancel_left, List.getElem_map, List.getElem_range] using harg

/-- Actual typing at an instantiated finite tree, or any earlier projection-
closed image, supplies this larger image class. -/
inductive InstanceProjectionImage (Γ : List VExpr) (e : VExpr) : Prop
  | closed : ProjectionClosedImage Γ e → InstanceProjectionImage Γ e
  | typed : env.HasType univs Γ e A → InstanceProjectionType env A → InstanceProjectionImage Γ e

/-- Actual typed substitution retains the instantiated tree. -/
theorem InstanceProjectionImage.subst (H : InstanceProjectionImage Γ e)
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ) :
    InstanceProjectionImage Γ₀ (e.subst σ) := by
  cases H with
  | closed H => exact .closed (H.subst hΓ₀ W)
  | typed h HA => exact .typed (h.subst henv.orderedStrong W hΓ₀) HA.subst

/-- Backward equality replay changes the image without changing its certified
parameter instance. -/
theorem InstanceProjectionImage.back (H : InstanceProjectionImage Γ e')
    (hΓ : OnCtx Γ (env.IsType univs)) (HE : env.IsDefEq univs Γ e e' T) :
    InstanceProjectionImage Γ e := by
  cases H with
  | closed H => exact .closed (H.back hΓ HE)
  | typed h HA => exact .typed (HE.toU.of_r henv hΓ h).hasType.1 HA

/-- The image class still excludes function positions. -/
theorem InstanceProjectionImage.not_function (H : InstanceProjectionImage Γ e)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ e (.forallE A B)) : False := by
  cases H with
  | closed H => exact H.not_function hΓ hf
  | typed h HA =>
    cases HA with
    | closed HA => exact (ProjectionClosedImage.typed h HA).not_function hΓ hf
    | record hi _ _ _ _ _ _ =>
      obtain ⟨_, hPi⟩ := hf.isType henv hΓ
      exact henv.headInversion.forallE_rigid hΓ (henv.projectionRigid hi)
        ((hf.uniqU henv hΓ h).typeChain henv hΓ hPi)

/-- A retained projection returns another instantiated-tree image. The original
positive structure typing reconstructs its own field carrier; owner injectivity
aligns the competing projection without demanding identical parameters. -/
theorem InstanceProjectionImage.projection (H : InstanceProjectionImage Γ e)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ (.proj s i e) T)
    (hn : ¬ IsProof Γ (.proj s i e)) : InstanceProjectionImage Γ (.proj s i e) := by
  cases H with
  | closed H => exact .closed (H.projection hΓ ht hn)
  | typed h HA =>
    cases HA with
    | closed HA => exact .closed ((ProjectionClosedImage.typed h HA).projection hΓ ht hn)
    | @record c info ls ps fields hi₀ hc hp hx hpos HF HT =>
      obtain ⟨_, _, _, _, _, _, _, hi, _, _, _, _, _, _, hm, _, _⟩ := ht.proj_inv henv hΓ
      obtain ⟨_, hC⟩ := h.isType henv hΓ
      obtain ⟨E, _, _⟩ := henv.headInversion.rigid_rigid hΓ
        (henv.projectionRigid hi₀) (henv.projectionRigid hi)
        ((h.uniqU henv hΓ hm.hasType.2).typeChain henv hΓ hC)
      subst E
      have hj := ht.proj_index_lt henv hΓ hi₀
      have hF := info.fieldType_subst_some hc (HF i hj) (substitution := VExpr.Subst.one e)
      have hfield : info.fieldType c ls ps i e = some ((fields i).inst e) := by
        simpa [List.map_map, Function.comp_def, ← VExpr.inst_eq, VExpr.inst_lift, VExpr.inst, instVar] using hF
      have hproj := StructureReplay.positive_projection_native hΓ hi₀ hp hx h hpos hj hfield
      exact .typed hproj (by simpa only [← VExpr.inst_eq] using (HT i hj).subst (σ := VExpr.Subst.one e))

end Lean4Lean.VEnv.Strengthening
