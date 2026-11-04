import Lean4Lean.Theory.Typing.Strengthening.ProofErasureProjectionTerminalImage

/-! # Finite certificates closed under retained projections

Record fields may themselves have record types. The inductive certificate
follows their declared rigid heads to terminal field shapes. Substitution and
universe specialization change the arguments but preserve this finite tree.
No normalization of values or bound on their computation is assumed.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params

section FieldShape
variable {env : VEnv}

/-- A finite tree of terminal types and registered record field types. The
recursive premise inspects declaration syntax, independently of any occurrence
or future comparison. Parameter-dependent rigid-head arguments are allowed. -/
inductive ProjectionClosedType (env : VEnv) : VExpr → Prop
  | terminal : TerminalFieldShape env A → ProjectionClosedType env A
  | record : env.projections c info →
      (∀ doms result, info.ctorType = wrapForalls doms result →
        doms.length = info.nparams + info.numFields →
        ∀ j (hj : j < doms.length), info.nparams ≤ j → ProjectionClosedType env doms[j]) →
      ProjectionClosedType env (mkApps (.const c ls) args)

/-- Arbitrary substitution retains the finite certificate tree. The declared
field domains do not change when an occurrence's arguments are substituted. -/
theorem ProjectionClosedType.subst (H : ProjectionClosedType env A) :
    ProjectionClosedType env (A.subst σ) := by
  cases H with
  | terminal H => exact .terminal H.subst
  | record hi HF =>
    simp only [VExpr.subst_mkApps, VExpr.subst]
    exact .record hi HF

/-- Universe specialization also preserves the declared field tree. -/
theorem ProjectionClosedType.instL (H : ProjectionClosedType env A) :
    ProjectionClosedType env (A.instL levels) := by
  cases H with
  | terminal H => exact .terminal H.instL
  | record hi HF =>
    simp only [VExpr.instL_mkApps, VExpr.instL]
    exact .record hi HF

/-- Every field of a registered constructor has a finite projection-closed
certificate; this abbreviation exposes the inductive record premise. -/
def StructureReplay.ProjectionClosedFields (env : VEnv) (info : VProjectionInfo) : Prop :=
  ∀ doms result, info.ctorType = wrapForalls doms result →
    doms.length = info.nparams + info.numFields →
    ∀ j (hj : j < doms.length), info.nparams ≤ j → ProjectionClosedType env doms[j]

/-- A displayed constructor telescope suffices to establish the record premise. -/
theorem StructureReplay.ProjectionClosedFields.of_telescope
    (hshape : info.ctorType = wrapForalls doms result)
    (hlen : doms.length = info.nparams + info.numFields)
    (hfields : ∀ j (hj : j < doms.length), info.nparams ≤ j → ProjectionClosedType env doms[j]) :
    ProjectionClosedFields env info := by
  intro doms' result' hshape' hlen'
  have he := congrArg (VExpr.takeForalls doms.length) (hshape.symm.trans hshape')
  rw [takeForalls_wrapForalls, show doms.length = doms'.length by omega,
    takeForalls_wrapForalls] at he
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj he)
  exact hfields

/-- Earlier terminal-field certificates embed as finite leaves. -/
theorem StructureReplay.TerminalFields.projectionClosed
    (H : TerminalFields env info) : ProjectionClosedFields env info :=
  fun doms result hs hl j hj hp => .terminal (H doms result hs hl j hj hp)

end FieldShape
variable [Params]

/-- An actual typed image with finite projection coverage. Terminal images
retain their earlier proof-only cases; typed tree nodes permit nested records. -/
inductive ProjectionClosedImage (Γ : List VExpr) (e : VExpr) : Prop
  | terminal : TerminalImage Γ e → ProjectionClosedImage Γ e
  | typed : env.HasType univs Γ e A → ProjectionClosedType env A → ProjectionClosedImage Γ e

/-- Terminal-field images embed without any native recovery requirement. -/
theorem ProjectionTerminalImage.closed (H : ProjectionTerminalImage Γ e) :
    ProjectionClosedImage Γ e := by
  cases H with
  | terminal H => exact .terminal H
  | fields h hi HF => exact .typed h (.record hi HF.projectionClosed)

/-- Actual typing at a certified record carries its full field tree. -/
theorem ProjectionClosedImage.of_fields
    (h : env.HasType univs Γ e (mkApps (.const c ls) args))
    (hi : env.projections c info) (HF : StructureReplay.ProjectionClosedFields env info) :
    ProjectionClosedImage Γ e := .typed h (.record hi HF)

/-- Typed substitution changes the actual image but preserves its finite tree. -/
theorem ProjectionClosedImage.subst (H : ProjectionClosedImage Γ e)
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ) :
    ProjectionClosedImage Γ₀ (e.subst σ) := by
  cases H with
  | terminal H => exact .terminal (H.subst hΓ₀ W)
  | typed h HA => exact .typed (h.subst henv.orderedStrong W hΓ₀) HA.subst

/-- Backward replay uses actual equality, without computing a chosen type. -/
theorem ProjectionClosedImage.back (H : ProjectionClosedImage Γ e')
    (hΓ : OnCtx Γ (env.IsType univs)) (HE : env.IsDefEq univs Γ e e' T) :
    ProjectionClosedImage Γ e := by
  cases H with
  | terminal H => exact .terminal (H.back hΓ HE)
  | typed h HA => exact .typed (HE.toU.of_r henv hΓ h).hasType.1 HA

/-- Every certified image is non-functional, including record nodes whose
projections can be used repeatedly. -/
theorem ProjectionClosedImage.not_function (H : ProjectionClosedImage Γ e)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ e (.forallE A B)) : False := by
  cases H with
  | terminal H => exact H.not_function hΓ hf
  | typed h HA =>
    cases HA with
    | terminal HA => exact (HA.image h).not_function hΓ hf
    | record hi _ =>
      obtain ⟨_, hPi⟩ := hf.isType henv hΓ
      exact henv.headInversion.forallE_rigid hΓ (henv.projectionRigid hi)
        ((hf.uniqU henv hΓ h).typeChain henv hΓ hPi)

/-- Actual projection inversion supplies the field type and its finite child
certificate at the native source's universe and parameter instance. -/
theorem StructureReplay.ProjectionClosedFields.projection (H : ProjectionClosedFields env info)
    (hΓ : OnCtx Γ (env.IsType univs)) (hi : env.projections family info)
    (ht : env.HasType univs Γ (.proj family i m) T) :
    ProjectionClosedImage Γ (.proj family i m) := by
  obtain ⟨info', levels, params, indices, source, F, v, hi', hw, hl, hp, hx,
    hfield, hF, hm, hclosed, hguard⟩ := ht.proj_inv henv hΓ
  cases henv.ordered.projections_unique hi' hi
  have hj := ht.proj_index_lt henv hΓ hi
  obtain ⟨decl, family', ctor, _, _, _, _, _, hnparams, _, _, _, hctorType,
    _, _, _, hraw, _⟩ := henv.ordered.projectionShape hi
  obtain ⟨doms, result, hshape, hle, _, _, harity⟩ := hraw.forallArity
  have hlen : doms.length = info.nparams + info.numFields := by
    change doms.length = info.nparams + (info.ctorType.forallArity - info.nparams)
    rw [← hctorType, ← harity]
    omega
  have hs : info.ctorType = wrapForalls doms result := hctorType.symm.trans hshape
  have Hshape := (H doms result hs hlen (info.nparams + i) (by omega) (by omega)).instL
    (levels := levels)
  have Hinst : ProjectionClosedType env ((doms[info.nparams + i].instL levels).instOuter
      (params ++ (List.range i).map (fun j => .proj family j source))) := by
    rw [VExpr.instOuter_eq_subst]
    exact Hshape.subst
  have EF := info.fieldType_eq_instOuter (typeName := family) (major := source) hs hl hp
    (by omega : info.nparams + i < doms.length)
  rw [hfield] at EF
  have hproj : env.HasType univs Γ (.proj family i m) F :=
    .projDF hi hw hl hp hx hfield hF hm hm hclosed hguard
  rw [Option.some.inj EF] at hproj
  exact .typed hproj Hinst

/-- Retained typed projection closes on the same image class. Repeating this
law follows the finite tree rather than requiring each immediate result to
be terminal. It assumes no comparison or computation-transport law. -/
theorem ProjectionClosedImage.projection (H : ProjectionClosedImage Γ e)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ (.proj s i e) T)
    (hn : ¬ IsProof Γ (.proj s i e)) : ProjectionClosedImage Γ (.proj s i e) := by
  cases H with
  | terminal H => exact (H.not_projection hΓ ht hn).elim
  | typed h HA =>
    cases HA with
    | terminal HA => exact ((HA.image h).not_projection hΓ ht hn).elim
    | record hi₀ HF =>
      obtain ⟨_, _, _, _, _, _, _, hi, _, _, _, _, _, _, hm, _, _⟩ := ht.proj_inv henv hΓ
      obtain ⟨_, hC⟩ := h.isType henv hΓ
      obtain ⟨E, _, _⟩ := henv.headInversion.rigid_rigid hΓ
        (henv.projectionRigid hi₀) (henv.projectionRigid hi)
        ((h.uniqU henv hΓ hm.hasType.2).typeChain henv hΓ hC)
      subst E
      exact StructureReplay.ProjectionClosedFields.projection HF hΓ hi₀ ht

end Lean4Lean.VEnv.Strengthening
