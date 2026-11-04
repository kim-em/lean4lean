import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTerminalImage

/-! # Retained projections with terminal field results

A constructor telescope whose field types have terminal heads supplies actual
terminal typings for every valid projection. Parameters and earlier fields may
occur in the arguments of rigid field types. This uses the projection's own
typing derivation, including its admissibility guard, and requires neither
constructor reconstruction nor forward transport of a dependent field carrier.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params

section FieldShape
variable {env : VEnv}

/-- A syntactic field type whose inhabitants are terminal images. Rigid-head
arguments may depend on parameters and earlier fields. -/
inductive TerminalFieldShape (env : VEnv) : VExpr → Prop
  | sort : TerminalFieldShape env (.sort u)
  | data : env.Rigid c → (∀ info, ¬ env.projections c info) →
      TerminalFieldShape env (mkApps (.const c ls) args)
  | fieldless : env.projections c info → info.numFields = 0 →
      TerminalFieldShape env (mkApps (.const c ls) args)

/-- Arbitrary term substitution preserves the certified field head. -/
theorem TerminalFieldShape.subst (H : TerminalFieldShape env A) :
    TerminalFieldShape env (A.subst σ) := by
  cases H with
  | sort => exact .sort
  | data hr hn =>
    simp only [VExpr.subst_mkApps, VExpr.subst]
    exact .data hr hn
  | fieldless hi hz =>
    simp only [VExpr.subst_mkApps, VExpr.subst]
    exact .fieldless hi hz

/-- The certificate also survives every universe specialization. -/
theorem TerminalFieldShape.instL (H : TerminalFieldShape env A) :
    TerminalFieldShape env (A.instL levels) := by
  cases H with
  | sort => exact .sort
  | data hr hn =>
    simp only [VExpr.instL_mkApps, VExpr.instL]
    exact .data hr hn
  | fieldless hi hz =>
    simp only [VExpr.instL_mkApps, VExpr.instL]
    exact .fieldless hi hz

/-- A closed constructor-telescope condition, independent of an occurrence's
parameters, major, indices and universe instance. -/
def StructureReplay.TerminalFields (env : VEnv) (info : VProjectionInfo) : Prop :=
  ∀ doms result, info.ctorType = wrapForalls doms result →
    doms.length = info.nparams + info.numFields →
    ∀ j (hj : j < doms.length), info.nparams ≤ j → TerminalFieldShape env doms[j]

/-- One displayed constructor telescope supplies the complete certificate. -/
theorem StructureReplay.TerminalFields.of_telescope
    (hshape : info.ctorType = wrapForalls doms result)
    (hlen : doms.length = info.nparams + info.numFields)
    (hfields : ∀ j (hj : j < doms.length), info.nparams ≤ j → TerminalFieldShape env doms[j]) :
    TerminalFields env info := by
  intro doms' result' hshape' hlen'
  have he := congrArg (VExpr.takeForalls doms.length) (hshape.symm.trans hshape')
  rw [takeForalls_wrapForalls, show doms.length = doms'.length by omega,
    takeForalls_wrapForalls] at he
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj he)
  exact hfields

end FieldShape

variable [Params]

/-- Actual typing at a certified field type yields a terminal image. -/
theorem TerminalFieldShape.image (H : TerminalFieldShape env A)
    (ht : env.HasType univs Γ e A) : TerminalImage Γ e := by
  cases H with
  | sort => exact .type ht
  | data hr hn => exact .data ht hr hn
  | fieldless hi hz => exact .fieldless ht hi hz

/-- A typed projection of a registered terminal-field structure is terminal.
The native field type is recovered from the projection derivation, so its
parameters and universe instance need not agree syntactically with a separate
major typing, and no structure expansion is assumed. -/
theorem StructureReplay.TerminalFields.projection (H : TerminalFields env info)
    (hΓ : OnCtx Γ (env.IsType univs)) (hi : env.projections family info)
    (ht : env.HasType univs Γ (.proj family i m) T) :
    TerminalImage Γ (.proj family i m) := by
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
  have Hinst : TerminalFieldShape env ((doms[info.nparams + i].instL levels).instOuter
      (params ++ (List.range i).map (fun j => .proj family j source))) := by
    rw [VExpr.instOuter_eq_subst]
    exact Hshape.subst
  have EF := info.fieldType_eq_instOuter (typeName := family) (major := source) hs hl hp (by omega : info.nparams + i < doms.length)
  rw [hfield] at EF
  have hproj : env.HasType univs Γ (.proj family i m) F :=
    .projDF hi hw hl hp hx hfield hF hm hm hclosed hguard
  rw [Option.some.inj EF] at hproj
  exact Hinst.image hproj

/-- A non-function image whose retained projections have terminal results.
Unlike TerminalImage, the structure branch permits retained data fields. -/
inductive ProjectionTerminalImage (Γ : List VExpr) (e : VExpr) : Prop
  | terminal : TerminalImage Γ e → ProjectionTerminalImage Γ e
  | fields : env.HasType univs Γ e (mkApps (.const c ls) args) →
      env.projections c info → StructureReplay.TerminalFields env info →
      ProjectionTerminalImage Γ e

/-- Typed substitution retains the concrete major typing and static field
certificate, with no assumption about native recovery after substitution. -/
theorem ProjectionTerminalImage.subst (H : ProjectionTerminalImage Γ e)
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ) :
    ProjectionTerminalImage Γ₀ (e.subst σ) := by
  cases H with
  | terminal H => exact .terminal (H.subst hΓ₀ W)
  | fields h hi HF =>
    have hh := h.subst henv.orderedStrong W hΓ₀
    simp only [VExpr.subst_mkApps, VExpr.subst_const] at hh
    exact .fields hh hi HF

/-- Backward replay of actual equality retains the classification. -/
theorem ProjectionTerminalImage.back (H : ProjectionTerminalImage Γ e')
    (hΓ : OnCtx Γ (env.IsType univs)) (HE : env.IsDefEq univs Γ e e' T) :
    ProjectionTerminalImage Γ e := by
  cases H with
  | terminal H => exact .terminal (H.back hΓ HE)
  | fields h hi HF => exact .fields (HE.toU.of_r henv hΓ h).hasType.1 hi HF

/-- Neither alternative can supply a function at a retained application. -/
theorem ProjectionTerminalImage.not_function (H : ProjectionTerminalImage Γ e)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ e (.forallE A B)) : False := by
  cases H with
  | terminal H => exact H.not_function hΓ hf
  | fields h hi _ =>
    obtain ⟨_, hPi⟩ := hf.isType henv hΓ
    exact henv.headInversion.forallE_rigid hΓ (henv.projectionRigid hi)
      ((hf.uniqU henv hΓ h).typeChain henv hΓ hPi)

/-- A retained typed projection has a terminal result. Owner injectivity
aligns the actual projection with the certified constructor telescope. -/
theorem ProjectionTerminalImage.projection (H : ProjectionTerminalImage Γ e)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ (.proj s i e) T)
    (hn : ¬ IsProof Γ (.proj s i e)) : TerminalImage Γ (.proj s i e) := by
  cases H with
  | terminal H => exact (H.not_projection hΓ ht hn).elim
  | fields h hi₀ HF =>
    obtain ⟨_, _, _, _, _, _, _, hi, _, _, _, _, _, _, hm, _, _⟩ := ht.proj_inv henv hΓ
    obtain ⟨_, hC⟩ := h.isType henv hΓ
    obtain ⟨E, _, _⟩ := henv.headInversion.rigid_rigid hΓ
      (henv.projectionRigid hi₀) (henv.projectionRigid hi)
      ((h.uniqU henv hΓ hm.hasType.2).typeChain henv hΓ hC)
    subst E
    exact HF.projection hΓ hi₀ ht

end Lean4Lean.VEnv.Strengthening
