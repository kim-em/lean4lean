import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypedComputationBinders
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureContextualTelescopeAnnotations

/-! # Telescope congruence for typed computation chains

Body chains lift through actual typed binders. Lambda annotations align using
the explicit generic-eta beta fork, so changing them requires ordinary domain
equality only. The construction closes arbitrary finite dependent lambda prefixes. No
fork-joining premise is used for the resulting computation chains.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params] {D : PureObservation.Definitions}

/-- The concrete telescope reannotation fork gives a typed computation chain,
without any fork-joining premise. The body stays unchanged throughout the
reannotation, and its typing under the assigned domains is derived. -/
theorem TypedComputationEq.telescope_annotations
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ (VExpr.wrapLams written b) (VExpr.wrapForalls ds T))
    (hlen : written.length = ds.length) :
    TypedComputationEq D Γ (VExpr.wrapLams written b) (VExpr.wrapLams ds b)
      (VExpr.wrapForalls ds T) := by
  obtain ⟨_, RL, RR⟩ := static_structure_telescope_annotations_fork heq hs hΓ hf hlen
  have hv : env.HasType univs (VExpr.wrapForalls ds T :: Γ) (.bvar 0)
      (VExpr.wrapForalls ds T).lift := .bvar .zero
  have Hβ : env.IsDefEq univs Γ
      (.app (.lam (VExpr.wrapForalls ds T) (.bvar 0)) (VExpr.wrapLams written b))
      (VExpr.wrapLams written b) (VExpr.wrapForalls ds T) := by
    simpa only [VExpr.inst, VExpr.instVar_zero, VExpr.inst_lift] using IsDefEq.beta hv hf
  exact (TypedComputationEq.step Hβ RL).symm.trans
    (.step (Hβ.trans (telescope_annotations_defeq hΓ hf hlen)) RR)

/-- Full lambda congruence for body chains permits arbitrary ordinary equality
of the written domain annotations. Domain computation is unnecessary: generic
eta aligns the annotations at the source Pi assignment. Different residual
bodies are handled by their typed chains, not by an assumed contextual closure. -/
theorem TypedComputationEq.lam_ordinary_domain
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (HA : env.IsDefEq univs Γ A A' (.sort u))
    (HB : TypedComputationEq D (A :: Γ) b b' T) :
    TypedComputationEq D Γ (.lam A b) (.lam A' b') (.forallE A T) := by
  have HL := IsDefEq.lamDF HA HB.defeq.hasType.2
  have HR : TypedComputationEq D Γ (.lam A' b') (.lam A b') (.forallE A T) :=
    TypedComputationEq.telescope_annotations (ds := [A]) (written := [A']) heq hs hΓ HL.hasType.2 rfl
  exact (HB.lam_body hΓ HA.hasType.1).trans HR.symm

/-- An arbitrary typed body chain closes beneath any finite dependent lambda
prefix. This is a congruence theorem for the chain relation, including arbitrary
retained data bodies, rather than an assumed closure of contextual observations. -/
theorem TypedComputationEq.wrapLams
    (hΓ : OnCtx Γ (env.IsType univs))
    (hctx : OnCtx (ds.reverse ++ Γ) (env.IsType univs))
    (H : TypedComputationEq D (ds.reverse ++ Γ) b b' T) :
    TypedComputationEq D Γ (VExpr.wrapLams ds b) (VExpr.wrapLams ds b') (VExpr.wrapForalls ds T) := by
  induction ds generalizing Γ with
  | nil => exact H
  | cons A ds ih =>
    have hctx' : OnCtx (ds.reverse ++ A :: Γ) (env.IsType univs) := by
      simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using hctx
    have hΓA : OnCtx (A :: Γ) (env.IsType univs) := by
      have dropPrefix {xs ys : List VExpr} (h : OnCtx (xs ++ ys) (env.IsType univs)) :
          OnCtx ys (env.IsType univs) := by
        induction xs with
        | nil => exact h
        | cons _ _ ih => exact ih h.1
      exact dropPrefix hctx'
    obtain ⟨u, hA⟩ := hΓA.2
    have H' : TypedComputationEq D (ds.reverse ++ A :: Γ) b b' T := by
      simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using H
    exact (ih hΓA hctx' H').lam_body hΓ hA

/-- Two arbitrary data bodies related by a typed computation chain can be
closed under differently annotated lambda telescopes at a common Pi assignment.
Whole-term typings suffice for both reannotations and for well-formedness of
the assigned binder context. No domain chain, native certificate or joining
premise is required. -/
theorem TypedComputationEq.annotated_telescopes
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hl : env.HasType univs Γ (VExpr.wrapLams left b) (VExpr.wrapForalls ds T))
    (hr : env.HasType univs Γ (VExpr.wrapLams right c) (VExpr.wrapForalls ds T))
    (hlenL : left.length = ds.length) (hlenR : right.length = ds.length)
    (HB : TypedComputationEq D (ds.reverse ++ Γ) b c T) :
    TypedComputationEq D Γ (VExpr.wrapLams left b) (VExpr.wrapLams right c) (VExpr.wrapForalls ds T) := by
  have hctx := (hl.etaOpen_wf henv.ordered hΓ).1
  exact (TypedComputationEq.telescope_annotations heq hs hΓ hl hlenL).trans
    ((HB.wrapLams hΓ hctx).trans (TypedComputationEq.telescope_annotations heq hs hΓ hr hlenR).symm)

/-- Type-fork joining turns telescope congruence for arbitrary typed body
chains into joining in every typed type observer. Body chains need not have a
common reduct and their bodies need not be types or proofs. Ordinary-equality
completeness of the chain relation and TypeForkJoin itself remain open. -/
theorem TypeForkJoin.contextual_telescopes_of_body_chain
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (HF : TypeForkJoin D)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hl : env.HasType univs Γ (VExpr.wrapLams left b) (VExpr.wrapForalls ds T))
    (hr : env.HasType univs Γ (VExpr.wrapLams right c) (VExpr.wrapForalls ds T))
    (hlenL : left.length = ds.length) (hlenR : right.length = ds.length)
    (HB : TypedComputationEq D (ds.reverse ++ Γ) b c T) :
    TypeContextJoin D Γ (VExpr.wrapForalls ds T)
      (VExpr.wrapLams left b) (VExpr.wrapLams right c) :=
  (HB.annotated_telescopes heq hs hΓ hl hr hlenL hlenR).contextual heq hs HF hΓ

end Lean4Lean.VEnv.Strengthening
