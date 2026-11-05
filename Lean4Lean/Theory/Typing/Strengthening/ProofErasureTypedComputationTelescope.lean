import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypedComputationSingletonEquation

/-! # Dependent telescope instances along typed computation chains

Whole-application typing determines each argument assignment. Applying related
spines to a typed lambda telescope and contracting beta compares its instances
without native argument recovery or type-fork joining.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params] {D : PureObservation.Definitions}

/-- Function and argument traces act on an entire dependent application spine. -/
theorem TypedComputationTrace.mkApps_congr
    (HF : TypedComputationTrace D Γ f g)
    (HX : List.Forall₂ (TypedComputationTrace D Γ) args args') :
    TypedComputationTrace D Γ (VExpr.mkApps f args) (VExpr.mkApps g args') := by
  induction HX generalizing f g with
  | nil => exact HF
  | cons H HT ih => exact ih (TypedComputationTrace.app HF H)

/-- Every argument of a typed telescope instance supplies a reflexive chain at
its own dependent assignment. -/
theorem TypedComputationEq.telInst_refl (ha : TelInst env univs Γ ds args) :
    List.Forall₂ (fun a b => ∃ A, TypedComputationEq D Γ a b A) args args := by
  apply List.forall₂_of_getElem rfl
  intro j hj _
  exact ⟨_, .refl (ha.2 j hj (by simpa only [← ha.1] using hj))⟩

/-- Instantiating a typed lambda telescope at pointwise chain-related arguments
produces a chain at the original result assignment. Only the source argument
instance is needed; application replay supplies the target instance typing. -/
theorem TypedComputationEq.instOuter_from_wrapper
    (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ (VExpr.wrapLams ds e) (wrapForalls ds T))
    (ha : TelInst env univs Γ ds args)
    (HX : List.Forall₂ (fun a b => ∃ A, TypedComputationEq D Γ a b A) args args') :
    TypedComputationEq D Γ (e.instOuter args) (e.instOuter args') (T.instOuter args) := by
  have Hargs : List.Forall₂ (TypedComputationTrace D Γ) args args' :=
    HX.imp (fun _ _ ⟨_, H⟩ => TypedComputationTrace.of_chain H)
  have HR := TypedComputationTrace.mkApps_congr (TypedComputationTrace.refl (D := D) (a := VExpr.wrapLams ds e)) Hargs
    hΓ (HasType.mkApps_of_tel ht ha)
  have hl : ds.length = args.length := ha.1.symm
  have hl' : ds.length = args'.length := hl.trans HX.length_eq
  have HB := BetaRed.mkApps_wrapLams ds e args (Nat.le_of_eq hl)
  have HB' := BetaRed.mkApps_wrapLams ds e args' (Nat.le_of_eq hl')
  rw [hl, List.take_length, List.drop_length] at HB
  rw [hl', List.take_length, List.drop_length] at HB'
  exact (TypedComputationEq.of_beta hΓ HR.defeq.hasType.1 HB).symm.trans
    (HR.trans (TypedComputationEq.of_beta hΓ HR.defeq.hasType.2 HB'))

/-- A typed body under an open telescope respects simultaneous argument
chains. The telescope and body may depend on the surrounding context. -/
theorem TypedComputationEq.instOuter_congr
    (hΓ : OnCtx Γ (env.IsType univs))
    (hctx : OnCtx (ds.reverse ++ Γ) (env.IsType univs))
    (ht : env.HasType univs (ds.reverse ++ Γ) e T)
    (ha : TelInst env univs Γ ds args)
    (HX : List.Forall₂ (fun a b => ∃ A, TypedComputationEq D Γ a b A) args args') :
    TypedComputationEq D Γ (e.instOuter args) (e.instOuter args') (T.instOuter args) :=
  TypedComputationEq.instOuter_from_wrapper hΓ (HasType.wrapLams_of hctx ht) ha HX

/-- A declaration telescope's typed body respects arbitrary pointwise chains
in an external context, including data arguments and dependent result types. -/
theorem TypedComputationEq.closed_instOuter_congr
    (hΓ : OnCtx Γ (env.IsType univs))
    (hctx : OnCtx ds.reverse (env.IsType univs))
    (ht : env.HasType univs ds.reverse e T)
    (ha : TelInst env univs Γ ds args)
    (HX : List.Forall₂ (fun a b => ∃ A, TypedComputationEq D Γ a b A) args args') :
    TypedComputationEq D Γ (e.instOuter args) (e.instOuter args') (T.instOuter args) := by
  have hf : env.HasType univs [] (VExpr.wrapLams ds e) (wrapForalls ds T) :=
    HasType.wrapLams_of (by simpa only [List.append_nil] using hctx)
      (by simpa only [List.append_nil] using ht)
  exact TypedComputationEq.instOuter_from_wrapper hΓ (hf.weak0 henv.ordered) ha HX

end Lean4Lean.VEnv.Strengthening
