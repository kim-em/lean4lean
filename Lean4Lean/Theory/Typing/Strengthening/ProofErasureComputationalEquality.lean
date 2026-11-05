import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypedComputationTelescope
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureComputationalTyping
import Lean4Lean.Theory.Typing.Confluence.JoinLemmas

/-! # Computational equality without a fixed assignment

Existentially hiding the common assignment lets dependent argument chains
compose. Every operation still replays a checked chain at an actual typing.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params] {D : PureObservation.Definitions}

/-- A computation chain at some common assignment. -/
def TypedComputationEqU (D : PureObservation.Definitions) (Γ : List VExpr) (a b : VExpr) : Prop :=
  ∃ A, TypedComputationEq D Γ a b A

theorem TypedComputationEqU.defeq (H : TypedComputationEqU D Γ a b) :
    env.IsDefEqU univs Γ a b := ⟨_, H.choose_spec.defeq⟩

theorem TypedComputationEqU.hasType (H : TypedComputationEqU D Γ a b) :
    (∃ A, env.HasType univs Γ a A) ∧ (∃ A, env.HasType univs Γ b A) :=
  ⟨⟨_, H.choose_spec.defeq.hasType.1⟩, ⟨_, H.choose_spec.defeq.hasType.2⟩⟩

theorem TypedComputationEqU.refl (ht : env.HasType univs Γ a A) :
    TypedComputationEqU D Γ a a := ⟨_, .refl ht⟩

theorem TypedComputationEqU.symm (H : TypedComputationEqU D Γ a b) :
    TypedComputationEqU D Γ b a := ⟨_, H.choose_spec.symm⟩

theorem TypedComputationEqU.trans (hΓ : OnCtx Γ (env.IsType univs))
    (H : TypedComputationEqU D Γ a b) (H' : TypedComputationEqU D Γ b c) :
    TypedComputationEqU D Γ a c :=
  ⟨_, H.choose_spec.trans (H'.choose_spec.at_source_type hΓ H.choose_spec.defeq.hasType.2)⟩

theorem TypedComputationEqU.at_source_type (hΓ : OnCtx Γ (env.IsType univs))
    (H : TypedComputationEqU D Γ a b) (ht : env.HasType univs Γ a A) :
    TypedComputationEq D Γ a b A := H.choose_spec.at_source_type hΓ ht

/-- An existing chain can be retagged at the source's actual universe. -/
theorem TypedComputationEqU.at_type (hΓ : OnCtx Γ (env.IsType univs))
    (H : TypedComputationEqU D Γ A B) (ht : env.IsType univs Γ A) :
    TypedComputationTypeEq D Γ A B := ⟨_, H.at_source_type hΓ ht.choose_spec⟩

theorem TypedComputationTypeEq.toEqU (H : TypedComputationTypeEq D Γ A B) :
    TypedComputationEqU D Γ A B := ⟨_, H.choose_spec⟩

theorem TypedComputationEqU.normalEq
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (H : NormalEqF mode Γ a b) :
    TypedComputationEqU D Γ a b := normal_computation_chain_exists heq hs hΓ H.choose_spec

theorem TypedComputationEqU.of_eqUpToLevels
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (H : EqUpToLevels univs a b)
    (ht : env.HasType univs Γ a A) : TypedComputationEqU D Γ a b :=
  .normalEq heq hs hΓ (NormalEq.of_eqUpToLevels H hΓ ht)

theorem TypedComputationEqU.of_beta (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ a A) (H : VExpr.BetaRed a b) :
    TypedComputationEqU D Γ a b := ⟨_, .of_beta hΓ ht H⟩

theorem TypedComputationEqU.app (hΓ : OnCtx Γ (env.IsType univs))
    (H : TypedComputationEqU D Γ f f') (HX : TypedComputationEqU D Γ x x')
    (ht : env.HasType univs Γ (.app f x) A) : TypedComputationEqU D Γ (.app f x) (.app f' x') :=
  ⟨_, TypedComputationTrace.app (TypedComputationTrace.of_chain H.choose_spec) (TypedComputationTrace.of_chain HX.choose_spec) hΓ ht⟩

theorem TypedComputationEqU.mkApps (hΓ : OnCtx Γ (env.IsType univs))
    (H : TypedComputationEqU D Γ f f') (HX : List.Forall₂ (TypedComputationEqU D Γ) args args')
    (ht : env.HasType univs Γ (VExpr.mkApps f args) A) :
    TypedComputationEqU D Γ (VExpr.mkApps f args) (VExpr.mkApps f' args') := by
  have Hargs : List.Forall₂ (TypedComputationTrace D Γ) args args' :=
    HX.imp fun _ _ ⟨_, H⟩ => TypedComputationTrace.of_chain H
  exact ⟨_, TypedComputationTrace.mkApps_congr (TypedComputationTrace.of_chain H.choose_spec) Hargs hΓ ht⟩

theorem TypedComputationEqU.forall₂_refl :
    ∀ {args : List VExpr}, (∀ a ∈ args, ∃ A, env.HasType univs Γ a A) →
      List.Forall₂ (TypedComputationEqU D Γ) args args
  | [], _ => .nil
  | _ :: _, H => .cons (.refl (H _ (List.mem_cons_self ..)).choose_spec)
      (forall₂_refl fun b hb => H b (List.mem_cons_of_mem _ hb))

theorem TypedComputationEqU.forall₂_trans (hΓ : OnCtx Γ (env.IsType univs))
    (H : List.Forall₂ (TypedComputationEqU D Γ) a b)
    (H' : List.Forall₂ (TypedComputationEqU D Γ) b c) :
    List.Forall₂ (TypedComputationEqU D Γ) a c :=
  List.Forall₂.trans (fun _ _ _ H H' => H.trans hΓ H') H H'

end Lean4Lean.VEnv.Strengthening
