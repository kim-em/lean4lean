import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertGuardedBodies

/-! # Both orientations of dependent guarded interfaces

Reversal retains each direction at its own selected carrier, annotation map,
and finite interface tree. Application returns both dependent result instances;
it does not identify the result trees at different arguments. This is retained
bidirectional evidence, not symmetry of every one-sided guarded value.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private tree_cons_comp tree_id_comp tree_inst
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertGuardedTrees
open private value_inst_lift from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertWorldValues
open private erase_forallE_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
variable [Params] {D : Definitions}

/-- Two orientations retain their own dependent interface syntax and carrier.
Each component includes actual assignments, ground history, and recursive
action. The reverse component is not inferred from the forward component. -/
structure PiInertGuardedPair (D : Definitions) (Δ : List ProofShape)
    (p q : PiInertGuardedTree) (ρ τ : ProofShape.Subst) (a b T U : ProofShape) : Prop where
  forward : PiInertGuardedTreeValue p ρ D Δ a b T
  backward : PiInertGuardedTreeValue q τ D Δ b a U

/-- Reversal swaps the already retained dependent interfaces. -/
theorem PiInertGuardedPair.symm (H : PiInertGuardedPair D Δ p q ρ τ a b T U) :
    PiInertGuardedPair D Δ q p τ ρ b a U T := ⟨H.backward, H.forward⟩

/-- Both annotation maps and both selected carriers move through one world. -/
theorem PiInertGuardedPair.move (H : PiInertGuardedPair D Δ p q ρ τ a b T U)
    (W : PiInertCoreWorld D Δ Λ σ) :
    PiInertGuardedPair D Λ p q (ρ.comp σ) (τ.comp σ)
      (a.subst σ) (b.subst σ) (T.subst σ) (U.subst σ) :=
  ⟨H.forward.move W, H.backward.move W⟩

/-- Application keeps the left result at its left argument and the reverse
result at its right argument. Input and output trees can differ between the
two directions; no dependent interface reindexing is assumed. -/
theorem PiInertGuardedPair.app
    (heq : env.HasCanonicalEq) (hc : TypedCoreConfluence (ErasedLevelCore D))
    (H : PiInertGuardedPair D Δ (.call A B p q) (.call C E r s) ρ τ f g T U)
    (HX : PiInertGuardedPair D Δ p r ρ τ x y (A.subst ρ) (C.subst τ))
    (HL : TypedSource Δ (.app f x)) (HR : TypedSource Δ (.app g y)) :
    PiInertGuardedPair D Δ q s (ρ.cons x) (τ.cons y)
      (.app f x) (.app g y) (B.subst (ρ.cons x)) (E.subst (τ.cons y)) :=
  ⟨H.forward.app heq hc HX.forward HL HR, H.backward.app heq hc HX.backward HR HL⟩

/-- Both guarded call interfaces survive explicit selected-type prefixes.
The four new assignments remain explicit and tied to the new carriers. -/
theorem PiInertGuardedPair.call_prefix
    (H : PiInertGuardedPair D Δ (.call A B p q) (.call C E r s) ρ τ a b T U)
    (HA : TypedAt Δ a V) (HB : TypedAt Δ b V)
    (HC : TypedAt Δ b W) (HD : TypedAt Δ a W)
    (RV : PiInertWorldComputation D n Δ V T) (RW : PiInertWorldComputation D m Δ W U) :
    PiInertGuardedPair D Δ (.call A B p q) (.call C E r s) ρ τ a b V W :=
  ⟨H.forward.call_prefix HA HB RV, H.backward.call_prefix HC HD RW⟩

/-- Paired image requirements retain each tree at both substituted native
carriers. This strengthens the old one-sided image environment explicitly. -/
def PiInertGuardedPairImages (D : Definitions) (Δ Λ : List ProofShape)
    (σ τ : ProofShape.Subst) (uses : List (Nat × PiInertGuardedTree)) : Prop :=
  ∀ i p, (i, p) ∈ uses → PiInertGuardedPair D Λ p p σ τ (σ i) (τ i)
    ((contextOracle Δ i).subst σ) ((contextOracle Δ i).subst τ)

/-- The forward environment is a genuine old guarded-image environment. -/
theorem PiInertGuardedPairImages.forward (H : PiInertGuardedPairImages D Δ Λ σ τ uses) :
    PiInertGuardedImages D Δ Λ σ τ uses := fun i p hi => (H i p hi).forward

/-- Reverse images keep the other substituted native carrier. -/
theorem PiInertGuardedPairImages.backward (H : PiInertGuardedPairImages D Δ Λ σ τ uses) :
    PiInertGuardedImages D Δ Λ τ σ uses := fun i p hi => (H i p hi).backward

/-- Reversal preserves the same finite variable requirement list. -/
theorem PiInertGuardedPairImages.symm (H : PiInertGuardedPairImages D Δ Λ σ τ uses) :
    PiInertGuardedPairImages D Δ Λ τ σ uses := fun i p hi => (H i p hi).symm

/-- Both orientations of a term comparison under paired typed environments.
The original endpoints, carriers and result profiles may differ. This is a
semantic induction interface; general strong coverage is not assumed. -/
structure PiInertGuardedPairInterpretation (D : Definitions) (Δ : List ProofShape)
    (uses : List (Nat × PiInertGuardedTree)) (a b T U : ProofShape)
    (p q : PiInertGuardedTree) : Prop where
  left : TypedAt Δ a T
  right : TypedAt Δ b U
  run : ∀ {Λ σ τ}, ContextSubstitution Δ Λ σ → ContextSubstitution Δ Λ τ →
    PiInertGuardedPairImages D Δ Λ σ τ uses →
    PiInertGuardedPair D Λ p q σ τ (a.subst σ) (b.subst τ) (T.subst σ) (U.subst τ)

/-- An existing body interpreter constructs both orientations by two proved
instances of its run theorem. No action for the reverse orientation is added
as a new hypothesis about the term. -/
theorem PiInertGuardedInterpretation.paired
    (H : PiInertGuardedInterpretation D Δ uses e T p) :
    PiInertGuardedPairInterpretation D Δ uses e e T T p p :=
  ⟨H.assigned, H.assigned, fun WL WR images =>
    ⟨H.run WL WR images.forward, H.run WR WL images.backward⟩⟩

/-- Comparison reversal uses the existing interpretation at swapped
environments, rather than recursively interpreting a newly symmetrized strong
derivation or converting one dependent result tree to the other. -/
theorem PiInertGuardedPairInterpretation.symm
    (H : PiInertGuardedPairInterpretation D Δ uses a b T U p q) :
    PiInertGuardedPairInterpretation D Δ uses b a U T q p :=
  ⟨H.right, H.left, fun WL WR images => (H.run WR WL images.symm).symm⟩

/-- Paired application preserves two separately instantiated output trees.
The result profiles record the corresponding original argument on each side. -/
theorem PiInertGuardedPairInterpretation.app
    (heq : env.HasCanonicalEq) (hc : TypedCoreConfluence (ErasedLevelCore D))
    (HF : PiInertGuardedPairInterpretation D Δ fs f g T U (.call A B p q) (.call C E r s))
    (HX : PiInertGuardedPairInterpretation D Δ xs x y A C p r)
    (HL : TypedAt Δ (.app f x) (B.inst x)) (HR : TypedAt Δ (.app g y) (E.inst y)) :
    PiInertGuardedPairInterpretation D Δ (fs ++ xs) (.app f x) (.app g y) (B.inst x) (E.inst y)
      (q.subst (.one x)) (s.subst (.one y)) := by
  refine ⟨HL, HR, ?_⟩
  intro Λ σ τ WL WR images
  have F := HF.run WL WR (fun i p hi => images i p (List.mem_append_left _ hi))
  have X := HX.run WL WR (fun i p hi => images i p (List.mem_append_right _ hi))
  have result := F.app heq hc X (HL.sources.1.subst WL) (HR.sources.1.subst WR)
  constructor
  · simpa only [PiInertGuardedTreeValue.subst_iff, ProofShape.Subst.one,
      tree_cons_comp, tree_id_comp, ProofShape.subst, ProofShape.subst_inst, tree_inst] using result.forward
  · simpa only [PiInertGuardedTreeValue.subst_iff, ProofShape.Subst.one,
      tree_cons_comp, tree_id_comp, ProofShape.subst, ProofShape.subst_inst, tree_inst] using result.backward

/-- Typed eta arguments instantiate to the actual raw argument, including
the proof-marker case for a proposition domain. -/
theorem ProofShape.TypedAt.eta_argument_inst
    (S : DomainSort Δ A u) (HX : TypedAt Δ x A) : (etaArgument u).inst x = x := by
  obtain ⟨Γ, C, hΓ, EΓ, hC, EC⟩ := S
  obtain ⟨x₀, hx, Ex⟩ := (EΓ ▸ HX).realize_carrier hΓ hC EC
  simpa only [Ex] using proofErase_eta_argument_inst hΓ hC hx

/-- Actual eta expansion has an assigned raw lambda when the source function
is not erased. The domain's sort selects a variable or proof-marker argument;
no positivity restriction on the domain is imposed. -/
theorem ProofShape.TypedAt.eta_expansion
    (H : TypedAt Δ f (.forallE A B)) (S : DomainSort Δ A u) (hn : f ≠ .proof) :
    TypedAt Δ (.lam A (.app (f.liftN 1) (etaArgument u))) (.forallE A B) := by
  obtain ⟨Γ, f₀, F, hΓ, rfl, hf, Ef, EF⟩ := H
  obtain ⟨A₀, B₀, rfl, _, EA, EB⟩ := erase_forallE_inv EF
  obtain ⟨_, hPi⟩ := hf.isType henv hΓ
  obtain ⟨⟨_, hA⟩, _⟩ := hPi.forallE_inv henv.ordered
  have hAu := S.realize_type hΓ hA rfl EA
  have hnf : ¬ IsProof Γ f₀ := fun hp => hn (Ef.symm.trans (proofErase_eq_proof.2 hp))
  have HE : env.IsDefEq univs Γ (.lam A₀ (.app f₀.lift (.bvar 0))) f₀ (.forallE A₀ B₀) := .eta hf
  have hne : ¬ IsProof Γ (.lam A₀ (.app f₀.lift (.bvar 0))) :=
    fun hp => hnf ((isProof_congr hΓ HE).1 hp)
  refine ⟨Γ, .lam A₀ (.app f₀.lift (.bvar 0)), .forallE A₀ B₀,
    hΓ, rfl, HE.hasType.1, ?_, EF⟩
  rw [show proofErase Γ (.lam A₀ (.app f₀.lift (.bvar 0))) = .lam _ _ from if_neg hne,
    proofErase_eta_body hΓ hAu hf hnf, EA, Ef]

/-- Application-level core prefixes construct a new full call tree and its
ground history. This permits eta expansion even when the functions themselves
have no ordinary-core reduction to the old endpoints. -/
theorem PiInertGuardedTreeValue.call_application_prefixes
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hRigid : ∀ {c}, env.Rigid c → ∀ levels rhs, ¬ D.unfolds c levels rhs)
    (H : PiInertGuardedTreeValue (.call A B p q) ProofShape.Subst.id D Δ f g (.forallE A B))
    (HF : TypedAt Δ f' (.forallE A B)) (HG : TypedAt Δ g' (.forallE A B))
    (supply : PiInertGuardedTreeSupply p ProofShape.Subst.id D Δ A)
    (left : ∀ {Λ σ x}, PiInertCoreWorld D Δ Λ σ → TypedAt Λ x (A.subst σ) →
      Compute (ErasedLevelCore D) (.app (f'.subst σ) x) (.app (f.subst σ) x))
    (right : ∀ {Λ σ y}, PiInertCoreWorld D Δ Λ σ → TypedAt Λ y (A.subst σ) →
      Compute (ErasedLevelCore D) (.app (g'.subst σ) y) (.app (g.subst σ) y)) :
    PiInertGuardedTreeValue (.call A B p q) ProofShape.Subst.id D Δ f' g' (.forallE A B) := by
  apply PiInertGuardedTreeValue.of_calls heq hs hc hRigid HF HG supply
  intro Λ σ x y W HX HL HR
  have FL := HF.subst W.typed
  have FR := HG.subst W.typed
  simp only [ProofShape.subst] at FL FR
  obtain ⟨TX, TL⟩ := FL.app_parts HL
  have TY := (FR.app_parts HR).1
  have TR := FR.app_result_left heq hs TX (p := .ground) HX.base.ground HR
  rw [tree_inst] at TL TR
  have RL := left W TX
  have RR := right W TY
  have body := H.2.2 W HX
    (PiInertEvidence.core_source (n := 0) hs hc HL RL).base.1
    (PiInertEvidence.core_source (n := 0) hs hc HR RR).base.1
  exact body.prefixes heq hs hc TL TR RL RR

/-- Eta expansion and the original function construct both complete recursive
call orientations from self action. Typed arguments handle proof domains;
fresh testing supplies each ground history. No eta comparison is a premise. -/
theorem pi_inert_guarded_eta_pair
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hRigid : ∀ {c}, env.Rigid c → ∀ levels rhs, ¬ D.unfolds c levels rhs)
    (H : PiInertGuardedTreeValue (.call A B p q) ProofShape.Subst.id D Δ f f (.forallE A B))
    (S : DomainSort Δ A u) (hn : f ≠ .proof)
    (supply : PiInertGuardedTreeSupply p ProofShape.Subst.id D Δ A) :
    PiInertGuardedPair D Δ (.call A B p q) (.call A B p q) ProofShape.Subst.id ProofShape.Subst.id
      (.lam A (.app (f.liftN 1) (etaArgument u))) f (.forallE A B) (.forallE A B) := by
  have HF := H.base.left
  have HE := HF.eta_expansion S hn
  have beta {Λ σ x} (W : PiInertCoreWorld D Δ Λ σ) (HX : TypedAt Λ x (A.subst σ)) :
      Compute (ErasedLevelCore D)
        (.app ((ProofShape.lam A (.app (f.liftN 1) (etaArgument u))).subst σ) x)
        (.app (f.subst σ) x) := by
    have E : ((ProofShape.app (f.liftN 1) (etaArgument u)).subst σ.lift).inst x =
        .app (f.subst σ) x := by
      simp only [ProofShape.subst, ProofShape.lift_subst_lift, etaArgument_subst,
        ProofShape.inst, value_inst_lift, HX.eta_argument_inst (ContextSubstitution.sort W.typed S)]
    exact E ▸ ProofShape.Compute.beta (ProofShape.BetaRed.beta (A := A.subst σ))
  exact ⟨H.call_application_prefixes heq hs hc hRigid HE HF supply beta (fun _ _ => .refl),
    H.call_application_prefixes heq hs hc hRigid HF HE supply (fun _ _ => .refl) beta⟩

end Lean4Lean.VEnv.Strengthening
