import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertGuardedInputAction

/-! # Recursive guarded interfaces for finite higher-order uses

An interface tree records the exposed Pi at each guarded call. Input and
dependent output requirements recurse, while leaves retain ordinary finite
demands. An explicit annotation substitution keeps recursive result types
dependent without treating a guarded type computation as an ordinary core join.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private weak_subst from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertDemandBinders
open private value_inst_lift from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertWorldValues
open private erase_forallE_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
open private erase_sort_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureComparison

private theorem tree_comp_assoc (ρ σ τ : ProofShape.Subst) :
    (ρ.comp σ).comp τ = ρ.comp (σ.comp τ) := by
  funext i
  exact ProofShape.subst_subst _ _ _

private theorem tree_cons_comp (ρ σ : ProofShape.Subst) (x : ProofShape) :
    (ρ.cons x).comp σ = (ρ.comp σ).cons (x.subst σ) := by
  funext i
  cases i <;> rfl

private theorem tree_id_comp (σ : ProofShape.Subst) : ProofShape.Subst.id.comp σ = σ := rfl

private theorem tree_comp_id (σ : ProofShape.Subst) : σ.comp ProofShape.Subst.id = σ := by
  funext i
  exact ProofShape.subst_id _

private theorem tree_lift_cons (ρ σ : ProofShape.Subst) (x : ProofShape) :
    ρ.lift.comp (σ.cons x) = (ρ.comp σ).cons x := by
  funext i
  cases i with
  | zero => rfl
  | succ i => exact ProofShape.lift_subst_cons _ _ _

private theorem tree_shift_cons (σ : ProofShape.Subst) (x : ProofShape) :
    ProofShape.Subst.comp (fun i => ProofShape.bvar (i+1)) (σ.cons x) = σ := rfl

private theorem tree_inst (B : ProofShape) (σ : ProofShape.Subst) (x : ProofShape) :
    (B.subst σ.lift).inst x = B.subst (σ.cons x) := by
  simp only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN, ProofShape.subst_subst,
    ProofShape.Subst.lift_comp_one]

variable [Params] {D : Definitions}

/-- A finite tree of uses. The call's domain and input tree live outside
its binder; its codomain and output tree live under that binder. Both permits
several different interfaces for the same operand pair. -/
inductive PiInertGuardedTree where
  | plain (demand : PiInertDemand)
  | call (domain codomain : ProofShape) (input output : PiInertGuardedTree)
  | both (left right : PiInertGuardedTree)

/-- Substitute the annotations of a tree, respecting output binders. -/
def PiInertGuardedTree.subst : PiInertGuardedTree → ProofShape.Subst → PiInertGuardedTree
  | .plain p, _ => .plain p
  | .both p q, σ => .both (p.subst σ) (q.subst σ)
  | .call A B p q, σ => .call (A.subst σ) (B.subst σ.lift) (p.subst σ) (q.subst σ.lift)

/-- Common assigned payload for recursive guarded calls. -/
structure PiInertAssignedBase (D : Definitions) (Δ : List ProofShape)
    (a b T : ProofShape) : Prop where
  left : TypedAt Δ a T
  right : TypedAt Δ b T
  ground : PiInertDemandBase D Δ a b T

/-- Recursive guarded action at the selected carrier. A call retains its own
exposed Pi and consumes the full recursively guarded input tree. Its output
tree is instantiated at the left argument, as is its dependent result type. -/
def PiInertGuardedTreeValue : PiInertGuardedTree → ProofShape.Subst →
    Definitions → List ProofShape → ProofShape → ProofShape → ProofShape → Prop
  | .plain p, _, D, Δ, a, b, T =>
      TypedAt Δ a T ∧ TypedAt Δ b T ∧ PiInertDemandValue p D Δ a b T
  | .both p q, ρ, D, Δ, a, b, T =>
      PiInertGuardedTreeValue p ρ D Δ a b T ∧ PiInertGuardedTreeValue q ρ D Δ a b T
  | .call A B p q, ρ, D, Δ, a, b, T =>
      PiInertAssignedBase D Δ a b T ∧
      (∃ n, PiInertWorldComputation D n Δ T (.forallE (A.subst ρ) (B.subst ρ.lift))) ∧
      ∀ {Λ σ x y}, PiInertCoreWorld D Δ Λ σ →
        PiInertGuardedTreeValue p (ρ.comp σ) D Λ x y (A.subst (ρ.comp σ)) →
        TypedSource Λ (.app (a.subst σ) x) → TypedSource Λ (.app (b.subst σ) y) →
        PiInertGuardedTreeValue q ((ρ.comp σ).cons x) D Λ
          (.app (a.subst σ) x) (.app (b.subst σ) y) (B.subst ((ρ.comp σ).cons x))

/-- Every recursive tree retains assigned ground evidence. -/
theorem PiInertGuardedTreeValue.base (H : PiInertGuardedTreeValue p ρ D Δ a b T) :
    PiInertAssignedBase D Δ a b T := by
  induction p with
  | plain => exact ⟨H.1, H.2.1, H.2.2.base⟩
  | both p q ih _ => exact ih H.1
  | call => exact H.1

/-- Assigned ground evidence moves through the actual typed world map. -/
theorem PiInertAssignedBase.move (H : PiInertAssignedBase D Δ a b T)
    (W : PiInertCoreWorld D Δ Λ σ) :
    PiInertAssignedBase D Λ (a.subst σ) (b.subst σ) (T.subst σ) := by
  exact ⟨H.left.subst W.typed, H.right.subst W.typed,
    (PiInertDemandValue.move (p := .ground) H.ground W)⟩

/-- Recursive interface annotations and all retained action move together. -/
theorem PiInertGuardedTreeValue.move (H : PiInertGuardedTreeValue p ρ D Δ a b T)
    (W : PiInertCoreWorld D Δ Λ σ) :
    PiInertGuardedTreeValue p (ρ.comp σ) D Λ (a.subst σ) (b.subst σ) (T.subst σ) := by
  induction p generalizing ρ Δ Λ σ a b T with
  | plain => exact ⟨H.1.subst W.typed, H.2.1.subst W.typed, H.2.2.move W⟩
  | both p q ihp ihq => exact ⟨ihp H.1 W, ihq H.2 W⟩
  | call A B p q =>
    obtain ⟨n, R⟩ := H.2.1
    refine ⟨H.1.move W, ⟨n, ?_⟩, ?_⟩
    · simpa only [ProofShape.subst, ProofShape.subst_subst, ProofShape.Subst.comp_lift] using R.move W
    · intro Ξ τ x y V HX HL HR
      simp only [tree_comp_assoc, ProofShape.subst_subst] at HX HL HR ⊢
      exact H.2.2 (W.compose V) HX HL HR

/-- Substituting a tree's syntax is equivalent to composing its annotation
environment. This includes dependent result trees and contravariant inputs. -/
theorem PiInertGuardedTreeValue.subst_iff :
    PiInertGuardedTreeValue (p.subst σ) ρ D Δ a b T ↔
      PiInertGuardedTreeValue p (σ.comp ρ) D Δ a b T := by
  induction p generalizing σ ρ Δ a b T with
  | plain => rfl
  | both p q ihp ihq =>
    simp only [PiInertGuardedTree.subst, PiInertGuardedTreeValue, ihp, ihq]
  | call A B p q ihp ihq =>
    simp only [PiInertGuardedTree.subst, PiInertGuardedTreeValue, ihp, ihq,
      ProofShape.subst_subst, ← ProofShape.Subst.comp_lift, tree_lift_cons, tree_comp_assoc]

/-- A local call consumes the complete recursive input tree and returns the
complete dependent output tree. Actual selected assignments provide its world. -/
theorem PiInertGuardedTreeValue.app
    (heq : env.HasCanonicalEq) (hc : TypedCoreConfluence (ErasedLevelCore D))
    (H : PiInertGuardedTreeValue (.call A B p q) ρ D Δ f g T)
    (HX : PiInertGuardedTreeValue p ρ D Δ x y (A.subst ρ))
    (HL : TypedSource Δ (.app f x)) (HR : TypedSource Δ (.app g y)) :
    PiInertGuardedTreeValue q (ρ.cons x) D Δ (.app f x) (.app g y) (B.subst (ρ.cons x)) := by
  have W := PiInertCoreWorld.identity_source (D := D) heq hc H.1.left.sources.1
  simpa only [tree_comp_id, ProofShape.subst_id] using H.2.2 W
    (by simpa only [tree_comp_id] using HX)
    (by simpa only [ProofShape.subst_id] using HL)
    (by simpa only [ProofShape.subst_id] using HR)

/-- Typed core predecessors preserve recursive guarded action. The assigned
original operands prevent proof erasure from silently changing their carriers;
recursive output assignments are derived from whole application sources. -/
theorem PiInertGuardedTreeValue.prefixes
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (H : PiInertGuardedTreeValue p ρ D Δ a' b' T)
    (HA : TypedAt Δ a T) (HB : TypedAt Δ b T)
    (RA : Compute (ErasedLevelCore D) a a') (RB : Compute (ErasedLevelCore D) b b') :
    PiInertGuardedTreeValue p ρ D Δ a b T := by
  induction p generalizing ρ Δ a b a' b' T with
  | plain => exact ⟨HA, HB, H.2.2.prefixes hs hc HA.sources.1 HB.sources.1 RA RB⟩
  | both p q ihp ihq => exact ⟨ihp H.1 HA HB RA RB, ihq H.2 HA HB RA RB⟩
  | call A B p q _ ih =>
    refine ⟨⟨HA, HB, PiInertDemandValue.prefixes (p := .ground) hs hc H.1.ground
      HA.sources.1 HB.sources.1 RA RB⟩, H.2.1, ?_⟩
    intro Λ σ x y W HX HL HR
    have RL : Compute (ErasedLevelCore D) (.app (a.subst σ) x) (.app (a'.subst σ) x) :=
      .app (RA.subst (fun R => erased_level_core_subst R)) .refl
    have RR : Compute (ErasedLevelCore D) (.app (b.subst σ) y) (.app (b'.subst σ) y) :=
      .app (RB.subst (fun R => erased_level_core_subst R)) .refl
    have body := H.2.2 W HX
      (PiInertEvidence.core_source (n := 0) hs hc HL RL).base.1
      (PiInertEvidence.core_source (n := 0) hs hc HR RR).base.1
    obtain ⟨n, R⟩ := H.2.1
    have FL := (HA.world_computation heq hs R).subst W.typed
    have FR := (HB.world_computation heq hs R).subst W.typed
    simp only [ProofShape.subst, ProofShape.subst_subst, ← ProofShape.Subst.comp_lift] at FL FR
    obtain ⟨TX, TL⟩ := FL.app_parts HL
    have TR := FR.app_result_left heq hs TX (p := .ground) HX.base.ground HR
    rw [tree_inst] at TL TR
    exact ih body TL TR RL RR

/-- Type-only exposure supply for a tree. Native function values need the
chosen root exposure and supplies for their result trees at every typed input.
No equality or function action occurs in this certificate. Input-tree supply
is unnecessary here because callers supply their actual input values. -/
def PiInertGuardedTreeSupply : PiInertGuardedTree → ProofShape.Subst →
    Definitions → List ProofShape → ProofShape → Prop
  | .plain _, _, _, _, _ => True
  | .both p q, ρ, D, Δ, T =>
      PiInertGuardedTreeSupply p ρ D Δ T ∧ PiInertGuardedTreeSupply q ρ D Δ T
  | .call A B _ q, ρ, D, Δ, T =>
      (∃ n, PiInertWorldComputation D n Δ T (.forallE (A.subst ρ) (B.subst ρ.lift))) ∧
      ∀ {Λ σ x}, PiInertCoreWorld D Δ Λ σ → TypedAt Λ x (A.subst (ρ.comp σ)) →
        PiInertGuardedTreeSupply q ((ρ.comp σ).cons x) D Λ (B.subst ((ρ.comp σ).cons x))

/-- Type-only supplies move through composed worlds without creating action. -/
theorem PiInertGuardedTreeSupply.move (H : PiInertGuardedTreeSupply p ρ D Δ T)
    (W : PiInertCoreWorld D Δ Λ σ) :
    PiInertGuardedTreeSupply p (ρ.comp σ) D Λ (T.subst σ) := by
  induction p generalizing ρ Δ Λ σ T with
  | plain => trivial
  | both p q ihp ihq => exact ⟨ihp H.1 W, ihq H.2 W⟩
  | call A B p q =>
    obtain ⟨n, R⟩ := H.1
    refine ⟨⟨n, ?_⟩, ?_⟩
    · simpa only [ProofShape.subst, ProofShape.subst_subst, ProofShape.Subst.comp_lift] using R.move W
    · intro Ξ τ x V HX
      simp only [tree_comp_assoc] at HX ⊢
      exact H.2 (W.compose V) HX

/-- Native neutral-returning values construct full recursive guarded action
from type-only supplies. The proof recurses on result trees; argument ground
history suffices for the neutral application rule, even when the argument
itself is a lambda carrying a recursively guarded tree. -/
theorem PiInertWorldValue.guarded_tree
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hRigid : ∀ {c}, env.Rigid c → ∀ levels rhs, ¬ D.unfolds c levels rhs)
    (H : PiInertWorldValue D n Δ a b T)
    (HA : TypedAt Δ a T) (HB : TypedAt Δ b T)
    (S : PiInertGuardedTreeSupply p ρ D Δ T) :
    PiInertGuardedTreeValue p ρ D Δ a b T := by
  induction p generalizing ρ n Δ a b T with
  | plain => exact ⟨HA, HB, (PiInertCarrierValue.neutral H).demand heq hs hc hRigid HA.sources.2⟩
  | both p q ihp ihq => exact ⟨ihp H HA HB S.1, ihq H HA HB S.2⟩
  | call A B p q _ ih =>
    refine ⟨⟨HA, HB, HA.sources.1, HB.sources.1, HA.sources.2, n, H.history hs hc⟩, S.1, ?_⟩
    intro Λ σ x y W HX HL HR
    obtain ⟨m, R⟩ := S.1
    have HF := HA.world_computation heq hs R
    have HG := HB.world_computation heq hs R
    have FL := HF.subst W.typed
    have FR := HG.subst W.typed
    simp only [ProofShape.subst, ProofShape.subst_subst, ← ProofShape.Subst.comp_lift] at FL FR
    obtain ⟨TX, TL⟩ := FL.app_parts HL
    have TR := FR.app_result_left heq hs TX (p := .ground) HX.base.ground HR
    have EW : (B.subst (ρ.comp σ).lift).inst x = B.subst ((ρ.comp σ).cons x) := by
      simp only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN, ProofShape.subst_subst,
        ProofShape.Subst.lift_comp_one]
    rw [EW] at TL TR
    obtain ⟨k, HK⟩ := HX.base.ground.history
    have R' : PiInertWorldComputation D m Λ (T.subst σ)
        (.forallE (A.subst (ρ.comp σ)) (B.subst (ρ.comp σ).lift)) := by
      simpa only [ProofShape.subst, ProofShape.subst_subst, ProofShape.Subst.comp_lift] using R.move W
    have HV := (((H.move W).raise (Nat.le_max_left n m)).convert
      (R'.raise (Nat.le_max_right n m)))
    have result := (HV.raise (Nat.le_max_left (max n m) k)).app
      (HK.raise (Nat.le_max_right (max n m) k)) HL HR
    rw [EW] at result
    exact ih result TL TR (S.2 W TX)

/-- A typed proof marker supplies every recursive tree whose type exposures
are supplied. Calls cannot have a typed proof-marker head. -/
theorem pi_inert_proof_guarded_tree
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (HA : TypedAt Δ .proof T) (S : PiInertGuardedTreeSupply p ρ D Δ T) :
    PiInertGuardedTreeValue p ρ D Δ .proof .proof T := by
  induction p with
  | plain => exact ⟨HA, HA, pi_inert_proof_demand_value hc HA.sources.1 HA.sources.2⟩
  | both p q ihp ihq => exact ⟨ihp S.1, ihq S.2⟩
  | call =>
    refine ⟨⟨HA, HA, PiInertDemandBase.refl hc HA.sources.1 HA.sources.2⟩, S.1, ?_⟩
    intro Λ σ x y W HX HL HR
    exact HL.not_proof_app.elim

/-- Fresh arguments construct recursive guarded trees from type-only supply.
This is the fresh-variable instance required for function ground readout. -/
theorem pi_inert_fresh_guarded_tree
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hRigid : ∀ {c}, env.Rigid c → ∀ levels rhs, ¬ D.unfolds c levels rhs)
    (S : DomainSort Δ A u) (supply : PiInertGuardedTreeSupply p ρ D Δ A) :
    PiInertGuardedTreeValue p (ρ.comp (fun i => .bvar (i+1))) D (A::Δ)
      (etaArgument u) (etaArgument u) (A.liftN 1) := by
  have W := PiInertCoreWorld.weakening (D := D) heq hc S
  have supply' : PiInertGuardedTreeSupply p (ρ.comp (fun i => .bvar (i+1))) D (A::Δ) (A.liftN 1) := by
    simpa only [weak_subst] using supply.move W
  obtain ⟨Γ, C, hΓ, EΓ, hC, EC⟩ := S
  have hΓC : OnCtx (C::Γ) (env.IsType univs) := ⟨hΓ, u, hC⟩
  have HA : TypedAt (A::Δ) (etaArgument u) (A.liftN 1) :=
    ⟨C::Γ, .bvar 0, C.lift, hΓC, by simp only [proofEraseCtx, EC, EΓ],
      .bvar .zero, proofErase_fresh_argument hΓ hC,
      (proofErase_liftN hΓ hΓC Ctx.LiftN.one hC).trans (congrArg (fun e => e.liftN 1) EC)⟩
  classical
  by_cases hu : u ≈ .zero
  · simp only [etaArgument, if_pos hu] at HA ⊢
    exact pi_inert_proof_guarded_tree hc HA supply'
  · simp only [etaArgument, if_neg hu] at HA ⊢
    have HV : PiInertWorldValue D 0 (A::Δ) (.bvar 0) (.bvar 0) (A.liftN 1) :=
      pi_inert_native_variable_world_neutral.value HA.sources.1 HA.sources.1
    exact HV.guarded_tree heq hs hc hRigid HA HA supply'

/-- Actual functions obtain their ground history by testing a recursively
guarded fresh argument. The supply concerns types alone; the call premise
must construct result history and is not a supplied function equality. -/
theorem pi_inert_tree_calls_typed_base
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hRigid : ∀ {c}, env.Rigid c → ∀ levels rhs, ¬ D.unfolds c levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (.forallE C E))
    (hg : env.HasType univs Γ g (.forallE C E))
    (supply : PiInertGuardedTreeSupply p ρ D (proofEraseCtx Γ) (proofErase Γ C))
    (run : ∀ {Λ σ x y}, PiInertCoreWorld D (proofEraseCtx Γ) Λ σ →
      PiInertGuardedTreeValue p (ρ.comp σ) D Λ x y ((proofErase Γ C).subst σ) →
      TypedSource Λ (.app ((proofErase Γ f).subst σ) x) →
      TypedSource Λ (.app ((proofErase Γ g).subst σ) y) →
      PiInertDemandBase D Λ (.app ((proofErase Γ f).subst σ) x)
        (.app ((proofErase Γ g).subst σ) y) (((proofErase (C::Γ) E).subst σ.lift).inst x)) :
    PiInertDemandBase D (proofEraseCtx Γ)
      (proofErase Γ f) (proofErase Γ g) (proofErase Γ (.forallE C E)) := by
  have TF := TypedAt.of_typed hΓ hf
  have TG := TypedAt.of_typed hΓ hg
  by_cases hp : IsProof Γ f
  · have hgp := isProof_of_common_type hΓ hf hg hp
    have HF := TF.sources.1
    rw [proofErase_eq_proof.2 hp] at HF
    have HT := TF.sources.2
    rw [proofErase_eq_proof.2 hp, proofErase_eq_proof.2 hgp]
    exact PiInertDemandBase.refl hc HF HT
  have hng : ¬ IsProof Γ g := fun hgp => hp (isProof_of_common_type hΓ hg hf hgp)
  obtain ⟨_, hPi⟩ := hf.isType henv hΓ
  obtain ⟨⟨u, hC⟩, ⟨v, hE⟩⟩ := hPi.forallE_inv henv.ordered
  have EP : proofErase Γ (.forallE C E) =
      .forallE (proofErase Γ C) (proofErase (C::Γ) E) := if_neg (not_isProof_of_sort hΓ hPi)
  have SC := DomainSort.of_typed hΓ hC
  have W := PiInertCoreWorld.weakening (D := D) heq hc SC
  have hΓC : OnCtx (C::Γ) (env.IsType univs) := ⟨hΓ, u, hC⟩
  have hFresh (a : VExpr) (ha : env.HasType univs Γ a (.forallE C E)) :
      env.HasType univs (C::Γ) (.app a.lift (.bvar 0)) E := by
    simpa only [VExpr.lift, VExpr.liftN, VExpr.inst_liftN_bvar, VExpr.inst] using
      HasType.app (ha.weak henv) (.bvar .zero)
  have freshSource (a : VExpr) (ha : env.HasType univs Γ a (.forallE C E))
      (hn : ¬ IsProof Γ a) :
      TypedSource (proofErase Γ C :: proofEraseCtx Γ)
        (.app ((proofErase Γ a).liftN 1) (etaArgument u)) :=
    ⟨C::Γ, .app a.lift (.bvar 0), E, hΓC, rfl, hFresh a ha, proofErase_eta_body hΓ hC ha hn⟩
  have HX : PiInertGuardedTreeValue p (ρ.comp (fun i => .bvar (i+1))) D
      (proofErase Γ C :: proofEraseCtx Γ) (etaArgument u) (etaArgument u)
      ((proofErase Γ C).subst (fun i => .bvar (i+1))) := by
    simpa only [weak_subst] using pi_inert_fresh_guarded_tree heq hs hc hRigid SC supply
  have body := run W HX
    (by simpa only [weak_subst] using freshSource f hf hp)
    (by simpa only [weak_subst] using freshSource g hg hng)
  have HE : TypedSource (proofErase Γ C :: proofEraseCtx Γ) (proofErase (C::Γ) E) :=
    ⟨C::Γ, E, .sort v, hΓC, rfl, hE, rfl⟩
  rw [HE.fresh_inst heq hc SC] at body
  simp only [weak_subst] at body
  obtain ⟨m, history⟩ := body.history
  exact ⟨TF.sources.1, TG.sources.1, TF.sources.2, m,
    EP.symm ▸ history.function heq hs hc SC⟩

/-- Assigned raw functions inherit fresh recursive-tree ground readout. -/
theorem pi_inert_tree_calls_base
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hRigid : ∀ {c}, env.Rigid c → ∀ levels rhs, ¬ D.unfolds c levels rhs)
    (hf : TypedAt Δ f (.forallE C E)) (hg : TypedAt Δ g (.forallE C E))
    (supply : PiInertGuardedTreeSupply p ρ D Δ C)
    (run : ∀ {Λ σ x y}, PiInertCoreWorld D Δ Λ σ →
      PiInertGuardedTreeValue p (ρ.comp σ) D Λ x y (C.subst σ) →
      TypedSource Λ (.app (f.subst σ) x) → TypedSource Λ (.app (g.subst σ) y) →
      PiInertDemandBase D Λ (.app (f.subst σ) x) (.app (g.subst σ) y) ((E.subst σ.lift).inst x)) :
    PiInertAssignedBase D Δ f g (.forallE C E) := by
  refine ⟨hf, hg, ?_⟩
  obtain ⟨Γ, f₀, F, hΓ, rfl, hf₀, Ef, EF⟩ := hf
  obtain ⟨C₀, E₀, rfl, _, EC, EE⟩ := erase_forallE_inv EF
  obtain ⟨_, hPi⟩ := hf₀.isType henv hΓ
  obtain ⟨g₀, hg₀, Eg⟩ := hg.realize_carrier hΓ hPi EF
  rw [← Ef, ← Eg, ← EF]
  apply pi_inert_tree_calls_typed_base heq hs hc hRigid hΓ hf₀ hg₀
    (by simpa only [EC] using supply)
  intro Λ σ x y W HX HL HR
  simp only [EC, EE, Ef, Eg] at HX HL HR ⊢
  exact run W HX HL HR

/-- Recursive typed calls construct a complete function tree, including its
ground history. Input exposure supply is explicit and type-only. -/
theorem PiInertGuardedTreeValue.of_calls
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hRigid : ∀ {c}, env.Rigid c → ∀ levels rhs, ¬ D.unfolds c levels rhs)
    (hf : TypedAt Δ f (.forallE A B)) (hg : TypedAt Δ g (.forallE A B))
    (supply : PiInertGuardedTreeSupply p ProofShape.Subst.id D Δ A)
    (run : ∀ {Λ σ x y}, PiInertCoreWorld D Δ Λ σ →
      PiInertGuardedTreeValue p σ D Λ x y (A.subst σ) →
      TypedSource Λ (.app (f.subst σ) x) → TypedSource Λ (.app (g.subst σ) y) →
      PiInertGuardedTreeValue q (σ.cons x) D Λ
        (.app (f.subst σ) x) (.app (g.subst σ) y) (B.subst (σ.cons x))) :
    PiInertGuardedTreeValue (.call A B p q) ProofShape.Subst.id D Δ f g (.forallE A B) := by
  have ground := pi_inert_tree_calls_base heq hs hc hRigid hf hg supply
    (fun W HX HL HR => by
      rw [tree_inst]
      exact (run W HX HL HR).base.ground)
  refine ⟨ground, ⟨0, ?_⟩, ?_⟩
  · simpa only [ProofShape.subst_id, ProofShape.Subst.id_lift] using
      (PiInertEvidence.of_core_join hc hf.sources.2 hf.sources.2 .refl).world_computation
  · intro Λ σ x y W HX HL HR
    exact run W HX HL HR

/-- A further selected-type prefix preserves a call tree's entire recursive
action. Its fixed exposed interface remains unchanged; ordinary-demand leaves
are not asserted to transport through arbitrary guarded type computations. -/
theorem PiInertGuardedTreeValue.call_prefix
    (H : PiInertGuardedTreeValue (.call A B p q) ρ D Δ a b T)
    (HA : TypedAt Δ a C) (HB : TypedAt Δ b C)
    (R : PiInertWorldComputation D n Δ C T) :
    PiInertGuardedTreeValue (.call A B p q) ρ D Δ a b C := by
  obtain ⟨m, HM⟩ := H.1.ground.history
  have ground : PiInertDemandBase D Δ a b C :=
    ⟨HA.sources.1, HB.sources.1, HA.sources.2, max n m,
      (HM.raise (Nat.le_max_right n m)).carrier_prefix (R.raise (Nat.le_max_left n m))⟩
  obtain ⟨k, S⟩ := H.2.1
  exact ⟨⟨HA, HB, ground⟩, ⟨max n k,
    (R.raise (Nat.le_max_left n k)).trans (S.raise (Nat.le_max_right n k))⟩, H.2.2⟩

/-- Original strong conversion children retain recursive call action when
the new selected carrier has an explicit guarded path to the old carrier.
The original type child supplies assignments, not the missing path. -/
theorem StrongBounded.guarded_tree_call_convert
    (typeChild : StrongBounded env univs k Γ T C (.sort u))
    (termChild : StrongBounded env univs k Γ a b T)
    (hΓ : OnCtx Γ (env.IsType univs))
    (H : PiInertGuardedTreeValue (.call A B p q) ρ D (proofEraseCtx Γ)
      (proofErase Γ a) (proofErase Γ b) (proofErase Γ T))
    (R : PiInertWorldComputation D n (proofEraseCtx Γ) (proofErase Γ C) (proofErase Γ T)) :
    PiInertGuardedTreeValue (.call A B p q) ρ D (proofEraseCtx Γ)
      (proofErase Γ a) (proofErase Γ b) (proofErase Γ C) := by
  have HE := typeChild.strong.defeq
  have HT := termChild.strong.defeq
  exact H.call_prefix (TypedAt.of_typed hΓ (HE.defeq HT.hasType.1))
    (TypedAt.of_typed hΓ (HE.defeq HT.hasType.2)) R

/-- Evaluator lambdas consume and return recursive guarded trees at arbitrary
finite depth. Captured inputs may themselves be lambdas with guarded call
requirements. Fresh testing constructs the evaluator's ground history from
the explicit type-only supply for its function argument. -/
theorem pi_inert_guarded_tree_evaluator
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hRigid : ∀ {c}, env.Rigid c → ∀ levels rhs, ¬ D.unfolds c levels rhs)
    (HZ : PiInertGuardedTreeValue p ProofShape.Subst.id D Δ z w A)
    (supply : PiInertGuardedTreeSupply (.call A B p q) ProofShape.Subst.id D Δ C)
    (HF : TypedAt Δ (.lam C (.app (.bvar 0) (z.liftN 1))) (.forallE C ((B.inst z).liftN 1)))
    (HG : TypedAt Δ (.lam C (.app (.bvar 0) (w.liftN 1))) (.forallE C ((B.inst z).liftN 1))) :
    PiInertGuardedTreeValue
      (.call C ((B.inst z).liftN 1) (.call A B p q)
        ((q.subst (.one z)).subst (fun i => .bvar (i+1)))) ProofShape.Subst.id D Δ
      (.lam C (.app (.bvar 0) (z.liftN 1))) (.lam C (.app (.bvar 0) (w.liftN 1)))
      (.forallE C ((B.inst z).liftN 1)) := by
  apply PiInertGuardedTreeValue.of_calls heq hs hc hRigid HF HG supply
  intro Λ σ x y W HX HL HR
  have beta (a x : ProofShape) : Compute (ErasedLevelCore D)
      (.app ((ProofShape.lam C (.app (.bvar 0) (a.liftN 1))).subst σ) x)
      (.app x (a.subst σ)) := by
    have E : ((ProofShape.app (.bvar 0) (a.liftN 1)).subst σ.lift).inst x =
        .app x (a.subst σ) := by
      simp only [ProofShape.subst, ProofShape.Subst.lift, ProofShape.lift_subst_lift,
        ProofShape.inst, Nat.lt_irrefl, ↓reduceIte, ProofShape.liftN_zero]
      exact congrArg (ProofShape.app x) (value_inst_lift (a.subst σ) x)
    exact E ▸ ProofShape.Compute.beta (ProofShape.BetaRed.beta (A := C.subst σ))
  have HL' := (PiInertEvidence.core_source (n := 0) hs hc HL (beta z x)).base.1
  have HR' := (PiInertEvidence.core_source (n := 0) hs hc HR (beta w y)).base.1
  have body := HX.app heq hc (HZ.move W) HL' HR'
  have FL := HF.subst W.typed
  have FR := HG.subst W.typed
  simp only [ProofShape.subst] at FL FR
  obtain ⟨TX, TL⟩ := FL.app_parts HL
  have TR := FR.app_result_left heq hs TX (p := .ground) HX.base.ground HR
  simp only [ProofShape.lift_subst_lift, value_inst_lift, ProofShape.subst_inst, tree_inst] at TL TR
  have result := body.prefixes heq hs hc TL TR
    (by simpa only [ProofShape.subst, ProofShape.lift_subst_lift] using beta z x)
    (by simpa only [ProofShape.subst, ProofShape.lift_subst_lift] using beta w y)
  simpa only [PiInertGuardedTreeValue.subst_iff, tree_shift_cons,
    ProofShape.Subst.one, tree_cons_comp, tree_id_comp,
    ProofShape.lift_subst_cons, ProofShape.subst_inst, tree_inst,
    ProofShape.subst, ProofShape.lift_subst_lift] using result

/-- Actual type equality transports a raw assignment without assuming any
computational interface certificate. It does not transport value action. -/
theorem ProofShape.TypedAt.actual_type_eq
    (hΓ : OnCtx Γ (env.IsType univs)) (HE : env.IsDefEq univs Γ A B (.sort u))
    (H : TypedAt (proofEraseCtx Γ) a (proofErase Γ A)) :
    TypedAt (proofEraseCtx Γ) a (proofErase Γ B) := by
  obtain ⟨a₀, ha, Ea⟩ := H.realize_carrier hΓ HE.hasType.1 rfl
  exact ⟨Γ, a₀, B, hΓ, rfl, HE.defeq ha, Ea, rfl⟩

/-- Evaluators returning universes construct recursive call trees from actual
typings. The captured argument may already carry any recursive tree; no raw
evaluator source or ground function equality is a premise. -/
theorem pi_inert_actual_tree_evaluator_to_sort
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hRigid : ∀ {c}, env.Rigid c → ∀ levels rhs, ¬ D.unfolds c levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (HC : env.IsDefEq univs Γ C (.forallE A (.sort v)) (.sort u))
    (hz : env.HasType univs Γ z A) (hw : env.HasType univs Γ w A)
    (HZ : PiInertGuardedTreeValue p ProofShape.Subst.id D (proofEraseCtx Γ)
      (proofErase Γ z) (proofErase Γ w) (proofErase Γ A))
    (R : PiInertWorldComputation D n (proofEraseCtx Γ) (proofErase Γ C)
      (.forallE (proofErase Γ A) (.sort v))) :
    PiInertGuardedTreeValue
      (.call (proofErase Γ C) (.sort v) (.call (proofErase Γ A) (.sort v) p (.plain q)) (.plain q))
      ProofShape.Subst.id D (proofEraseCtx Γ)
      (.lam (proofErase Γ C) (.app (.bvar 0) ((proofErase Γ z).liftN 1)))
      (.lam (proofErase Γ C) (.app (.bvar 0) ((proofErase Γ w).liftN 1)))
      (.forallE (proofErase Γ C) (.sort v)) := by
  have supply : PiInertGuardedTreeSupply
      (.call (proofErase Γ A) (.sort v) p (.plain q)) ProofShape.Subst.id D
      (proofEraseCtx Γ) (proofErase Γ C) := by
    refine ⟨⟨n, ?_⟩, ?_⟩
    · simpa only [ProofShape.subst_id, ProofShape.Subst.id_lift, ProofShape.subst] using R
    · intro Λ σ x W HX
      trivial
  simpa only [ProofShape.inst, ProofShape.liftN, PiInertGuardedTree.subst] using
    pi_inert_guarded_tree_evaluator heq hs hc hRigid HZ supply
      (TypedAt.evaluator_to_sort hΓ HC hz) (TypedAt.evaluator_to_sort hΓ HC hw)

/-- Assigned raw functions returning universes construct their application
sources from an assigned argument. Actual realization and non-proofness of a
sorted result justify the raw application shape. -/
theorem ProofShape.TypedAt.app_to_sort
    (HF : TypedAt Δ f (.forallE A (.sort u))) (HX : TypedAt Δ x A) :
    TypedAt Δ (.app f x) (.sort u) := by
  obtain ⟨Γ, f₀, F, hΓ, rfl, hf, Ef, EF⟩ := HF
  obtain ⟨A₀, B₀, rfl, _, EA, EB⟩ := erase_forallE_inv EF
  obtain rfl := erase_sort_inv EB
  obtain ⟨_, hPi⟩ := hf.isType henv hΓ
  obtain ⟨⟨_, hA⟩, _⟩ := hPi.forallE_inv henv.ordered
  obtain ⟨x₀, hx, Ex⟩ := HX.realize_carrier hΓ hA EA
  have happ : env.HasType univs Γ (.app f₀ x₀) (.sort u) := hf.app hx
  refine ⟨Γ, .app f₀ x₀, .sort u, hΓ, rfl, happ, ?_, ?_⟩
  · rw [show proofErase Γ (.app f₀ x₀) = .app _ _ from
      if_neg (not_isProof_of_sort hΓ happ), Ef, Ex]
  · exact if_neg (not_isProof_of_sort hΓ (HasType.sort (happ.sort_r henv hΓ)))

/-- Native actual variables realize every recursively supplied tree. The
type-only supplies may contain guarded exposures at every call depth. -/
theorem pi_inert_native_guarded_tree
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hRigid : ∀ {c}, env.Rigid c → ∀ levels rhs, ¬ D.unfolds c levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs)) (lookup : Lookup Γ i T)
    (hn : ¬ IsProof Γ (.bvar i))
    (supply : PiInertGuardedTreeSupply p ρ D (proofEraseCtx Γ) (proofErase Γ T)) :
    PiInertGuardedTreeValue p ρ D (proofEraseCtx Γ)
      (proofErase Γ (.bvar i)) (proofErase Γ (.bvar i)) (proofErase Γ T) := by
  have HF := TypedAt.of_typed hΓ (HasType.bvar lookup)
  have EV : proofErase Γ (.bvar i) = .bvar i := if_neg hn
  have EO : contextOracle (proofEraseCtx Γ) i = proofErase Γ T := by
    rw [proofEraseCtx_oracle, erasedTypeOracle_valid hΓ lookup]
  have HV : PiInertWorldValue D 0 (proofEraseCtx Γ)
      (proofErase Γ (.bvar i)) (proofErase Γ (.bvar i)) (proofErase Γ T) := by
    rw [EV, ← EO]
    exact pi_inert_native_variable_world_neutral.value
      (EV ▸ HF.sources.1) (EV ▸ HF.sources.1)
  exact HV.guarded_tree heq hs hc hRigid HF HF supply

/-- A nested evaluator application uses recursive guarded action twice.
Both selected domains may be opaque aliases: actual type equalities and their
guarded exposures are explicit. The captured native function, both evaluator
trees, and the final application source are constructed from actual typings;
no function action or raw application source is assumed. -/
theorem pi_inert_nested_actual_tree_evaluators
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hRigid : ∀ {c}, env.Rigid c → ∀ levels rhs, ¬ D.unfolds c levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (HC : env.IsDefEq univs Γ C (.forallE A (.sort v)) (.sort u))
    (HK : env.IsDefEq univs Γ K (.forallE C (.sort v)) (.sort w))
    (hz : env.HasType univs Γ z A) (lookup : Lookup Γ i C)
    (RC : PiInertWorldComputation D n (proofEraseCtx Γ) (proofErase Γ C)
      (.forallE (proofErase Γ A) (.sort v)))
    (RK : PiInertWorldComputation D m (proofEraseCtx Γ) (proofErase Γ K)
      (.forallE (proofErase Γ C) (.sort v))) :
    let inner := ProofShape.lam (proofErase Γ C) (.app (.bvar 0) ((proofErase Γ z).liftN 1))
    let outer := ProofShape.lam (proofErase Γ K)
      (.app (.bvar 0) ((proofErase Γ (.bvar i)).liftN 1))
    PiInertGuardedTreeValue (.plain q) ProofShape.Subst.id D (proofEraseCtx Γ)
      (.app outer inner) (.app outer inner) (.sort v) := by
  dsimp only
  have TZ := TypedAt.of_typed hΓ hz
  have HZ : PiInertGuardedTreeValue (.plain .ground) ProofShape.Subst.id D (proofEraseCtx Γ)
      (proofErase Γ z) (proofErase Γ z) (proofErase Γ A) :=
    ⟨TZ, TZ, PiInertDemandBase.refl hc TZ.sources.1 TZ.sources.2⟩
  have inner := pi_inert_actual_tree_evaluator_to_sort (q := q) heq hs hc hRigid hΓ HC hz hz HZ RC
  have supply : PiInertGuardedTreeSupply
      (.call (proofErase Γ A) (.sort v) (.plain .ground) (.plain q)) ProofShape.Subst.id D
      (proofEraseCtx Γ) (proofErase Γ C) := by
    refine ⟨⟨n, ?_⟩, ?_⟩
    · simpa only [ProofShape.subst_id, ProofShape.Subst.id_lift, ProofShape.subst] using RC
    · intro Λ σ x W HX
      trivial
  have hf : env.HasType univs Γ (.bvar i) C := .bvar lookup
  have native := pi_inert_native_guarded_tree heq hs hc hRigid hΓ lookup
    (not_isProof_function_to_sort hΓ (HC.defeq hf)) supply
  have outer := pi_inert_actual_tree_evaluator_to_sort (q := q) heq hs hc hRigid hΓ HK hf hf native RK
  obtain ⟨⟨uC, hC⟩, ⟨uB, hB⟩⟩ := HK.hasType.2.forallE_inv henv.ordered
  have hΓC : OnCtx (C::Γ) (env.IsType univs) := ⟨hΓ, uC, hC⟩
  have EP : proofErase Γ (.forallE C (.sort v)) = .forallE (proofErase Γ C) (.sort v) := by
    rw [show proofErase Γ (.forallE C (.sort v)) = .forallE _ _ from
      if_neg (not_isProof_of_sort hΓ HK.hasType.2),
      show proofErase (C::Γ) (.sort v) = .sort v from if_neg (not_isProof_of_sort hΓC hB)]
  have TL := (EP.symm ▸ inner.base.left).actual_type_eq hΓ HK.symm
  have TR := (EP.symm ▸ inner.base.right).actual_type_eq hΓ HK.symm
  have argument := inner.call_prefix TL TR RK
  have application := outer.base.left.app_to_sort argument.base.left
  exact outer.app heq hc
    (by simpa only [ProofShape.subst_id] using argument) application.sources.1 application.sources.1

end Lean4Lean.VEnv.Strengthening
