import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertAssignedBodies
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureMaskedConstructorRecovery

/-! # Original type children at constant endpoints and constructor pivots

A constant's native type may lie on the right of the original constDF type
child. Record edge orientation instead of reconstructing a strong symmetry
at a larger rank. Native unit constructors then interpret transitivity at
arbitrary assigned carriers using original type children, without composing
the two erased term histories.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr

/-- A finite type path with either orientation of each original lower-rank
strong child. Backward edges retain the original child, not a newly constructed
strong symmetry derivation. -/
inductive BoundedTypePath (env : VEnv) (U bound : Nat) (Γ : List VExpr) :
    VExpr → VExpr → Prop where
  | refl : BoundedTypePath env U bound Γ A A
  | forward (hlt : k < bound) : BoundedTypePath env U bound Γ A B →
      StrongBounded env U k Γ B C (.sort u) → BoundedTypePath env U bound Γ A C
  | backward (hlt : k < bound) : BoundedTypePath env U bound Γ A C →
      StrongBounded env U k Γ B C (.sort u) → BoundedTypePath env U bound Γ A B

/-- Raising the outer bound preserves every recorded original child. -/
theorem BoundedTypePath.mono (H : BoundedTypePath env U n Γ A B) (hle : n ≤ m) :
    BoundedTypePath env U m Γ A B := by
  induction H with
  | refl => exact .refl
  | forward hlt H HE ih => exact .forward (Nat.lt_of_lt_of_le hlt hle) ih HE
  | backward hlt H HE ih => exact .backward (Nat.lt_of_lt_of_le hlt hle) ih HE

private def ConstantAssignment (env : VEnv) (U n : Nat)
    (Γ : List VExpr) (e T : VExpr) : Prop :=
  ∀ c ls, e = .const c ls → ∃ ci, env.constants c = some ci ∧
    (∀ l ∈ ls, l.WF U) ∧ ls.length = ci.uvars ∧
    BoundedTypePath env U n Γ (ci.type.instL ls) T

private theorem ConstantAssignment.mono (H : ConstantAssignment env U n Γ e T)
    (hle : n ≤ m) : ConstantAssignment env U m Γ e T := by
  intro c ls E
  obtain ⟨ci, hc, hw, hl, path⟩ := H c ls E
  exact ⟨ci, hc, hw, hl, path.mono hle⟩

private theorem ConstantAssignment.convert (H : ConstantAssignment env U n Γ e T)
    (HT : StrongBounded env U n Γ T V (.sort u)) :
    ConstantAssignment env U (n+1) Γ e V := by
  intro c ls E
  obtain ⟨ci, hc, hw, hl, path⟩ := H c ls E
  exact ⟨ci, hc, hw, hl, .forward (Nat.lt_succ_self _) (path.mono (Nat.le_succ _)) HT⟩

private theorem constant_assignments (H : StrongBounded env U n Γ a b T) :
    ConstantAssignment env U n Γ a T ∧ ConstantAssignment env U n Γ b T := by
  induction H with
  | bvar | sortDF | appDF | projDF | lamDF | forallEDF =>
    constructor <;> intro c ls E <;> cases E
  | constDF hc hw hw' hl he hu ht0 ht =>
    constructor
    · intro c ls E
      cases E
      exact ⟨_, hc, hw, hl, .refl⟩
    · intro c ls E
      cases E
      exact ⟨_, hc, hw', he.length_eq.symm.trans hl,
        .backward (Nat.lt_succ_self _) .refl ht⟩
  | symm _ ih => exact ⟨ih.2.mono (Nat.le_succ _), ih.1.mono (Nat.le_succ _)⟩
  | trans _ _ ih₁ ih₂ => exact ⟨ih₁.1.mono (Nat.le_succ _), ih₂.2.mono (Nat.le_succ _)⟩
  | defeqDF hu HT H ihT ih => exact ⟨ih.1.convert HT, ih.2.convert HT⟩
  | beta h1 h2 h3 h4 h5 h6 h7 h8 _ _ _ _ _ ih8 =>
    exact ⟨(fun c ls E => by cases E), ih8.1.mono (Nat.le_succ _)⟩
  | eta h1 h2 h3 h4 h5 h6 h7 h8 _ _ _ ih6 _ _ =>
    exact ⟨(fun c ls E => by cases E), ih6.1.mono (Nat.le_succ _)⟩
  | proofIrrel h1 h2 h3 _ ih2 ih3 =>
    exact ⟨ih2.1.mono (Nat.le_succ _), ih3.1.mono (Nat.le_succ _)⟩
  | extra h1 h2 h3 h4 h5 h6 h7 h8 h9 _ _ _ ih8 ih9 =>
    exact ⟨ih8.1.mono (Nat.le_succ _), ih9.1.mono (Nat.le_succ _)⟩
  | pat hp hm he hred hr hall ihe ihred ihall =>
    exact ⟨ihe.1.mono (Nat.le_succ _), ihred.1.mono (Nat.le_succ _)⟩
  | projIota hi ht hg hf iht ihf =>
    exact ⟨iht.1.mono (Nat.le_succ _), ihf.1.mono (Nat.le_succ _)⟩
  | structEta hi hp hx hm hc ihm ihc =>
    exact ⟨ihc.1.mono (Nat.le_succ _), ihm.1.mono (Nat.le_succ _)⟩
  | unitLike hi hp hx hz hm hn ihm ihn =>
    exact ⟨ihm.1.mono (Nat.le_succ _), ihn.1.mono (Nat.le_succ _)⟩
  | raise hlt H ih => exact ⟨ih.1.mono (Nat.le_of_lt hlt), ih.2.mono (Nat.le_of_lt hlt)⟩

/-- Either constant endpoint has its declared native type connected to the
selected carrier by original strictly smaller type children. This includes
right endpoints of universe-congruent constDF and every other strong rule. -/
theorem StrongBounded.constant_assignment_path
    (H : StrongBounded env U n Γ a b T)
    (endpoint : a = .const c ls ∨ b = .const c ls) :
    ∃ ci, env.constants c = some ci ∧ (∀ l ∈ ls, l.WF U) ∧ ls.length = ci.uvars ∧
      BoundedTypePath env U n Γ (ci.type.instL ls) T :=
  endpoint.elim (fun E => (constant_assignments H).1 c ls E)
    (fun E => (constant_assignments H).2 c ls E)

open Params ProofShape PureObservation
variable [Params] {D : Definitions}

/-- Forgetting orientations gives ordinary equality, not semantic transport. -/
theorem BoundedTypePath.defeq (H : BoundedTypePath env univs n Γ A B)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.IsType univs Γ A) :
    env.IsDefEqU univs Γ A B := by
  induction H with
  | refl => obtain ⟨u, hA⟩ := hA; exact ⟨_, hA⟩
  | forward hlt H HE ih => exact (ih hA).trans henv hΓ HE.strong.defeq.toU
  | backward hlt H HE ih => exact (ih hA).trans henv hΓ HE.strong.defeq.toU.symm

/-- Both semantic directions are selected from the same original child.
Intermediate assignments use ordinary path equality; no reconstructed strong
symmetry or transitivity proof is passed to the lower-rank handler. -/
theorem BoundedTypePath.ground_type_equiv
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (H : BoundedTypePath env univs bound Γ A B)
    (edge : ∀ {k X Y v}, k < bound → StrongBounded env univs k Γ X Y (.sort v) →
      PiInertGroundTypeEquiv D Γ X Y) : PiInertGroundTypeEquiv D Γ A B := by
  induction H with
  | refl => exact .refl
  | forward hlt path HE ih =>
    have HP := (path.defeq hΓ ⟨u, hA⟩).of_l henv hΓ hA
    have HQ := HE.strong.defeq.toU.of_l henv hΓ HP.hasType.2
    exact .trans hΓ HP HQ (ih hA) (edge hlt HE)
  | backward hlt path HE ih =>
    have HP := (path.defeq hΓ ⟨u, hA⟩).of_l henv hΓ hA
    have HQ := HE.strong.defeq.toU.symm.of_l henv hΓ HP.hasType.2
    exact .trans hΓ HP HQ (ih hA) (edge hlt HE).symm

/-- A native unit path interprets any pair assigned its endpoint type, not
only the constant or variable that supplied the path. This is what allows a
middle constructor to resolve transitivity without erased-history composition. -/
theorem BoundedTypePath.unit_ground_interpretation
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hf : info.numFields = 0)
    (hD : ∀ levels rhs, ¬ D.unfolds family levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hS : env.HasType univs Γ (.const family ls) (.sort u))
    (ha : env.HasType univs Γ a T) (hb : env.HasType univs Γ b T)
    (path : BoundedTypePath env univs bound Γ (.const family ls) T)
    (edge : ∀ {k X Y v}, k < bound → StrongBounded env univs k Γ X Y (.sort v) →
      PiInertGroundTypeEquiv D Γ X Y) :
    PiInertGuardedPairInterpretation D (proofEraseCtx Γ) []
      (proofErase Γ a) (proofErase Γ b) (proofErase Γ T) (proofErase Γ T)
      (.plain .ground) (.plain .ground) := by
  have HE := (path.defeq hΓ ⟨u, hS⟩).of_l henv hΓ hS
  have ES : proofErase Γ (.const family ls) = .const family ls :=
    if_neg (not_isProof_of_sort hΓ hS)
  have native := PiInertGuardedPairInterpretation.unit_ground hi hp hx hf hD
    (ES ▸ TypedAt.of_typed hΓ (HE.symm.defeq ha))
    (ES ▸ TypedAt.of_typed hΓ (HE.symm.defeq hb))
  have transport : PiInertTreeTransport D (proofEraseCtx Γ)
      (.plain .ground) (proofErase Γ (.const family ls)) (.plain .ground) (proofErase Γ T) :=
    (path.ground_type_equiv hΓ hS edge).forward
  rw [ES] at transport
  exact native.convert_trees heq hs transport transport
    (.of_typed hΓ ha) (.of_typed hΓ hb)

/-- A registered nullary empty constructor has the literal family as its
native declared type. Recover that fact from the actual declaration and then
read its original conversion path; no native-shape or exposure premise is
added. The selected carrier may be an arbitrary opaque alias. -/
theorem StrongBounded.unit_constructor_origin
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hf : info.numFields = 0)
    (hΓ : OnCtx Γ (env.IsType univs))
    (H : StrongBounded env univs bound Γ x y T)
    (endpoint : x = .const info.ctorName ls ∨ y = .const info.ctorName ls) :
    ∃ u, env.HasType univs Γ (.const family ls) (.sort u) ∧
      BoundedTypePath env univs bound Γ (.const family ls) T := by
  obtain ⟨ci, hc, hw, hl, path⟩ := H.constant_assignment_path endpoint
  rw [henv.ordered.projectionConstructor hi] at hc
  cases Option.some.inj hc
  have hm : env.HasType univs Γ (.const info.ctorName ls) T :=
    endpoint.elim (fun E => E ▸ H.strong.defeq.hasType.1)
      (fun E => E ▸ H.strong.defeq.hasType.2)
  have HW := structure_constructor_native_walk hΓ hi hx (args := [])
    (by simp only [List.length_nil, hp, hf, Nat.zero_add]) hm
  simp only [List.take_nil, VExpr.mkApps, List.foldl_nil] at HW
  have empty {X Y : VExpr} (H : InstForallsC env univs Γ X [] Y) : X = Y := by
    cases H
    rfl
  have ET := empty HW
  have hnative := HasType.const (Γ := Γ) (henv.ordered.projectionConstructor hi) hw hl
  change env.HasType univs Γ (.const info.ctorName ls) (info.ctorType.instL ls) at hnative
  rw [ET] at hnative
  obtain ⟨u, hS⟩ := hnative.isType henv hΓ
  exact ⟨u, hS, by simpa only [ET] using path⟩

/-- A constructor endpoint of one original strong derivation supplies the
selected-type provenance needed to interpret any two terms at that carrier.
Only original lower-rank type children need semantic interpretation; neither
term-comparison history is consumed or composed. -/
theorem StrongBounded.unit_constructor_assigned_pair
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hf : info.numFields = 0)
    (hD : ∀ levels rhs, ¬ D.unfolds family levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (H : StrongBounded env univs bound Γ x y T)
    (endpoint : x = .const info.ctorName ls ∨ y = .const info.ctorName ls)
    (ha : env.HasType univs Γ a T) (hb : env.HasType univs Γ b T)
    (edge : ∀ {k X Y v}, k < bound → StrongBounded env univs k Γ X Y (.sort v) →
      PiInertGroundTypeEquiv D Γ X Y) :
    PiInertGuardedPairInterpretation D (proofEraseCtx Γ) []
      (proofErase Γ a) (proofErase Γ b) (proofErase Γ T) (proofErase Γ T)
      (.plain .ground) (.plain .ground) := by
  obtain ⟨u, hS, path⟩ := H.unit_constructor_origin hi hp hx hf hΓ endpoint
  exact path.unit_ground_interpretation heq hs hi hp hx hf hD hΓ hS ha hb edge

/-- The original transitivity rule through a native unit constructor is
interpreted at its possibly opaque assigned carrier. Outer endpoints are
unrestricted. Each semantic handler call has rank j<k below one rank-k child,
so even a handler only below that child suffices. General transitivity and
construction of the lower type transports remain open. -/
theorem StrongBounded.trans_unit_constructor_ground_of_lower
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hf : info.numFields = 0)
    (hD : ∀ levels rhs, ¬ D.unfolds family levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (left : StrongBounded env univs k Γ a (.const info.ctorName ls) T)
    (right : StrongBounded env univs k Γ (.const info.ctorName ls) b T)
    (edge : ∀ {j X Y v}, j < k → StrongBounded env univs j Γ X Y (.sort v) →
      PiInertGroundTypeEquiv D Γ X Y) :
    PiInertGuardedPairInterpretation D (proofEraseCtx Γ) []
      (proofErase Γ a) (proofErase Γ b) (proofErase Γ T) (proofErase Γ T)
      (.plain .ground) (.plain .ground) :=
  left.unit_constructor_assigned_pair heq hs hi hp hx hf hD hΓ (.inr rfl)
    left.strong.defeq.hasType.1 right.strong.defeq.hasType.2 edge

/-- Constructor-pivot transitivity also supplies substitution-indexed finite
histories, suitable for Eq-rec index consumers. Stages are chosen after each
typed substitution; no uniform bound or diagonal image hypothesis is needed. -/
theorem StrongBounded.trans_unit_constructor_finite_history_of_lower
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hf : info.numFields = 0)
    (hD : ∀ levels rhs, ¬ D.unfolds family levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (left : StrongBounded env univs k Γ a (.const info.ctorName ls) T)
    (right : StrongBounded env univs k Γ (.const info.ctorName ls) b T)
    (edge : ∀ {j X Y v}, j < k → StrongBounded env univs j Γ X Y (.sort v) →
      PiInertGroundTypeEquiv D Γ X Y) :
    PiInertFiniteHistory D (proofEraseCtx Γ) (proofErase Γ T)
      (proofErase Γ a) (proofErase Γ b) := by
  have result := left.trans_unit_constructor_ground_of_lower heq hs hi hp hx hf hD hΓ right edge
  intro Λ σ W
  exact result.empty_finite_history W

end Lean4Lean.VEnv.Strengthening
