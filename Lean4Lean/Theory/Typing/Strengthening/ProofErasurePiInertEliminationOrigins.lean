import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertConstantOrigins

/-! # Original formation results for application and projection endpoints

An application retains its own argument's result instance and the original
comparison to the selected result. A projection retains its recorded source
major and field type. Both survive every strong constructor through paths
whose type children remain strictly below the original bound.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr

/-- The function of an application comes from an original endpoint child,
or from beta's original body child. The beta source does not contain a
smaller function-typing child, so that distinction is retained explicitly. -/
inductive BoundedApplicationFunction (env : VEnv) (U k : Nat) (Γ : List VExpr) :
    VExpr → VExpr → VExpr → Prop where
  | endpoint : BoundedEndpoint env U k Γ f (.forallE A B) →
      BoundedApplicationFunction env U k Γ f A B
  | lambda : StrongBounded env U k (A::Γ) body body B →
      BoundedApplicationFunction env U k Γ (.lam A body) A B

/-- Formation of an application at its own argument's result type, followed
by original type-conversion edges to the selected carrier. Every recorded
premise is strictly below bound, including result formation. -/
inductive BoundedApplicationOrigin (env : VEnv) (U bound : Nat)
    (Γ : List VExpr) (f x T : VExpr) : Prop where
  | intro (hlt : k < bound) (hu : u.WF U) (hv : v.WF U)
      (hA : StrongBounded env U k Γ A A (.sort u))
      (hB : StrongBounded env U k (A::Γ) B B (.sort v))
      (hF : BoundedApplicationFunction env U k Γ f A B)
      (hX : BoundedEndpoint env U k Γ x A)
      (hR : BoundedEndpoint env U k Γ (B.inst x) (.sort v))
      (path : BoundedTypePath env U bound Γ (B.inst x) T) :
      BoundedApplicationOrigin env U bound Γ f x T

/-- Raising the enclosing bound preserves every application premise rank. -/
theorem BoundedApplicationOrigin.mono
    (H : BoundedApplicationOrigin env U n Γ f x T) (hle : n ≤ m) :
    BoundedApplicationOrigin env U m Γ f x T := by
  cases H with
  | intro hlt hu hv hA hB hF hX hR path =>
    exact .intro (Nat.lt_of_lt_of_le hlt hle) hu hv hA hB hF hX hR (path.mono hle)

/-- An original conversion child extends the path at its original rank. -/
theorem BoundedApplicationOrigin.convert
    (H : BoundedApplicationOrigin env U n Γ f x T)
    (HT : StrongBounded env U n Γ T V (.sort u)) :
    BoundedApplicationOrigin env U (n+1) Γ f x V := by
  cases H with
  | intro hlt hu hv hA hB hF hX hR path =>
    exact .intro (Nat.lt_trans hlt (Nat.lt_succ_self _)) hu hv hA hB hF hX hR
      (.forward (Nat.lt_succ_self _) (path.mono (Nat.le_succ _)) HT)

private def ApplicationAssignment (env : VEnv) (U n : Nat)
    (Γ : List VExpr) (e T : VExpr) : Prop :=
  ∀ f x, e = .app f x → BoundedApplicationOrigin env U n Γ f x T

private theorem ApplicationAssignment.mono
    (H : ApplicationAssignment env U n Γ e T) (hle : n ≤ m) :
    ApplicationAssignment env U m Γ e T := fun f x E => (H f x E).mono hle

private theorem ApplicationAssignment.convert
    (H : ApplicationAssignment env U n Γ e T)
    (HT : StrongBounded env U n Γ T V (.sort u)) :
    ApplicationAssignment env U (n+1) Γ e V := fun f x E => (H f x E).convert HT

private theorem application_assignments (H : StrongBounded env U n Γ a b T) :
    ApplicationAssignment env U n Γ a T ∧ ApplicationAssignment env U n Γ b T := by
  induction H with
  | bvar | sortDF | constDF | projDF | lamDF | forallEDF =>
    constructor <;> intro f x E <;> cases E
  | appDF hu hv hA hB hF hX hR ihA ihB ihF ihX ihR =>
    constructor
    · intro f x E
      cases E
      exact .intro (Nat.lt_succ_self _) hu hv hA hB (.endpoint (.left hF))
        (.left hX) (.left hR) .refl
    · intro f x E
      cases E
      exact .intro (Nat.lt_succ_self _) hu hv hA hB (.endpoint (.right hF))
        (.right hX) (.right hR) (.backward (Nat.lt_succ_self _) .refl hR)
  | beta hu hv hA hB hbody hX hR hred ihA ihB ihbody ihX ihR ihred =>
    constructor
    · intro f x E
      cases E
      exact .intro (Nat.lt_succ_self _) hu hv hA hB (.lambda hbody)
        (.left hX) (.left hR) .refl
    · exact ihred.1.mono (Nat.le_succ _)
  | symm _ ih => exact ⟨ih.2.mono (Nat.le_succ _), ih.1.mono (Nat.le_succ _)⟩
  | trans _ _ ih₁ ih₂ => exact ⟨ih₁.1.mono (Nat.le_succ _), ih₂.2.mono (Nat.le_succ _)⟩
  | defeqDF hu HT H ihT ih => exact ⟨ih.1.convert HT, ih.2.convert HT⟩
  | eta h1 h2 h3 h4 h5 h6 h7 h8 _ _ _ ih6 _ _ =>
    exact ⟨(fun f x E => by cases E), ih6.1.mono (Nat.le_succ _)⟩
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

/-- Every application endpoint has an original formation frame and selected
type path. The right appDF endpoint retains B[x'] and reverses the original
B[x]=B[x'] child. Beta sources retain their body premise separately. -/
theorem StrongBounded.application_origin (H : StrongBounded env U n Γ a b T)
    (endpoint : a = .app f x ∨ b = .app f x) :
    BoundedApplicationOrigin env U n Γ f x T :=
  endpoint.elim (fun E => (application_assignments H).1 f x E)
    (fun E => (application_assignments H).2 f x E)

/-- Projection formation retains the actual source major used by fieldType,
and the original comparison to the endpoint major. The source is not silently
replaced by that endpoint inside the dependent field type. -/
inductive BoundedProjectionOrigin (env : VEnv) (U bound : Nat)
    (Γ : List VExpr) (family : Name) (index : Nat) (major T : VExpr) : Prop where
  | intro (hlt : k < bound)
      (hi : env.projections family info)
      (hw : ∀ l ∈ levels, l.WF U) (hl : levels.length = info.uvars)
      (hp : params.length = info.nparams) (hx : indexArgs.length = info.nindices)
      (hfield : info.fieldType family levels params index source = some F)
      (hv : v.WF U) (hF : StrongBounded env U k Γ F F (.sort v))
      (hM : StrongBounded env U k Γ source major
        (VExpr.mkApps (.const family levels) (params ++ indexArgs)))
      (hclosed : info.ctorType.Closed)
      (hguard : (info.resultLevel.inst levels).IsNeverZero ∨ v ≈ .zero)
      (path : BoundedTypePath env U bound Γ F T) :
      BoundedProjectionOrigin env U bound Γ family index major T

/-- Raising a projection's bound leaves its source-major child unchanged. -/
theorem BoundedProjectionOrigin.mono
    (H : BoundedProjectionOrigin env U n Γ family index major T) (hle : n ≤ m) :
    BoundedProjectionOrigin env U m Γ family index major T := by
  cases H with
  | intro hlt hi hw hl hp hx hfield hv hF hM hclosed hguard path =>
    exact .intro (Nat.lt_of_lt_of_le hlt hle) hi hw hl hp hx hfield hv hF hM hclosed hguard
      (path.mono hle)

/-- Selected projection conversions append only their original type child. -/
theorem BoundedProjectionOrigin.convert
    (H : BoundedProjectionOrigin env U n Γ family index major T)
    (HT : StrongBounded env U n Γ T V (.sort u)) :
    BoundedProjectionOrigin env U (n+1) Γ family index major V := by
  cases H with
  | intro hlt hi hw hl hp hx hfield hv hF hM hclosed hguard path =>
    exact .intro (Nat.lt_trans hlt (Nat.lt_succ_self _)) hi hw hl hp hx hfield hv hF hM hclosed hguard
      (.forward (Nat.lt_succ_self _) (path.mono (Nat.le_succ _)) HT)

private def ProjectionAssignment (env : VEnv) (U n : Nat)
    (Γ : List VExpr) (e T : VExpr) : Prop :=
  ∀ family index major, e = .proj family index major →
    BoundedProjectionOrigin env U n Γ family index major T

private theorem ProjectionAssignment.mono
    (H : ProjectionAssignment env U n Γ e T) (hle : n ≤ m) :
    ProjectionAssignment env U m Γ e T := fun family index major E => (H family index major E).mono hle

private theorem ProjectionAssignment.convert
    (H : ProjectionAssignment env U n Γ e T)
    (HT : StrongBounded env U n Γ T V (.sort u)) :
    ProjectionAssignment env U (n+1) Γ e V :=
  fun family index major E => (H family index major E).convert HT

private theorem projection_assignments (H : StrongBounded env U n Γ a b T) :
    ProjectionAssignment env U n Γ a T ∧ ProjectionAssignment env U n Γ b T := by
  induction H with
  | bvar | sortDF | constDF | appDF | lamDF | forallEDF =>
    constructor <;> intro family index major E <;> cases E
  | projDF hi hw hl hp hx hfield hv hF hL hR hclosed hguard ihF ihL ihR =>
    constructor
    · intro family index major E
      cases E
      exact .intro (Nat.lt_succ_self _) hi hw hl hp hx hfield hv hF hL hclosed hguard .refl
    · intro family index major E
      cases E
      exact .intro (Nat.lt_succ_self _) hi hw hl hp hx hfield hv hF hR hclosed hguard .refl
  | symm _ ih => exact ⟨ih.2.mono (Nat.le_succ _), ih.1.mono (Nat.le_succ _)⟩
  | trans _ _ ih₁ ih₂ => exact ⟨ih₁.1.mono (Nat.le_succ _), ih₂.2.mono (Nat.le_succ _)⟩
  | defeqDF hu HT H ihT ih => exact ⟨ih.1.convert HT, ih.2.convert HT⟩
  | beta h1 h2 h3 h4 h5 h6 h7 h8 _ _ _ _ _ ih8 =>
    exact ⟨(fun family index major E => by cases E), ih8.1.mono (Nat.le_succ _)⟩
  | eta h1 h2 h3 h4 h5 h6 h7 h8 _ _ _ ih6 _ _ =>
    exact ⟨(fun family index major E => by cases E), ih6.1.mono (Nat.le_succ _)⟩
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

/-- Every projection endpoint retains its original field-formation frame and
selected-type conversion path, including projection-iota's source typing child.
Interpreting the source-major comparison remains a separate semantic task. -/
theorem StrongBounded.projection_origin (H : StrongBounded env U n Γ a b T)
    (endpoint : a = .proj family index major ∨ b = .proj family index major) :
    BoundedProjectionOrigin env U n Γ family index major T :=
  endpoint.elim (fun E => (projection_assignments H).1 family index major E)
    (fun E => (projection_assignments H).2 family index major E)

open Params ProofShape PureObservation
variable [Params] {D : Definitions}

/-- Forgetting an original endpoint supplies ordinary typing without making
or assigning a rank to a reflexive strong derivation. -/
theorem BoundedEndpoint.hasType (H : BoundedEndpoint env univs k Γ e T) :
    env.HasType univs Γ e T := by
  obtain ⟨a, b, HE, side⟩ := H
  exact side.elim (fun E => E.symm ▸ HE.strong.defeq.hasType.1)
    (fun E => E.symm ▸ HE.strong.defeq.hasType.2)

/-- Beta's literal function uses ordinary lambda typing of its original body
child. This does not claim that the function itself has a smaller strong rank. -/
theorem BoundedApplicationFunction.hasType
    (H : BoundedApplicationFunction env univs k Γ f A B)
    (hA : env.HasType univs Γ A (.sort u)) :
    env.HasType univs Γ f (.forallE A B) := by
  cases H with
  | endpoint HF => exact HF.hasType
  | lambda HB => exact HasType.lam hA HB.strong.defeq.hasType.1

/-- The exact application formation result is connected to the selected
carrier by semantic transports at original lower ranks. Its actual function,
argument and result typing remain available for recursive interface action.
This does not interpret the function or argument comparison itself. -/
theorem BoundedApplicationOrigin.result_transport
    (hΓ : OnCtx Γ (env.IsType univs))
    (H : BoundedApplicationOrigin env univs bound Γ f x T)
    (edge : ∀ {k X Y v}, k < bound → StrongBounded env univs k Γ X Y (.sort v) →
      PiInertGroundTypeEquiv D Γ X Y) :
    ∃ A B v, env.HasType univs Γ f (.forallE A B) ∧ env.HasType univs Γ x A ∧
      env.HasType univs Γ (B.inst x) (.sort v) ∧
      PiInertGroundTypeEquiv D Γ (B.inst x) T := by
  cases H with
  | intro hlt hu hv hA hB hF hX hR path =>
    exact ⟨_, _, _, hF.hasType hA.strong.defeq.hasType.1, hX.hasType, hR.hasType,
      path.ground_type_equiv hΓ hR.hasType edge⟩

/-- A projection's recorded field type, with its original source major, is
connected to the selected carrier using only original lower type children.
The endpoint major is typed at that field type by the original comparison;
no equality of fieldType at different majors is assumed. -/
theorem BoundedProjectionOrigin.result_transport
    (hΓ : OnCtx Γ (env.IsType univs))
    (H : BoundedProjectionOrigin env univs bound Γ family index major T)
    (edge : ∀ {k X Y v}, k < bound → StrongBounded env univs k Γ X Y (.sort v) →
      PiInertGroundTypeEquiv D Γ X Y) :
    ∃ F v, env.HasType univs Γ (.proj family index major) F ∧
      env.HasType univs Γ F (.sort v) ∧ PiInertGroundTypeEquiv D Γ F T := by
  cases H with
  | intro hlt hi hw hl hp hx hfield hv hF hM hclosed hguard path =>
    have hproj := IsDefEq.projDF hi hw hl hp hx hfield hF.strong.defeq.hasType.1
      hM.strong.defeq hM.strong.defeq hclosed hguard
    exact ⟨_, _, hproj.hasType.1, hF.strong.defeq.hasType.1,
      path.ground_type_equiv hΓ hF.strong.defeq.hasType.1 edge⟩

/-- Application endpoints of an arbitrary original strong comparison recover
their own argument's formation result and transport to the selected type.
Outer transitivity and conversion nodes do not require new semantic cases
for that path. Actual application interpretation remains to be supplied. -/
theorem StrongBounded.application_result_transport_of_lower
    (hΓ : OnCtx Γ (env.IsType univs))
    (H : StrongBounded env univs bound Γ a b T)
    (endpoint : a = .app f x ∨ b = .app f x)
    (edge : ∀ {k X Y v}, k < bound → StrongBounded env univs k Γ X Y (.sort v) →
      PiInertGroundTypeEquiv D Γ X Y) :
    ∃ A B v, env.HasType univs Γ f (.forallE A B) ∧ env.HasType univs Γ x A ∧
      env.HasType univs Γ (B.inst x) (.sort v) ∧
      PiInertGroundTypeEquiv D Γ (B.inst x) T :=
  (H.application_origin endpoint).result_transport hΓ edge

/-- Projection endpoints recover a recorded field result and its selected
transport from original type children, keeping the field's source-major
comparison inside the origin frame. General projection semantics is open. -/
theorem StrongBounded.projection_result_transport_of_lower
    (hΓ : OnCtx Γ (env.IsType univs))
    (H : StrongBounded env univs bound Γ a b T)
    (endpoint : a = .proj family index major ∨ b = .proj family index major)
    (edge : ∀ {k X Y v}, k < bound → StrongBounded env univs k Γ X Y (.sort v) →
      PiInertGroundTypeEquiv D Γ X Y) :
    ∃ F v, env.HasType univs Γ (.proj family index major) F ∧
      env.HasType univs Γ F (.sort v) ∧ PiInertGroundTypeEquiv D Γ F T :=
  (H.projection_origin endpoint).result_transport hΓ edge

end Lean4Lean.VEnv.Strengthening
