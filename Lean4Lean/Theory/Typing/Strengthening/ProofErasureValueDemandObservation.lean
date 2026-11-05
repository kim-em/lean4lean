import Lean4Lean.Theory.Typing.Strengthening.ProofErasureValueDemandFrames
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedValueChain

/-! # Finite rigid-head observations with retained value demands

Value keys name arguments in the fixed outer context. Their witnesses are
scoped computation chains in the current context, so beta may substitute opaque
or function-valued arguments without preserving individual forward guards.
These are observer constructors and transport laws, not a readout theorem.
-/
namespace Lean4Lean.VEnv.Strengthening.ValueDemandProfile
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open PiOriginObservation (FixedTail)
open private erase_lam_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
open private subst_bvar_liftN from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRenaming

/-- A finite demand reads a rigid spine, remembers a data value, or calls a
function after supplying finitely many demands on its argument. -/
inductive Key where
  | value (origin : ProofShape)
  | head (arguments : List ProofShape)
  | app (keys : List Key) (result : Key)

/-- A value demand observes opaque nonproof data; a head demand observes a type. -/
inductive Demand : Profile → Key → Prop where
  | value : Demand .data (.value a)
  | head : Demand .sort (.head args)
  | fn : (∀ key ∈ keys, Demand A key) → Demand B o → Demand (.arrow A B) (.app keys o)

/-- Every demand is retained by erasure. -/
theorem Demand.visible (H : Demand p o) : p.Visible := by
  induction H with
  | value => exact .data
  | head => exact .sort
  | fn _ _ _ ih => exact .arrow ih

/-- Proof slots need no value observation; data slots demand their original value. -/
def slotProfile : Bool → Profile | true => .proof | false => .data

def slotKeys (s : Bool × ProofShape) : List Key := if s.1 then [] else [.value s.2]

def argumentProfile : List (Bool × ProofShape) → Profile → Profile
  | [], p => p
  | s :: slots, p => .arrow (slotProfile s.1) (argumentProfile slots p)

def argumentKey : List (Bool × ProofShape) → Key → Key
  | [], o => o
  | s :: slots, o => .app (slotKeys s) (argumentKey slots o)

/-- A constant's saturated demand retains every slot, including proof markers. -/
def spineKey (slots : List (Bool × ProofShape)) : Key :=
  argumentKey slots (.head (slots.map Prod.snd))

/-- Every slot demand follows its declared proof/data profile. -/
theorem Demand.arguments (H : Demand p o) :
    Demand (argumentProfile slots p) (argumentKey slots o) := by
  induction slots with
  | nil => exact H
  | cons s slots ih =>
    apply Demand.fn ?_ ih
    rcases s with ⟨b, a⟩
    cases b <;> simp only [slotKeys, slotProfile, Bool.false_eq_true, ↓reduceIte, List.mem_singleton] <;> intro key hk
    · cases hk; exact .value
    · cases hk

/-- Control assumptions retain the assigned profile and the demanded key. -/
def Sets := Nat → Profile → Key → Prop

def Sets.cons (A : Profile) (keys : List Key) (S : Sets) : Sets
  | 0, t, o => t = A ∧ o ∈ keys
  | i+1, t, o => S i t o

variable [Params] {D : PureObservation.Definitions}

/-- The finite observer has explicit value histories, and separate control
application/lambda nodes. Proof slots at a constant carry literal proof labels.
The value-step constructor transports arbitrary computation chains, not just
forward paths. Computation preservation and readout are proved in subsequent modules. -/
inductive Obs (D : PureObservation.Definitions) (c : Name) :
    Nat → List ProofShape → Sets → ProofShape → Profile → Key → Prop where
  | const : Typing Δ (.const c ls) (argumentProfile slots .sort) →
      (∀ s ∈ slots, s.1 = true → s.2 = .proof) →
      Obs D c n Δ S (.const c ls) (argumentProfile slots .sort) (spineKey slots)
  | var : Typing Δ (.bvar i) t → Demand t o → S i t o → Obs D c n Δ S (.bvar i) t o
  | value : Typing Δ e .data → ScopedValueChain D Δ (a.liftN n) e →
      Obs D c n Δ S e .data (.value a)
  | value_step : Typing Δ e' .data → Obs D c n Δ S e .data (.value a) →
      ScopedValueChain D Δ e e' → Obs D c n Δ S e' .data (.value a)
  | app : Typing Δ (.app f a) B → Obs D c n Δ S f (.arrow A B) (.app keys o) →
      (∀ key ∈ keys, Obs D c n Δ S a A key) → Obs D c n Δ S (.app f a) B o
  | lam : Typing Δ (.lam A b) (.arrow p q) → (∀ key ∈ keys, Demand p key) →
      Obs D c (n+1) (A :: Δ) (Sets.cons p keys S) b q o →
      Obs D c n Δ S (.lam A b) (.arrow p q) (.app keys o)

/-- Every observed node retains an actual typing and its dependent profile. -/
theorem Obs.typing (H : Obs D c n Δ S e t o) : Typing Δ e t := by cases H <;> assumption

/-- Every observed key agrees with its profile. -/
theorem Obs.demand (H : Obs D c n Δ S e t o) : Demand t o := by
  induction H with
  | const => exact Demand.arguments .head
  | var _ HD => exact HD
  | value | value_step => exact .value
  | app _ _ _ ihf _ => cases ihf; assumption
  | lam _ HK _ ih => exact .fn HK ih

/-- Typed renaming transports histories while fixing their original outer labels. -/
theorem Obs.rename
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (H : Obs D c n Δ S e t o) (W : ContextSubstitution Δ Δ' σ)
    (HT : FixedTail n m σ)
    (hσ : ∀ i t key, S i t key → ∃ j, σ i = .bvar j ∧ T j t key) :
    Obs D c m Δ' T (e.subst σ) t o := by
  induction H generalizing Δ' T σ m with
  | const H HP => exact .const (H.subst W) HP
  | var H HD h =>
    obtain ⟨j, E, hj⟩ := hσ _ _ _ h
    simpa only [ProofShape.subst, E] using
      (Obs.var (by simpa only [ProofShape.subst, E] using H.subst W) HD hj : Obs D c m Δ' T (.bvar j) _ _)
  | value H HC =>
    have HC' := HC.subst heq hs W
    rw [HT.payload] at HC'
    exact .value (H.subst W) HC'
  | value_step H _ HC ih => exact .value_step (H.subst W) (ih W HT hσ) (HC.subst heq hs W)
  | app H _ _ ihf iha => exact .app (H.subst W) (ihf W HT hσ) (fun key hk => iha key hk W HT hσ)
  | @lam Δ A b p q keys n S o H HK _ ih =>
    apply Obs.lam (H.subst W) HK
    apply ih W.cons HT.lift
    intro i t key hi
    cases i with
    | zero => exact ⟨0, rfl, hi⟩
    | succ i =>
      obtain ⟨j, E, hj⟩ := hσ i t key hi
      exact ⟨j+1, by simp [ProofShape.Subst.lift, E, ProofShape.liftN, liftVar, Nat.add_comm], hj⟩

/-- Weakening introduces a temporary control binder without changing value labels. -/
theorem Obs.lift
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (H : Obs D c n Δ S e t o) (SD : DomainSort Δ A u) :
    Obs D c (n+1) (A :: Δ) (Sets.cons p keys S) (e.liftN 1) t o := by
  have HT : FixedTail n (n+1) (fun i => .bvar (i+1)) := by intro i; simp [Nat.add_right_comm]
  have R := H.rename heq hs (H.typing.weak_interpretation SD) HT
    (T := Sets.cons p keys S) (fun i t key hi => ⟨i+1, rfl, hi⟩)
  have E : e.subst (fun i => .bvar (i+1)) = e.liftN 1 := by
    simpa only [liftVar, Nat.not_lt_zero, ↓reduceIte, Nat.add_comm] using
      (subst_bvar_liftN (n := 1) (k := 0) e)
  exact E ▸ R

/-- Typed substitution replaces demanded controls by their observations.
Value chains substitute even when native guards of their forward edges do not. -/
theorem Obs.subst
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (H : Obs D c n Δ S e t o) (W : ContextSubstitution Δ Δ' σ)
    (HT : FixedTail n m σ)
    (hσ : ∀ i t key, S i t key → Demand t key → Obs D c m Δ' T (σ i) t key) :
    Obs D c m Δ' T (e.subst σ) t o := by
  induction H generalizing Δ' T σ m with
  | const H HP => exact .const (H.subst W) HP
  | var H HD h => exact hσ _ _ _ h HD
  | value H HC =>
    have HC' := HC.subst heq hs W
    rw [HT.payload] at HC'
    exact .value (H.subst W) HC'
  | value_step H _ HC ih => exact .value_step (H.subst W) (ih W HT hσ) (HC.subst heq hs W)
  | app H _ _ ihf iha => exact .app (H.subst W) (ihf W HT hσ) (fun key hk => iha key hk W HT hσ)
  | @lam Δ A b p q keys n S o H HK _ ih =>
    have H' := H.subst W
    obtain ⟨Γ, f, F, hΓ, EΓ, hf, HP, Ef⟩ := H
    obtain ⟨A₀, b₀, rfl, _, EA, _⟩ := erase_lam_inv Ef
    obtain ⟨⟨u, hA⟩, _⟩ := hf.lam_inv henv hΓ
    have SD : DomainSort Δ A u := ⟨Γ, A₀, hΓ, EΓ, hA, EA⟩
    apply Obs.lam H' HK
    apply ih W.cons HT.lift
    intro i t key hi HD
    cases i with
    | zero => obtain ⟨rfl, hk⟩ := hi; exact .var (H'.lam_parts.2 HD.visible) HD ⟨rfl, hk⟩
    | succ i => exact (hσ i t key hi HD).lift heq hs (W.sort SD)

end Lean4Lean.VEnv.Strengthening.ValueDemandProfile
