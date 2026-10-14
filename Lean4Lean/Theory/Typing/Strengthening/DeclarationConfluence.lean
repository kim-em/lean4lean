import Lean4Lean.Theory.Typing.Strengthening.DeclarationDeterminism
import Lean4Lean.Theory.Typing.Strengthening.DeclarationStep

/-! # Finite confluence of deterministic closed beta/delta computation

Parallel complete developments give confluence without normalization, source
typing or canonical Eq. Recursive closed definitions are allowed. This theorem
concerns beta/delta only; it does not assert confluence of the larger relation
with projection, pattern or singleton-prefix computation.
-/
namespace Lean4Lean.VEnv.Strengthening.PureObservation
open _root_.Lean4Lean _root_.Lean4Lean.VExpr

/-- Exact uniqueness of the raw value at a fixed constant instance. -/
def Definitions.Deterministic (D : Definitions) : Prop :=
  ∀ {c ls rhs rhs'}, D.unfolds c ls rhs → D.unfolds c ls rhs' → rhs = rhs'

/-- Parallel contraction develops only redexes already present in the source.
A delta step does not recursively develop its possibly recursive value. -/
inductive ComputePar (D : Definitions) : VExpr → VExpr → Prop where
  | bvar : ComputePar D (.bvar i) (.bvar i)
  | sort : ComputePar D (.sort u) (.sort u)
  | const : ComputePar D (.const c ls) (.const c ls)
  | delta : D.unfolds c ls rhs → ComputePar D (.const c ls) rhs
  | app : ComputePar D f f' → ComputePar D a a' → ComputePar D (.app f a) (.app f' a')
  | lam : ComputePar D A A' → ComputePar D b b' → ComputePar D (.lam A b) (.lam A' b')
  | forallE : ComputePar D A A' → ComputePar D B B' → ComputePar D (.forallE A B) (.forallE A' B')
  | proj : ComputePar D m m' → ComputePar D (.proj s i m) (.proj s i m')
  | beta : ComputePar D b b' → ComputePar D a a' → ComputePar D (.app (.lam A b) a) (b'.inst a')

variable {D : Definitions}

theorem ComputePar.refl (e : VExpr) : ComputePar D e e := by
  induction e with
  | bvar => exact .bvar
  | sort => exact .sort
  | const => exact .const
  | app _ _ ih1 ih2 => exact .app ih1 ih2
  | lam _ _ ih1 ih2 => exact .lam ih1 ih2
  | forallE _ _ ih1 ih2 => exact .forallE ih1 ih2
  | proj _ _ _ ih => exact .proj ih

/-- Closed delta bodies remain fixed by every binder lift. -/
theorem ComputePar.liftN (R : ComputePar D e e') (n k : Nat) :
    ComputePar D (e.liftN n k) (e'.liftN n k) := by
  induction R generalizing k with
  | bvar => exact .refl _
  | sort => exact .sort
  | const => exact .const
  | delta H => rw [(D.closed H).liftN_eq (Nat.zero_le k)]; exact .delta H
  | app _ _ ih1 ih2 => exact .app (ih1 k) (ih2 k)
  | lam _ _ ih1 ih2 => exact .lam (ih1 k) (ih2 (k+1))
  | forallE _ _ ih1 ih2 => exact .forallE (ih1 k) (ih2 (k+1))
  | proj _ ih => exact .proj (ih k)
  | beta _ _ ih1 ih2 => rw [liftN_inst_hi]; exact .beta (ih1 (k+1)) (ih2 k)

/-- Parallel computation is compatible with parallel substitution, including
substitution into a newly contracted beta redex. -/
theorem ComputePar.subst (R : ComputePar D e e')
    (H : ∀ i, ComputePar D (σ i) (τ i)) : ComputePar D (e.subst σ) (e'.subst τ) := by
  have hlift {σ τ : VExpr.Subst} (H : ∀ i, ComputePar D (σ i) (τ i)) :
      ∀ i, ComputePar D (σ.lift i) (τ.lift i) := by
    intro i
    cases i with
    | zero => exact .bvar
    | succ i => exact (H i).liftN 1 0
  induction R generalizing σ τ with
  | bvar => exact H _
  | sort => exact .sort
  | const => exact .const
  | delta h => rw [(D.closed h).subst_eq (by intro i hi; omega)]; exact .delta h
  | app _ _ ih1 ih2 => exact .app (ih1 H) (ih2 H)
  | lam _ _ ih1 ih2 => exact .lam (ih1 H) (ih2 (hlift H))
  | forallE _ _ ih1 ih2 => exact .forallE (ih1 H) (ih2 (hlift H))
  | proj _ ih => exact .proj (ih H)
  | beta _ _ ih1 ih2 => rw [subst_inst]; exact .beta (ih1 (hlift H)) (ih2 H)

theorem ComputePar.inst (R : ComputePar D e e') (H : ComputePar D a a') :
    ComputePar D (e.inst a) (e'.inst a') := by
  rw [inst_eq, inst_eq]
  apply R.subst
  intro i
  cases i with
  | zero => exact H
  | succ => exact .bvar

/-- Choose one value only for the redex at this constant; no recursive calls
inspect the chosen body. Determinism makes the choice immaterial. -/
private noncomputable def deltaDevelop (D : Definitions) (c : Name) (ls : List VLevel) : VExpr := by
  classical
  exact if h : ∃ rhs, D.unfolds c ls rhs then Classical.choose h else .const c ls

/-- Complete development of the source's beta and delta redexes. -/
private noncomputable def develop (D : Definitions) : VExpr → VExpr
  | .bvar i => .bvar i
  | .sort u => .sort u
  | .const c ls => deltaDevelop D c ls
  | .app (.lam _ b) a => (develop D b).inst (develop D a)
  | .app f a => .app (develop D f) (develop D a)
  | .lam A b => .lam (develop D A) (develop D b)
  | .forallE A B => .forallE (develop D A) (develop D B)
  | .proj s i m => .proj s i (develop D m)

private theorem deltaDevelop_self : ComputePar D (.const c ls) (deltaDevelop D c ls) := by
  unfold deltaDevelop
  split
  · exact .delta (Classical.choose_spec (by assumption))
  · exact .const

private theorem deltaDevelop_eq (hd : D.Deterministic) (H : D.unfolds c ls rhs) :
    deltaDevelop D c ls = rhs := by
  unfold deltaDevelop
  rw [dif_pos ⟨rhs, H⟩]
  exact hd (Classical.choose_spec _) H

/-- Every partial parallel development reaches the complete development in one
more parallel step. Newly exposed redexes need not be normalized. -/
private theorem ComputePar.triangle (hd : D.Deterministic) (R : ComputePar D e e') :
    ComputePar D e' (develop D e) := by
  induction R with
  | bvar => exact .bvar
  | sort => exact .sort
  | const => exact deltaDevelop_self
  | delta H => change ComputePar D _ (deltaDevelop D _ _); rw [deltaDevelop_eq hd H]; exact .refl _
  | @app f f' a a' Rf Ra ihf iha =>
    cases f with
    | lam A b =>
      cases Rf with
      | lam RA Rb =>
        cases ihf with
        | lam _ ihb => exact .beta ihb iha
    | bvar | sort | const | app | forallE | proj => exact .app ihf iha
  | lam _ _ ih1 ih2 => exact .lam ih1 ih2
  | forallE _ _ ih1 ih2 => exact .forallE ih1 ih2
  | proj _ ih => exact .proj ih
  | beta _ _ ih1 ih2 => exact ih1.inst ih2

/-- Exact parallel diamond for deterministic closed definitions. -/
theorem ComputePar.diamond (hd : D.Deterministic) (R1 : ComputePar D a b)
    (R2 : ComputePar D a c) : ∃ out, ComputePar D b out ∧ ComputePar D c out :=
  ⟨develop D a, R1.triangle hd, R2.triangle hd⟩

/-- Parallel contractions serialize into the existing computation relation. -/
theorem ComputePar.toCompute (R : ComputePar D e e') : Compute D e e' := by
  induction R with
  | bvar | sort | const => exact .refl
  | delta H => exact .delta H
  | app _ _ ih1 ih2 => exact .app ih1 ih2
  | lam _ _ ih1 ih2 => exact .lam ih1 ih2
  | forallE _ _ ih1 ih2 => exact .forallE ih1 ih2
  | proj _ ih => exact .proj ih
  | beta _ _ ih1 ih2 => exact (Compute.app (.lam .refl ih1) ih2).trans .beta

private theorem ComputeStep.toPar (R : ComputeStep D e e') : ComputePar D e e' := by
  induction R with
  | delta H => exact .delta H
  | beta => exact .beta (.refl _) (.refl _)
  | appL _ ih => exact .app ih (.refl _)
  | appR _ ih => exact .app (.refl _) ih
  | lamL _ ih => exact .lam ih (.refl _)
  | lamR _ ih => exact .lam (.refl _) ih
  | forallL _ ih => exact .forallE ih (.refl _)
  | forallR _ ih => exact .forallE (.refl _) ih
  | proj _ ih => exact .proj ih

private theorem Compute.toParallel (R : Compute D e e') : ReflTransGen (ComputePar D) e e' :=
  compute_induct_steps R .rfl (fun R H => H.tail R.toPar)

private theorem parallel_toCompute (R : ReflTransGen (ComputePar D) e e') : Compute D e e' := by
  induction R with
  | rfl => exact .refl
  | tail _ R ih => exact ih.trans R.toCompute

private theorem parallel_strip (hd : D.Deterministic) (R1 : ComputePar D a b)
    (R2 : ReflTransGen (ComputePar D) a c) :
    ∃ out, ReflTransGen (ComputePar D) b out ∧ ComputePar D c out := by
  induction R2 with
  | rfl => exact ⟨b, .rfl, R1⟩
  | tail _ R ih =>
    obtain ⟨out0, HB, HC⟩ := ih
    obtain ⟨out, R', HC'⟩ := R.diamond hd HC
    exact ⟨out, HB.tail HC', R'⟩

private theorem parallel_confluent (hd : D.Deterministic)
    (R1 : ReflTransGen (ComputePar D) a b) (R2 : ReflTransGen (ComputePar D) a c) :
    ∃ out, ReflTransGen (ComputePar D) b out ∧ ReflTransGen (ComputePar D) c out := by
  induction R1 with
  | rfl => exact ⟨c, R2, .rfl⟩
  | tail _ R ih =>
    obtain ⟨out0, HB, HC⟩ := ih
    obtain ⟨out, RB, RC⟩ := parallel_strip hd R HB
    exact ⟨out, RB, HC.tail RC⟩

/-- Arbitrary finite beta/delta computations from the same raw source join
exactly. The definition collection may contain recursive or looping bodies. -/
theorem Compute.confluent (hd : D.Deterministic) (R1 : Compute D a b)
    (R2 : Compute D a c) : ∃ out, Compute D b out ∧ Compute D c out := by
  obtain ⟨out, HB, HC⟩ := parallel_confluent hd R1.toParallel R2.toParallel
  exact ⟨out, parallel_toCompute HB, parallel_toCompute HC⟩

/-- Actual stored definitions satisfy the untyped confluence hypothesis. -/
theorem Definitions.ofEnv_deterministic (henv : env.WF) :
    (Definitions.ofEnv env U henv).Deterministic := fun H1 H2 =>
  Definitions.ofEnv_unique henv H1 H2

/-- Adding registry-selected closed structure programs preserves exact
beta/delta confluence, before adding projection and prefix computation. -/
theorem Compute.registeredStructure_confluent [Params]
    (R1 : Compute (RegisteredStructure.definitions
      (Definitions.ofEnv Params.env Params.univs Params.henv)) a b)
    (R2 : Compute (RegisteredStructure.definitions
      (Definitions.ofEnv Params.env Params.univs Params.henv)) a c) :
    ∃ out, Compute (RegisteredStructure.definitions
      (Definitions.ofEnv Params.env Params.univs Params.henv)) b out ∧
      Compute (RegisteredStructure.definitions
        (Definitions.ofEnv Params.env Params.univs Params.henv)) c out :=
  R1.confluent (fun H1 H2 => RegisteredStructure.definitions_ofEnv_unique H1 H2) R2

end Lean4Lean.VEnv.Strengthening.PureObservation
