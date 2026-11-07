import Lean4Lean.Theory.Typing.Strengthening.ProofErasureComputedJointTransport

/-! # Structural depth of the full computed joint checker

The bound counts structural comparison and carrier layers, including finite
field families. Computation prefixes, symmetry and carrier computations cost
no depth. This measures certificates, not normalization of terms or guards.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params]
namespace ProofShape

/-- The full recursive checker with a structural-depth upper bound.
All recursive premises of a structural rule fit below its next depth layer.
Native and computed application rules have the same cost. -/
inductive ComputedJointCheckDepth (Step : List ProofShape → ProofShape → ProofShape → Prop) :
    Nat → List ProofShape → JointCheckKind → ProofShape → ProofShape → Prop where
  | leaf : ScopedLeaf mode a b → ComputedJointCheckDepth Step n Δ (.compare mode) a b
  | app : ComputedJointCheckDepth Step n Δ (.compare false) f f' → ComputedJointCheckDepth Step n Δ (.compare true) a a' →
      ComputedJointCheckDepth Step (n+1) Δ (.compare mode) (.app f a) (.app f' a')
  /-- A recovered domain licenses carrier comparison at the argument, while
  the inferred function comparison recursively uses this enlarged language. -/
  | appCarrier : ScopedTypeRecovery Step Δ f (.forallE A B) →
      ComputedJointCheckDepth Step n Δ (.compare false) f g → ComputedJointCheckDepth Step n Δ (.carrier A) x y →
      ComputedJointCheckDepth Step (n+1) Δ (.compare mode) (.app f x) (.app g y)
  /-- Read a domain from computation of the left function; both checking
  premises recurse in this same family. -/
  | appComputed : ScopedCompute Step Δ f (.lam A body) →
      ComputedJointCheckDepth Step n Δ (.compare false) f g →
      ComputedJointCheckDepth Step n Δ (.carrier A) x y →
      ComputedJointCheckDepth Step (n+1) Δ (.compare mode) (.app f x) (.app g y)
  | proj : ComputedJointCheckDepth Step n Δ (.compare false) m m' →
      ComputedJointCheckDepth Step (n+1) Δ (.compare mode) (.proj s i m) (.proj s i m')
  | lam : ComputedJointCheckDepth Step n Δ (.compare false) A A' → ComputedJointCheckDepth Step n (A :: Δ) (.compare mode) b b' →
      ComputedJointCheckDepth Step (n+1) Δ (.compare mode) (.lam A b) (.lam A' b')
  | forallE : ComputedJointCheckDepth Step n Δ (.compare false) A A' → ComputedJointCheckDepth Step n (A :: Δ) (.compare false) B B' →
      ComputedJointCheckDepth Step (n+1) Δ (.compare mode) (.forallE A B) (.forallE A' B')
  /-- Equal witnessed sorts align independently supplied domain typings. -/
  | lamSorted : DomainSort Δ A u → DomainSort Δ A' u → ComputedJointCheckDepth Step n Δ (.compare true) A A' →
      ComputedJointCheckDepth Step n (A :: Δ) (.compare mode) b b' →
      ComputedJointCheckDepth Step (n+1) Δ (.compare mode) (.lam A b) (.lam A' b')
  /-- Pi domains and codomains are types, so shared witnessed sorts suffice
  for common-mode recursive comparison at both positions. -/
  | forallSorted : DomainSort Δ A u → DomainSort Δ A' u → ComputedJointCheckDepth Step n Δ (.compare true) A A' →
      DomainSort (A :: Δ) B v → DomainSort (A :: Δ) B' v →
      ComputedJointCheckDepth Step n (A :: Δ) (.compare true) B B' →
      ComputedJointCheckDepth Step (n+1) Δ (.compare mode) (.forallE A B) (.forallE A' B')
  | lamCommon : ComputedJointCheckDepth Step n (A :: Δ) (.compare true) b b' →
      ComputedJointCheckDepth Step (n+1) Δ (.compare true) (.lam A b) (.lam A' b')
  | etaBodyL : DomainSort Δ A u →
      ComputedJointCheckDepth Step n (A :: Δ) (.compare true) b (.app (f.liftN 1) (etaArgument u)) →
      ComputedJointCheckDepth Step (n+1) Δ (.compare true) (.lam A b) f
  | etaBodyR : DomainSort Δ A u →
      ComputedJointCheckDepth Step n (A :: Δ) (.compare true) (.app (f.liftN 1) (etaArgument u)) b →
      ComputedJointCheckDepth Step (n+1) Δ (.compare true) f (.lam A b)
  /-- Source constructor parameters determine a typed projected expansion.
  Every retained field recursively checks against its projection of the major. -/
  | structFields {family : Name} {info : VProjectionInfo} {ls : List VLevel}
      {ps fields : List ProofShape} {m : ProofShape}
      (hi : env.projections family info) (hx : info.nindices = 0)
      (hp : ps.length = info.nparams) (hf : fields.length = info.numFields)
      (hadm : (info.resultLevel.inst ls).IsNeverZero ∨ StructureReplay.ProofFields env univs info ls)
      (H : ∀ i (h : i < fields.length), fields[i] ≠ .proof →
        ComputedJointCheckDepth Step n Δ (.compare true) fields[i] (.proj family i m)) :
      ComputedJointCheckDepth Step (n+1) Δ (.compare true) (mkApps (.const info.ctorName ls) (ps ++ fields)) m
  /-- Displayed lambda domains align lambda-headed eta in inferred mode. -/
  | etaLams : ComputedJointCheckDepth Step n Δ (.compare false) A D →
      (EtaHead (.lam A b) (.lam D f) ∨ EtaHead (.lam D f) (.lam A b)) →
      ComputedJointCheckDepth Step (n+1) Δ (.compare mode) (.lam A b) (.lam D f)
  | compute : ScopedCompute Step Δ a a' → ScopedCompute Step Δ b b' → ComputedJointCheckDepth Step n Δ (.compare mode) a' b' →
      ComputedJointCheckDepth Step n Δ (.compare mode) a b
  | symm : ComputedJointCheckDepth Step n Δ (.compare mode) a b → ComputedJointCheckDepth Step n Δ (.compare mode) b a
  | carrierIntro (hi : env.projections family info) (hx : info.nindices = 0)
      (hp : ps.length = info.nparams)
      (hadm : (info.resultLevel.inst ls).IsNeverZero ∨ StructureReplay.ProofFields env univs info ls)
      (H : ∀ i, i < info.numFields → ¬ StructureReplay.ProofField env univs info ls i →
        ComputedJointCheckDepth Step n Δ (.compare true) (.proj family i a) (.proj family i b)) :
      ComputedJointCheckDepth Step (n+1) Δ (.carrier (mkApps (.const family ls) ps)) a b
  | carrierChecked : ComputedJointCheckDepth Step n Δ (.compare true) a b → ComputedJointCheckDepth Step (n+1) Δ (.carrier A) a b
  | carrierSubsingleton : SubsingletonCarrier A → ComputedJointCheckDepth Step n Δ (.carrier A) a b
  | carrierFunction : DomainSort Δ A u →
      ComputedJointCheckDepth Step n (A :: Δ) (.carrier B)
        (.app (a.liftN 1) (etaArgument u)) (.app (b.liftN 1) (etaArgument u)) →
      ComputedJointCheckDepth Step (n+1) Δ (.carrier (.forallE A B)) a b
  | carrierSymm : ComputedJointCheckDepth Step n Δ (.carrier A) a b → ComputedJointCheckDepth Step n Δ (.carrier A) b a
  | carrierCompute : ScopedCompute Step Δ A A' → ComputedJointCheckDepth Step n Δ (.carrier A') a b →
      ComputedJointCheckDepth Step n Δ (.carrier A) a b
  | carrierReduce : ScopedCompute Step Δ a a' → ScopedCompute Step Δ b b' →
      ComputedJointCheckDepth Step n Δ (.carrier A) a' b' → ComputedJointCheckDepth Step n Δ (.carrier A) a b
  | carrierNested (hi : env.projections family info) (hx : info.nindices = 0)
      (hp : ps.length = info.nparams)
      (hadm : (info.resultLevel.inst ls).IsNeverZero ∨ StructureReplay.ProofFields env univs info ls)
      (HT : ProjTele env univs family info ls doms result)
      (H : ∀ i (hj : i < info.numFields), ¬ StructureReplay.ProofField env univs info ls i →
        ComputedJointCheckDepth Step n Δ
          (.carrier (projectionType family info doms i (by have := HT.numFields; omega) ps a))
          (.proj family i a) (.proj family i b)) :
      ComputedJointCheckDepth Step (n+1) Δ (.carrier (mkApps (.const family ls) ps)) a b

/-- Forget the depth bound, retaining exactly the original checker. -/
theorem ComputedJointCheckDepth.forget
    (H : ComputedJointCheckDepth Step n Δ kind a b) : ComputedJointCheck Step Δ kind a b := by
  induction H with
  | leaf H => exact .leaf H
  | app _ _ ihf ihx => exact .app ihf ihx
  | appCarrier R _ _ ihf ihx => exact .appCarrier R ihf ihx
  | appComputed R _ _ ihf ihx => exact .appComputed R ihf ihx
  | proj _ ih => exact .proj ih
  | lam _ _ ihA ihb => exact .lam ihA ihb
  | forallE _ _ ihA ihB => exact .forallE ihA ihB
  | lamSorted S S' _ _ ihA ihb => exact .lamSorted S S' ihA ihb
  | forallSorted S S' _ T T' _ ihA ihB => exact .forallSorted S S' ihA T T' ihB
  | lamCommon _ ih => exact .lamCommon ih
  | etaBodyL S _ ih => exact .etaBodyL S ih
  | etaBodyR S _ ih => exact .etaBodyR S ih
  | structFields hi hx hp hf hadm _ ih => exact .structFields hi hx hp hf hadm ih
  | etaLams _ H ih => exact .etaLams ih H
  | compute Ra Rb _ ih => exact .compute Ra Rb ih
  | symm _ ih => exact .symm ih
  | carrierIntro hi hx hp hadm _ ih => exact .carrierIntro hi hx hp hadm ih
  | carrierChecked _ ih => exact .carrierChecked ih
  | carrierSubsingleton H => exact .carrierSubsingleton H
  | carrierFunction S _ ih => exact .carrierFunction S ih
  | carrierSymm _ ih => exact .carrierSymm ih
  | carrierCompute R _ ih => exact .carrierCompute R ih
  | carrierReduce Ra Rb _ ih => exact .carrierReduce Ra Rb ih
  | carrierNested hi hx hp hadm HT _ ih => exact .carrierNested hi hx hp hadm HT ih

/-- Any larger upper bound is admissible. -/
theorem ComputedJointCheckDepth.weaken
    (H : ComputedJointCheckDepth Step n Δ kind a b) (h : n ≤ m) :
    ComputedJointCheckDepth Step m Δ kind a b := by
  induction H generalizing m with
  | leaf H => exact .leaf H
  | app _ _ ihf ihx =>
    cases m with
    | zero => omega
    | succ m => exact .app (ihf (by omega)) (ihx (by omega))
  | appCarrier R _ _ ihf ihx =>
    cases m with
    | zero => omega
    | succ m => exact .appCarrier R (ihf (by omega)) (ihx (by omega))
  | appComputed R _ _ ihf ihx =>
    cases m with
    | zero => omega
    | succ m => exact .appComputed R (ihf (by omega)) (ihx (by omega))
  | proj _ ih =>
    cases m with
    | zero => omega
    | succ m => exact .proj (ih (by omega))
  | lam _ _ ihA ihb =>
    cases m with
    | zero => omega
    | succ m => exact .lam (ihA (by omega)) (ihb (by omega))
  | forallE _ _ ihA ihB =>
    cases m with
    | zero => omega
    | succ m => exact .forallE (ihA (by omega)) (ihB (by omega))
  | lamSorted S S' _ _ ihA ihb =>
    cases m with
    | zero => omega
    | succ m => exact .lamSorted S S' (ihA (by omega)) (ihb (by omega))
  | forallSorted S S' _ T T' _ ihA ihB =>
    cases m with
    | zero => omega
    | succ m => exact .forallSorted S S' (ihA (by omega)) T T' (ihB (by omega))
  | lamCommon _ ih =>
    cases m with
    | zero => omega
    | succ m => exact .lamCommon (ih (by omega))
  | etaBodyL S _ ih =>
    cases m with
    | zero => omega
    | succ m => exact .etaBodyL S (ih (by omega))
  | etaBodyR S _ ih =>
    cases m with
    | zero => omega
    | succ m => exact .etaBodyR S (ih (by omega))
  | structFields hi hx hp hf hadm _ ih =>
    cases m with
    | zero => omega
    | succ m => exact .structFields hi hx hp hf hadm (fun i hj hn => ih i hj hn (by omega))
  | etaLams _ H ih =>
    cases m with
    | zero => omega
    | succ m => exact .etaLams (ih (by omega)) H
  | compute Ra Rb _ ih => exact .compute Ra Rb (ih h)
  | symm _ ih => exact .symm (ih h)
  | carrierIntro hi hx hp hadm _ ih =>
    cases m with
    | zero => omega
    | succ m => exact .carrierIntro hi hx hp hadm (fun i hj hn => ih i hj hn (by omega))
  | carrierChecked _ ih =>
    cases m with
    | zero => omega
    | succ m => exact .carrierChecked (ih (by omega))
  | carrierSubsingleton H => exact .carrierSubsingleton H
  | carrierFunction S _ ih =>
    cases m with
    | zero => omega
    | succ m => exact .carrierFunction S (ih (by omega))
  | carrierSymm _ ih => exact .carrierSymm (ih h)
  | carrierCompute R _ ih => exact .carrierCompute R (ih h)
  | carrierReduce Ra Rb _ ih => exact .carrierReduce Ra Rb (ih h)
  | carrierNested hi hx hp hadm HT _ ih =>
    cases m with
    | zero => omega
    | succ m => exact .carrierNested hi hx hp hadm HT (fun i hj hn => ih i hj hn (by omega))

omit [Params] in
private theorem finite_depth_bound
    {R : (i : Nat) → i < len → Nat → Prop}
    (hm : ∀ i hi n m, n ≤ m → R i hi n → R i hi m)
    (H : ∀ i hi, ∃ n, R i hi n) : ∃ n, ∀ i hi, R i hi n := by
  induction len with
  | zero => exact ⟨0, fun i hi => (Nat.not_lt_zero i hi).elim⟩
  | succ len ih =>
    obtain ⟨n, Hn⟩ := ih
      (R := fun i hi k => R i (Nat.lt_trans hi (Nat.lt_succ_self len)) k)
      (fun i hi k l h => hm i _ k l h) (fun i hi => H i _)
    obtain ⟨m, Hm⟩ := H len (Nat.lt_succ_self len)
    refine ⟨max n m, ?_⟩
    intro i hi
    by_cases he : i = len
    · subst i; exact hm _ _ _ _ (Nat.le_max_right ..) Hm
    · exact hm _ _ _ _ (Nat.le_max_left ..) (Hn i (by omega))

/-- Every original checker certificate admits a finite structural-depth bound,
including rules with an arbitrary finite family of field premises. -/
theorem ComputedJointCheck.depth
    (H : ComputedJointCheck Step Δ kind a b) :
    ∃ n, ComputedJointCheckDepth Step n Δ kind a b := by
  classical
  induction H with
  | leaf H => exact ⟨0, .leaf H⟩
  | app _ _ ihf ihx =>
    obtain ⟨n, Hn⟩ := ihf
    obtain ⟨m, Hm⟩ := ihx
    exact ⟨max n m + 1, .app (Hn.weaken (Nat.le_max_left n m)) (Hm.weaken (Nat.le_max_right n m))⟩
  | appCarrier R _ _ ihf ihx =>
    obtain ⟨n, Hn⟩ := ihf
    obtain ⟨m, Hm⟩ := ihx
    exact ⟨max n m + 1, .appCarrier R (Hn.weaken (Nat.le_max_left n m)) (Hm.weaken (Nat.le_max_right n m))⟩
  | appComputed R _ _ ihf ihx =>
    obtain ⟨n, Hn⟩ := ihf
    obtain ⟨m, Hm⟩ := ihx
    exact ⟨max n m + 1, .appComputed R (Hn.weaken (Nat.le_max_left n m)) (Hm.weaken (Nat.le_max_right n m))⟩
  | proj _ ih =>
    obtain ⟨n, Hn⟩ := ih
    exact ⟨n+1, .proj Hn⟩
  | lam _ _ ihA ihb =>
    obtain ⟨n, Hn⟩ := ihA
    obtain ⟨m, Hm⟩ := ihb
    exact ⟨max n m + 1, .lam (Hn.weaken (Nat.le_max_left n m)) (Hm.weaken (Nat.le_max_right n m))⟩
  | forallE _ _ ihA ihB =>
    obtain ⟨n, Hn⟩ := ihA
    obtain ⟨m, Hm⟩ := ihB
    exact ⟨max n m + 1, .forallE (Hn.weaken (Nat.le_max_left n m)) (Hm.weaken (Nat.le_max_right n m))⟩
  | lamSorted S S' _ _ ihA ihb =>
    obtain ⟨n, Hn⟩ := ihA
    obtain ⟨m, Hm⟩ := ihb
    exact ⟨max n m + 1, .lamSorted S S' (Hn.weaken (Nat.le_max_left n m)) (Hm.weaken (Nat.le_max_right n m))⟩
  | forallSorted S S' _ T T' _ ihA ihB =>
    obtain ⟨n, Hn⟩ := ihA
    obtain ⟨m, Hm⟩ := ihB
    exact ⟨max n m + 1, .forallSorted S S' (Hn.weaken (Nat.le_max_left n m)) T T' (Hm.weaken (Nat.le_max_right n m))⟩
  | lamCommon _ ih =>
    obtain ⟨n, Hn⟩ := ih
    exact ⟨n+1, .lamCommon Hn⟩
  | etaBodyL S _ ih =>
    obtain ⟨n, Hn⟩ := ih
    exact ⟨n+1, .etaBodyL S Hn⟩
  | etaBodyR S _ ih =>
    obtain ⟨n, Hn⟩ := ih
    exact ⟨n+1, .etaBodyR S Hn⟩
  | @structFields Δ family info ls ps fields major hi hx hp hf hadm _ ih =>
    have HB : ∃ n, ∀ i (hj : i < fields.length), fields[i] ≠ .proof →
        ComputedJointCheckDepth Step n Δ (.compare true) fields[i] (.proj family i major) := by
      apply finite_depth_bound
      · intro i hi n m h Hn hn
        exact (Hn hn).weaken h
      · intro i hi
        by_cases hn : fields[i] ≠ .proof
        · obtain ⟨n, Hn⟩ := ih i hi hn
          exact ⟨n, fun _ => Hn⟩
        · exact ⟨0, fun hn' => (hn hn').elim⟩
    obtain ⟨n, Hn⟩ := HB
    exact ⟨n+1, .structFields hi hx hp hf hadm Hn⟩
  | etaLams _ H ih =>
    obtain ⟨n, Hn⟩ := ih
    exact ⟨n+1, .etaLams Hn H⟩
  | compute Ra Rb _ ih =>
    obtain ⟨n, Hn⟩ := ih
    exact ⟨n, .compute Ra Rb Hn⟩
  | symm _ ih =>
    obtain ⟨n, Hn⟩ := ih
    exact ⟨n, .symm Hn⟩
  | @carrierIntro family info ls Δ a b ps hi hx hp hadm _ ih =>
    have HB : ∃ n, ∀ i, i < info.numFields → ¬ StructureReplay.ProofField env univs info ls i →
        ComputedJointCheckDepth Step n Δ (.compare true) (.proj family i a) (.proj family i b) := by
      apply finite_depth_bound
      · intro i hi n m h Hn hn
        exact (Hn hn).weaken h
      · intro i hi
        by_cases hn : ¬ StructureReplay.ProofField env univs info ls i
        · obtain ⟨n, Hn⟩ := ih i hi hn
          exact ⟨n, fun _ => Hn⟩
        · exact ⟨0, fun hn' => (hn hn').elim⟩
    obtain ⟨n, Hn⟩ := HB
    exact ⟨n+1, .carrierIntro hi hx hp hadm Hn⟩
  | carrierChecked _ ih =>
    obtain ⟨n, Hn⟩ := ih
    exact ⟨n+1, .carrierChecked Hn⟩
  | carrierSubsingleton H => exact ⟨0, .carrierSubsingleton H⟩
  | carrierFunction S _ ih =>
    obtain ⟨n, Hn⟩ := ih
    exact ⟨n+1, .carrierFunction S Hn⟩
  | carrierSymm _ ih =>
    obtain ⟨n, Hn⟩ := ih
    exact ⟨n, .carrierSymm Hn⟩
  | carrierCompute R _ ih =>
    obtain ⟨n, Hn⟩ := ih
    exact ⟨n, .carrierCompute R Hn⟩
  | carrierReduce Ra Rb _ ih =>
    obtain ⟨n, Hn⟩ := ih
    exact ⟨n, .carrierReduce Ra Rb Hn⟩
  | @carrierNested family info ls doms result Δ ps a b hi hx hp hadm HT _ ih =>
    have HB : ∃ n, ∀ i (hj : i < info.numFields), ¬ StructureReplay.ProofField env univs info ls i →
        ComputedJointCheckDepth Step n Δ
          (.carrier (projectionType family info doms i (by have := HT.numFields; omega) ps a))
          (.proj family i a) (.proj family i b) := by
      apply finite_depth_bound
      · intro i hi n m h Hn hn
        exact (Hn hn).weaken h
      · intro i hi
        by_cases hn : ¬ StructureReplay.ProofField env univs info ls i
        · obtain ⟨n, Hn⟩ := ih i hi hn
          exact ⟨n, fun _ => Hn⟩
        · exact ⟨0, fun hn' => (hn hn').elim⟩
    obtain ⟨n, Hn⟩ := HB
    exact ⟨n+1, .carrierNested hi hx hp hadm HT Hn⟩

/-- Comparison at a bounded structural depth. -/
abbrev ComputedJointCompareDepth (Step : List ProofShape → ProofShape → ProofShape → Prop)
    (n : Nat) (Δ : List ProofShape) (mode : Bool) (a b : ProofShape) : Prop :=
  ComputedJointCheckDepth Step n Δ (.compare mode) a b

/-- Explicit-carrier checking at a bounded structural depth. -/
abbrev ComputedJointCarrierDepth (Step : List ProofShape → ProofShape → ProofShape → Prop)
    (n : Nat) (Δ : List ProofShape) (A a b : ProofShape) : Prop :=
  ComputedJointCheckDepth Step n Δ (.carrier A) a b
end ProofShape

open private erase_app_inv erase_proj_inv erase_lam_inv erase_forallE_inv
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
open private infer_raw common_raw carrier_raw domain_sort_raw lambda_common_context
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureComputedJointTransport

/-- Typed interpretation of checker transport at the unchanged depth bound. -/
def ComputedJointTransportDepthResult (Transport : List ProofShape → List ProofShape → ProofShape.Subst → Prop)
    (Target : List ProofShape → ProofShape → ProofShape → Prop)
    (n : Nat) (Δ : List ProofShape) (kind : JointCheckKind) (sa sb : ProofShape) : Prop :=
  match kind with
  | .compare mode => ∀ {Γ a b A Δ' τ}, OnCtx Γ (env.IsType univs) →
      env.HasType univs Γ a A → env.HasType univs Γ b A → proofEraseCtx Γ = Δ →
      proofErase Γ a = sa → proofErase Γ b = sb → Transport Δ Δ' τ →
      ComputedJointCompareDepth Target n Δ' mode (sa.subst τ) (sb.subst τ)
  | .carrier α => ∀ {Γ a b A Δ' τ}, OnCtx Γ (env.IsType univs) →
      env.HasType univs Γ a A → env.HasType univs Γ b A → proofEraseCtx Γ = Δ →
      proofErase Γ A = α → proofErase Γ a = sa → proofErase Γ b = sb →
      Transport Δ Δ' τ → ComputedJointCarrierDepth Target n Δ' (α.subst τ) (sa.subst τ) (sb.subst τ)

/-- Recursive transport with a typed application repair. The callback receives
both already transported guards and actual source argument typings at the
selected domain. It may convert the argument carrier before rebuilding the
application at exactly one layer above the supplied child bounds. Every other
constructor, including computed-domain applications, transports without changing
its bound. This is an induction interface;
its application callback must be proved for the chosen substitution class. -/
theorem ProofShape.ComputedJointCheckDepth.transport_application
    (Transport : List ProofShape → List ProofShape → ProofShape.Subst → Prop)
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hcons : ∀ {Δ Δ' τ A}, Transport Δ Δ' τ → Transport (A :: Δ) (A.subst τ :: Δ') τ.lift)
    (hsort : ∀ {Δ Δ' τ A u}, Transport Δ Δ' τ → DomainSort Δ A u → DomainSort Δ' (A.subst τ) u)
    (hcompute : ∀ {Γ Δ Δ' τ e T source out}, ScopedCompute Step Δ source out →
      OnCtx Γ (env.IsType univs) → env.HasType univs Γ e T →
      proofEraseCtx Γ = Δ → proofErase Γ e = source → Transport Δ Δ' τ →
      ScopedCompute Target Δ' (source.subst τ) (out.subst τ))
    (happ : ∀ {n Γ Δ' τ f x y D C A B g mode}, OnCtx Γ (env.IsType univs) →
      env.HasType univs Γ f (.forallE D C) →
      env.HasType univs Γ x D → env.HasType univs Γ y D → ¬ IsProof Γ f →
      ScopedTypeRecovery Step (proofEraseCtx Γ) (proofErase Γ f) (.forallE A B) →
      Transport (proofEraseCtx Γ) Δ' τ →
      ComputedJointCompareDepth Target n Δ' false ((proofErase Γ f).subst τ) g →
      ComputedJointCarrierDepth Target n Δ' (A.subst τ)
        ((proofErase Γ x).subst τ) ((proofErase Γ y).subst τ) →
      ComputedJointCompareDepth Target (n+1) Δ' mode
        (.app ((proofErase Γ f).subst τ) ((proofErase Γ x).subst τ))
        (.app g ((proofErase Γ y).subst τ)))
    (H : ComputedJointCheckDepth Step n Δ kind sa sb) : ComputedJointTransportDepthResult Transport Target n Δ kind sa sb := by
  induction H with
  | leaf H =>
    intro Γ a b A Δ' τ hΓ ha hb EΓ Ea Eb W
    exact .leaf H.subst
  | app HF HX ihf ihx =>
    intro Γ a b A Δ' τ hΓ ha hb EΓ Ea Eb W
    obtain ⟨f, x, rfl, hna, Ef, Ex⟩ := erase_app_inv Ea
    obtain ⟨g, y, rfl, hnb, Eg, Ey⟩ := erase_app_inv Eb
    obtain ⟨_, _, hf, hx⟩ := ha.app_inv henv hΓ
    obtain ⟨_, _, hg, hy⟩ := hb.app_inv henv hΓ
    have HE := infer_raw hstep HF.forget hΓ hf hg EΓ Ef Eg
      (not_isProof_fn hΓ hf hx hna) (not_isProof_fn hΓ hg hy hnb)
    have hy' := argument_at_displayed_domain hΓ hg HE.hasType.2 hy
    exact .app (ihf hΓ hf HE.hasType.2 EΓ Ef Eg W) (ihx hΓ hx hy' EΓ Ex Ey W)
  | appCarrier R HF HX ihf ihx =>
    intro Γ a b A Δ' τ hΓ ha hb EΓ Ea Eb W
    obtain ⟨f, x, rfl, hna, Ef, Ex⟩ := erase_app_inv Ea
    obtain ⟨g, y, rfl, hnb, Eg, Ey⟩ := erase_app_inv Eb
    obtain ⟨_, _, hf, hx⟩ := ha.app_inv henv hΓ
    obtain ⟨_, _, hg, hy⟩ := hb.app_inv henv hΓ
    have HE := infer_raw hstep HF.forget hΓ hf hg EΓ Ef Eg
      (not_isProof_fn hΓ hf hx hna) (not_isProof_fn hΓ hg hy hnb)
    obtain ⟨D, C, hfPi, ED, EC⟩ := proofErase_scoped_recovered_pi_descend hstep hΓ hΓ
      (show Ctx.LiftN 0 0 Γ Γ from .zero []) hf
      (by simpa only [ProofShape.liftN_zero, EΓ, Ef] using R)
    have hgPi := (show env.IsDefEqU univs Γ f g from ⟨_, HE⟩).of_l henv hΓ hfPi |>.hasType.2
    have hxD := argument_at_displayed_domain hΓ hf hfPi hx
    have hyD := argument_at_displayed_domain hΓ hg hgPi hy
    have HX' := ihx hΓ hxD hyD EΓ (by simpa only [ProofShape.liftN_zero] using ED) Ex Ey W
    have HF' := ihf hΓ hf HE.hasType.2 EΓ Ef Eg W
    simpa only [Ef, Ex, Ey, ProofShape.subst] using
      happ hΓ hfPi hxD hyD (not_isProof_fn hΓ hf hx hna)
        (by simpa only [EΓ, Ef] using R) (by simpa only [EΓ] using W)
        (by simpa only [Ef] using HF')
        (by simpa only [Ex, Ey] using HX')
  | appComputed RF HF HX ihf ihx =>
    intro Γ a b A Δ' τ hΓ ha hb EΓ Ea Eb W
    obtain ⟨f, x, rfl, hna, Ef, Ex⟩ := erase_app_inv Ea
    obtain ⟨g, y, rfl, hnb, Eg, Ey⟩ := erase_app_inv Eb
    obtain ⟨_, _, hf, hx⟩ := ha.app_inv henv hΓ
    obtain ⟨_, _, hg, hy⟩ := hb.app_inv henv hΓ
    have HE := infer_raw hstep HF.forget hΓ hf hg EΓ Ef Eg
      (not_isProof_fn hΓ hf hx hna) (not_isProof_fn hΓ hg hy hnb)
    obtain ⟨f', HE', EF'⟩ := proofErase_scoped_compute_realize hstep hΓ hf EΓ Ef RF
    obtain ⟨D, body, rfl, _, ED, _⟩ := erase_lam_inv EF'
    obtain ⟨⟨_, hD⟩, _, hbody⟩ := HE'.hasType.2.lam_inv henv hΓ
    have hfPi := (HE'.toU.of_r henv hΓ (HasType.lam hD hbody)).hasType.1
    have hgPi := HE.toU.of_l henv hΓ hfPi |>.hasType.2
    have hxD := argument_at_displayed_domain hΓ hf hfPi hx
    have hyD := argument_at_displayed_domain hΓ hg hgPi hy
    exact .appComputed (hcompute RF hΓ hf EΓ Ef W)
      (ihf hΓ hf HE.hasType.2 EΓ Ef Eg W) (ihx hΓ hxD hyD EΓ ED Ex Ey W)
  | proj HM ihm =>
    intro Γ a b A Δ' τ hΓ ha hb EΓ Ea Eb W
    obtain ⟨m, rfl, hn, Em⟩ := erase_proj_inv Ea
    obtain ⟨m', rfl, hn', Em'⟩ := erase_proj_inv Eb
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ := ha.proj_inv henv hΓ
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm', _, _⟩ := hb.proj_inv henv hΓ
    have HE := infer_raw hstep HM.forget hΓ hm.hasType.2 hm'.hasType.2 EΓ Em Em'
      (not_isProof_major hΓ ha hn) (not_isProof_major hΓ hb hn')
    exact .proj (ihm hΓ hm.hasType.2 HE.hasType.2 EΓ Em Em' W)
  | lam HD HB ihD ihB =>
    intro Γ a b A Δ' τ hΓ ha hb EΓ Ea Eb W
    obtain ⟨D, body, rfl, _, ED, Ebody⟩ := erase_lam_inv Ea
    obtain ⟨D', body', rfl, _, ED', Ebody'⟩ := erase_lam_inv Eb
    obtain ⟨u, C, hD, hD', hbody, hbody', Ectx⟩ := lambda_common_context hΓ ha hb
    rw [Ectx] at Ebody'
    have hΓD : OnCtx (D :: Γ) (env.IsType univs) := ⟨hΓ, u, hD⟩
    have HB' := ihB hΓD hbody hbody' (by simp only [proofEraseCtx, EΓ, ED]) Ebody Ebody' (hcons W)
    exact .lam (ihD hΓ hD hD' EΓ ED ED' W) HB'
  | lamSorted SD SD' HD HB ihD ihB =>
    intro Γ a b A Δ' τ hΓ ha hb EΓ Ea Eb W
    obtain ⟨D, body, rfl, _, ED, Ebody⟩ := erase_lam_inv Ea
    obtain ⟨D', body', rfl, _, ED', Ebody'⟩ := erase_lam_inv Eb
    obtain ⟨u, C, hD, hD', hbody, hbody', Ectx⟩ := lambda_common_context hΓ ha hb
    rw [Ectx] at Ebody'
    have hΓD : OnCtx (D :: Γ) (env.IsType univs) := ⟨hΓ, u, hD⟩
    have HB' := ihB hΓD hbody hbody' (by simp only [proofEraseCtx, EΓ, ED]) Ebody Ebody' (hcons W)
    exact .lamSorted (hsort W SD) (hsort W SD') (ihD hΓ hD hD' EΓ ED ED' W) HB'
  | lamCommon HB ihB =>
    intro Γ a b A Δ' τ hΓ ha hb EΓ Ea Eb W
    obtain ⟨D, body, rfl, _, ED, Ebody⟩ := erase_lam_inv Ea
    obtain ⟨D', body', rfl, _, ED', Ebody'⟩ := erase_lam_inv Eb
    obtain ⟨u, C, hD, hD', hbody, hbody', Ectx⟩ := lambda_common_context hΓ ha hb
    rw [Ectx] at Ebody'
    have hΓD : OnCtx (D :: Γ) (env.IsType univs) := ⟨hΓ, u, hD⟩
    have HB' := ihB hΓD hbody hbody' (by simp only [proofEraseCtx, EΓ, ED]) Ebody Ebody' (hcons W)
    exact .lamCommon HB'
  | etaLams HD Hη ihD =>
    intro Γ a b A Δ' τ hΓ ha hb EΓ Ea Eb W
    obtain ⟨D, body, rfl, _, ED, Ebody⟩ := erase_lam_inv Ea
    obtain ⟨D', body', rfl, _, ED', Ebody'⟩ := erase_lam_inv Eb
    obtain ⟨u, C, hD, hD', hbody, hbody', Ectx⟩ := lambda_common_context hΓ ha hb
    rw [Ectx] at Ebody'
    have hΓD : OnCtx (D :: Γ) (env.IsType univs) := ⟨hΓ, u, hD⟩
    exact .etaLams (ihD hΓ hD hD' EΓ ED ED' W) (Hη.imp (fun H => H.subst) (fun H => H.subst))
  | forallE HD HC ihD ihC =>
    intro Γ a b A Δ' τ hΓ ha hb EΓ Ea Eb W
    obtain ⟨D, C, rfl, _, ED, EC⟩ := erase_forallE_inv Ea
    obtain ⟨D', C', rfl, _, ED', EC'⟩ := erase_forallE_inv Eb
    obtain ⟨⟨u, hD⟩, _, hC⟩ := ha.forallE_inv henv
    obtain ⟨⟨_, hD'⟩, _, hC'⟩ := hb.forallE_inv henv
    have HDD := infer_raw hstep HD.forget hΓ hD hD' EΓ ED ED'
      (not_isProof_of_sort hΓ hD) (not_isProof_of_sort hΓ hD')
    have hΓD : OnCtx (D :: Γ) (env.IsType univs) := ⟨hΓ, u, hD⟩
    have hctx := IsDefEqCtx.succ .zero HDD.symm
    have Ectx := proofErase_defeqCtx (Γ₁ := D' :: Γ) ⟨hΓ, _, hD'⟩ hctx hC'
    rw [Ectx] at EC'
    have hC' := hC'.defeqDFC henv hctx
    have EΓD := congr (congrArg List.cons ED) EΓ
    change proofEraseCtx (D :: Γ) = _ at EΓD
    have HCC := infer_raw hstep HC.forget hΓD hC hC' EΓD EC EC'
      (not_isProof_of_sort hΓD hC) (not_isProof_of_sort hΓD hC')
    exact .forallE (ihD hΓ hD HDD.hasType.2 EΓ ED ED' W)
      (ihC hΓD hC HCC.hasType.2 EΓD EC EC' (hcons W))
  | forallSorted SD SD' HD SC SC' HC ihD ihC =>
    intro Γ a b A Δ' τ hΓ ha hb EΓ Ea Eb W
    obtain ⟨D, C, rfl, _, ED, EC⟩ := erase_forallE_inv Ea
    obtain ⟨D', C', rfl, _, ED', EC'⟩ := erase_forallE_inv Eb
    obtain ⟨⟨_, hD⟩, _, hC⟩ := ha.forallE_inv henv
    obtain ⟨⟨_, hD'⟩, _, hC'⟩ := hb.forallE_inv henv
    have hD := domain_sort_raw SD hΓ hD EΓ ED
    have hD' := domain_sort_raw SD' hΓ hD' EΓ ED'
    have HDD := common_raw hstep HD.forget hΓ hD hD' EΓ ED ED'
    have hΓD : OnCtx (D :: Γ) (env.IsType univs) := ⟨hΓ, _, hD⟩
    have hctx := IsDefEqCtx.succ .zero HDD.symm
    have Ectx := proofErase_defeqCtx (Γ₁ := D' :: Γ) ⟨hΓ, _, hD'⟩ hctx hC'
    rw [Ectx] at EC'
    have hC' := hC'.defeqDFC henv hctx
    have EΓD := congr (congrArg List.cons ED) EΓ
    change proofEraseCtx (D :: Γ) = _ at EΓD
    have hC := domain_sort_raw SC hΓD hC EΓD EC
    have hC' := domain_sort_raw SC' hΓD hC' EΓD EC'
    exact .forallSorted (hsort W SD) (hsort W SD') (ihD hΓ hD hD' EΓ ED ED' W)
      (hsort (hcons W) SC) (hsort (hcons W) SC')
      (ihC hΓD hC hC' EΓD EC EC' (hcons W))
  | etaBodyL SD HB ihB =>
    intro Γ a b A Δ' τ hΓ ha hb EΓ Ea Eb W
    obtain ⟨D, body, rfl, hn, ED, Ebody⟩ := erase_lam_inv Ea
    obtain ⟨⟨_, hD⟩, C, hbody⟩ := ha.lam_inv henv hΓ
    have hD := domain_sort_raw SD hΓ hD EΓ ED
    have hΓD : OnCtx (D :: Γ) (env.IsType univs) := ⟨hΓ, _, hD⟩
    have hfPi := hb.defeqU_r henv hΓ (ha.uniqU henv hΓ (HasType.lam hD hbody))
    have hnf : ¬ IsProof Γ b := by
      rintro ⟨P, hfP, hP⟩
      exact hn ⟨P, ha.defeqU_r henv hΓ (hb.uniqU henv hΓ hfP), hP⟩
    have hη : env.HasType univs (D :: Γ) (.app b.lift (.bvar 0)) C := by
      simpa only [lift, VExpr.liftN, inst_liftN_bvar] using HasType.app (hfPi.weak henv (B := D)) (.bvar .zero)
    have Eη := proofErase_eta_body hΓ hD hfPi hnf
    rw [Eb] at Eη
    apply ComputedJointCheckDepth.etaBodyL (hsort W SD)
    simpa only [ProofShape.subst, etaArgument_subst, ProofShape.lift_subst_lift] using
      ihB hΓD hbody hη (by simp only [proofEraseCtx, EΓ, ED]) Ebody Eη (hcons W)
  | etaBodyR SD HB ihB =>
    intro Γ a b A Δ' τ hΓ ha hb EΓ Ea Eb W
    obtain ⟨D, body, rfl, hn, ED, Ebody⟩ := erase_lam_inv Eb
    obtain ⟨⟨_, hD⟩, C, hbody⟩ := hb.lam_inv henv hΓ
    have hD := domain_sort_raw SD hΓ hD EΓ ED
    have hΓD : OnCtx (D :: Γ) (env.IsType univs) := ⟨hΓ, _, hD⟩
    have hfPi := ha.defeqU_r henv hΓ (hb.uniqU henv hΓ (HasType.lam hD hbody))
    have hnf : ¬ IsProof Γ a := by
      rintro ⟨P, hfP, hP⟩
      exact hn ⟨P, hb.defeqU_r henv hΓ (ha.uniqU henv hΓ hfP), hP⟩
    have hη : env.HasType univs (D :: Γ) (.app a.lift (.bvar 0)) C := by
      simpa only [lift, VExpr.liftN, inst_liftN_bvar] using HasType.app (hfPi.weak henv (B := D)) (.bvar .zero)
    have Eη := proofErase_eta_body hΓ hD hfPi hnf
    rw [Ea] at Eη
    apply ComputedJointCheckDepth.etaBodyR (hsort W SD)
    simpa only [ProofShape.subst, etaArgument_subst, ProofShape.lift_subst_lift] using
      ihB hΓD hη hbody (by simp only [proofEraseCtx, EΓ, ED]) Eη Ebody (hcons W)
  | @structFields n Δ family info ls ps fields major hi hx hp hf hadm Hfields ihfields =>
    intro Γ a b A Δ' τ hΓ ha hb EΓ Ea Eb W
    have HE := common_raw hstep (.structFields hi hx hp hf hadm (fun i hj hn => (Hfields i hj hn).forget)) hΓ ha hb EΓ Ea Eb
    simp only [ProofShape.subst_mkApps, ProofShape.subst, List.map_append]
    apply ComputedJointCheckDepth.structFields hi hx (by simpa only [List.length_map] using hp)
      (by simpa only [List.length_map] using hf) hadm
    intro i hj hn
    have hj₀ : i < fields.length := by simpa only [List.length_map] using hj
    have hn₀ : fields[i] ≠ .proof := by
      intro HE
      apply hn
      simp only [List.getElem_map, HE, ProofShape.subst]
    obtain ⟨x, X, hxt, hpt, Ex⟩ := proofErase_equal_structure_field_realize hΓ HE hi hx hp hf hadm Ea hj₀
    have hnx : ¬ IsProof Γ x := fun H => hn₀ (Ex.symm.trans (proofErase_eq_proof.2 H))
    have hnp : ¬ IsProof Γ (.proj family i b) := by
      rintro ⟨P, hpP, hP⟩
      exact hnx ⟨P, hxt.defeqU_r henv hΓ (hpt.uniqU henv hΓ hpP), hP⟩
    have Ep : proofErase Γ (.proj family i b) = .proj family i major := by
      rw [show proofErase Γ (.proj family i b) = .proj family i (proofErase Γ b) from if_neg hnp, Eb]
    simpa only [List.getElem_map, ProofShape.subst] using
      ihfields i hj₀ hn₀ hΓ hxt hpt EΓ Ex Ep W
  | compute Ra Rb HC ih =>
    intro Γ a b A Δ' τ hΓ ha hb EΓ Ea Eb W
    obtain ⟨a', HA, EA⟩ := proofErase_scoped_compute_realize hstep hΓ ha EΓ Ea Ra
    obtain ⟨b', HB, EB⟩ := proofErase_scoped_compute_realize hstep hΓ hb EΓ Eb Rb
    exact .compute (hcompute Ra hΓ ha EΓ Ea W)
      (hcompute Rb hΓ hb EΓ Eb W)
      (ih hΓ HA.hasType.2 HB.hasType.2 EΓ EA EB W)
  | symm HC ih =>
    intro Γ a b A Δ' τ hΓ ha hb EΓ Ea Eb W
    exact .symm (ih hΓ hb ha EΓ Eb Ea W)
  | carrierChecked HC ih =>
    intro Γ a b A Δ' τ hΓ ha hb EΓ Eα Ea Eb W
    exact .carrierChecked (ih hΓ ha hb EΓ Ea Eb W)
  | carrierSubsingleton HS =>
    intro Γ a b A Δ' τ hΓ ha hb EΓ Eα Ea Eb W
    exact .carrierSubsingleton (HS.subst τ)
  | carrierSymm HC ih =>
    intro Γ a b A Δ' τ hΓ ha hb EΓ Eα Ea Eb W
    exact .carrierSymm (ih hΓ hb ha EΓ Eα Eb Ea W)
  | carrierCompute RC HC ih =>
    intro Γ a b A Δ' τ hΓ ha hb EΓ Eα Ea Eb W
    obtain ⟨u, hA⟩ := ha.isType henv hΓ
    obtain ⟨A', HE, EA⟩ := proofErase_scoped_compute_realize hstep hΓ hA EΓ Eα RC
    exact .carrierCompute (hcompute RC hΓ hA EΓ Eα W)
      (ih hΓ (HE.defeq ha) (HE.defeq hb) EΓ EA Ea Eb W)
  | carrierReduce Ra Rb HC ih =>
    intro Γ a b A Δ' τ hΓ ha hb EΓ Eα Ea Eb W
    obtain ⟨a', HA, EA⟩ := proofErase_scoped_compute_realize hstep hΓ ha EΓ Ea Ra
    obtain ⟨b', HB, EB⟩ := proofErase_scoped_compute_realize hstep hΓ hb EΓ Eb Rb
    exact .carrierReduce (hcompute Ra hΓ ha EΓ Ea W)
      (hcompute Rb hΓ hb EΓ Eb W)
      (ih hΓ HA.hasType.2 HB.hasType.2 EΓ Eα EA EB W)
  | carrierFunction SD HC ih =>
    intro Γ a b A Δ' τ hΓ ha hb EΓ Eα Ea Eb W
    obtain ⟨D, C, rfl, _, ED, EC⟩ := erase_forallE_inv Eα
    obtain ⟨_, hPi⟩ := ha.isType henv hΓ
    obtain ⟨⟨_, hD⟩, _, _⟩ := hPi.forallE_inv henv
    have hD := domain_sort_raw SD hΓ hD EΓ ED
    have hΓD : OnCtx (D :: Γ) (env.IsType univs) := ⟨hΓ, _, hD⟩
    by_cases hpa : IsProof Γ a
    · obtain ⟨P, haP, hP⟩ := hpa
      have hpb : IsProof Γ b := ⟨P, hb.defeqU_r henv hΓ (ha.uniqU henv hΓ haP), hP⟩
      rw [← Ea, ← Eb, proofErase_eq_proof.2 ⟨P, haP, hP⟩, proofErase_eq_proof.2 hpb]
      exact .carrierChecked (.leaf .refl)
    have hpb : ¬ IsProof Γ b := by
      rintro ⟨P, hbP, hP⟩
      exact hpa ⟨P, ha.defeqU_r henv hΓ (hb.uniqU henv hΓ hbP), hP⟩
    have hfa : env.HasType univs (D :: Γ) (.app a.lift (.bvar 0)) C := by
      simpa only [lift, VExpr.liftN, inst_liftN_bvar] using HasType.app (ha.weak henv) (.bvar .zero)
    have hfb : env.HasType univs (D :: Γ) (.app b.lift (.bvar 0)) C := by
      simpa only [lift, VExpr.liftN, inst_liftN_bvar] using HasType.app (hb.weak henv) (.bvar .zero)
    have Efa := proofErase_eta_body hΓ hD ha hpa
    have Efb := proofErase_eta_body hΓ hD hb hpb
    rw [Ea] at Efa
    rw [Eb] at Efb
    apply ComputedJointCheckDepth.carrierFunction (hsort W SD)
    simpa only [ProofShape.subst, etaArgument_subst, ProofShape.lift_subst_lift] using
      ih hΓD hfa hfb (by simp only [proofEraseCtx, EΓ, ED]) EC Efa Efb (hcons W)
  | @carrierIntro family info ls n Δ sa sb ps hi hx hp hadm Hfields ihfields =>
    intro Γ a b A Δ' τ hΓ ha hb EΓ Eα Ea Eb W
    have HE := carrier_raw hstep (.carrierIntro hi hx hp hadm (fun i hj hn => (Hfields i hj hn).forget)) hΓ ha hb EΓ Eα Ea Eb
    obtain ⟨args, rfl, Eargs⟩ := proofErase_const_spine_inv Eα
    have hlen : args.length = info.nparams := by
      have HH := congrArg List.length Eargs
      simp only [List.length_map] at HH
      omega
    have hexpa := (StructureReplay.expansion_typed_iff henv hΓ hi hlen hx ha).2 hadm
    simp only [ProofShape.subst_mkApps, ProofShape.subst]
    apply ComputedJointCheckDepth.carrierIntro hi hx (by simpa only [List.length_map] using hp) hadm
    intro i hj hn
    obtain ⟨F, hia, hib⟩ := structure_equal_projection_typings hΓ HE hexpa hj
    have hpa : ¬ IsProof Γ (.proj family i a) := fun H =>
      hn (StructureReplay.ProofField.of_projection hΓ hi hlen hj hexpa H)
    have hpb : ¬ IsProof Γ (.proj family i b) := by
      rintro ⟨P, hibP, hP⟩
      exact hpa ⟨P, hia.defeqU_r henv hΓ (hib.uniqU henv hΓ hibP), hP⟩
    have Epa : proofErase Γ (.proj family i a) = .proj family i sa := by
      rw [show proofErase Γ (.proj family i a) = .proj family i (proofErase Γ a) from if_neg hpa, Ea]
    have Epb : proofErase Γ (.proj family i b) = .proj family i sb := by
      rw [show proofErase Γ (.proj family i b) = .proj family i (proofErase Γ b) from if_neg hpb, Eb]
    exact ihfields i hj hn hΓ hia hib EΓ Epa Epb W
  | @carrierNested family info ls doms result n Δ ps sa sb hi hx hp hadm HT Hfields ihfields =>
    intro Γ a b A Δ' τ hΓ ha hb EΓ Eα Ea Eb W
    have HE := carrier_raw hstep (.carrierNested hi hx hp hadm HT (fun i hj hn => (Hfields i hj hn).forget)) hΓ ha hb EΓ Eα Ea Eb
    obtain ⟨args, rfl, Eargs⟩ := proofErase_const_spine_inv Eα
    have hlen : args.length = info.nparams := by
      have HH := congrArg List.length Eargs
      simp only [List.length_map] at HH
      omega
    have hexpa := (StructureReplay.expansion_typed_iff henv hΓ hi hlen hx ha).2 hadm
    simp only [ProofShape.subst_mkApps, ProofShape.subst]
    apply ComputedJointCheckDepth.carrierNested hi hx (by simpa only [List.length_map] using hp) hadm HT
    intro i hj hn
    obtain ⟨F, hia, hib⟩ := structure_equal_projection_typings hΓ HE hexpa hj
    have hpa : ¬ IsProof Γ (.proj family i a) := fun H =>
      hn (StructureReplay.ProofField.of_projection hΓ hi hlen hj hexpa H)
    have hpb : ¬ IsProof Γ (.proj family i b) := by
      rintro ⟨P, hibP, hP⟩
      exact hpa ⟨P, hia.defeqU_r henv hΓ (hib.uniqU henv hΓ hibP), hP⟩
    obtain ⟨hj', F', hiaF, EF⟩ := proofErase_projection_at_recovered_family hΓ hi HT hia hpa ha
    have hibF := hib.defeqU_r henv hΓ (hia.uniqU henv hΓ hiaF)
    have EF' : proofErase Γ F' = projectionType family info doms i hj' ps sa := by
      simpa only [projectionType, List.map_take, ← Eargs, Ea] using EF
    have Epa : proofErase Γ (.proj family i a) = .proj family i sa := by
      rw [show proofErase Γ (.proj family i a) = .proj family i (proofErase Γ a) from if_neg hpa, Ea]
    have Epb : proofErase Γ (.proj family i b) = .proj family i sb := by
      rw [show proofErase Γ (.proj family i b) = .proj family i (proofErase Γ b) from if_neg hpb, Eb]
    simpa only [projectionType_subst (args := ps) HT _ (by omega), ProofShape.subst] using
      ihfields i hj hn hΓ hiaF hibF EΓ EF' Epa Epb W


/-- Exact recovery or computed-domain exposure preserves the depth bound. -/
theorem ProofShape.ComputedJointCheckDepth.transport
    (Transport : List ProofShape → List ProofShape → ProofShape.Subst → Prop)
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hcons : ∀ {Δ Δ' τ A}, Transport Δ Δ' τ → Transport (A :: Δ) (A.subst τ :: Δ') τ.lift)
    (hsort : ∀ {Δ Δ' τ A u}, Transport Δ Δ' τ → DomainSort Δ A u → DomainSort Δ' (A.subst τ) u)
    (hcompute : ∀ {Γ Δ Δ' τ e T source out}, ScopedCompute Step Δ source out →
      OnCtx Γ (env.IsType univs) → env.HasType univs Γ e T →
      proofEraseCtx Γ = Δ → proofErase Γ e = source → Transport Δ Δ' τ →
      ScopedCompute Target Δ' (source.subst τ) (out.subst τ))
    (happ : ∀ {Γ Δ' τ f D C A B}, OnCtx Γ (env.IsType univs) →
      env.HasType univs Γ f (.forallE D C) → ¬ IsProof Γ f →
      ScopedTypeRecovery Step (proofEraseCtx Γ) (proofErase Γ f) (.forallE A B) →
      Transport (proofEraseCtx Γ) Δ' τ →
      ScopedTypeRecovery Target Δ' ((proofErase Γ f).subst τ)
        (.forallE (A.subst τ) (B.subst τ.lift)) ∨
      ∃ body, ScopedCompute Target Δ' ((proofErase Γ f).subst τ) (.lam (A.subst τ) body))
    (H : ComputedJointCheckDepth Step n Δ kind sa sb) : ComputedJointTransportDepthResult Transport Target n Δ kind sa sb := by
  apply H.transport_application Transport hstep hcons hsort hcompute
  intro n Γ Δ' τ f x y D C A B g mode hΓ hf _ _ hn R W HF HX
  rcases happ hΓ hf hn R W with HR | ⟨body, RF⟩
  · exact .appCarrier HR HF HX
  · exact .appComputed RF HF HX

end Lean4Lean.VEnv.Strengthening
