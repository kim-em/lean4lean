import Lean4Lean.Theory.Typing.Strengthening.ProofErasureComputedLambdaApplication

/-! # Recursive comparison with computed application domains

All joint comparison and carrier constructors recurse in this family. An
additional application rule reads its carrier from a function computation.
This defines a larger certificate language; equivalence with the old checker
and completeness for declarative equality are not asserted.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params]
namespace ProofShape

/-- Comparison and carrier checking recurse into each other at arbitrary depth.
All previous comparison constructors and carrier constructors are retained. -/
inductive ComputedJointCheck (Step : List ProofShape → ProofShape → ProofShape → Prop) :
    List ProofShape → JointCheckKind → ProofShape → ProofShape → Prop where
  | leaf : ScopedLeaf mode a b → ComputedJointCheck Step Δ (.compare mode) a b
  | app : ComputedJointCheck Step Δ (.compare false) f f' → ComputedJointCheck Step Δ (.compare true) a a' →
      ComputedJointCheck Step Δ (.compare mode) (.app f a) (.app f' a')
  /-- A recovered domain licenses carrier comparison at the argument, while
  the inferred function comparison recursively uses this enlarged language. -/
  | appCarrier : ScopedTypeRecovery Step Δ f (.forallE A B) →
      ComputedJointCheck Step Δ (.compare false) f g → ComputedJointCheck Step Δ (.carrier A) x y →
      ComputedJointCheck Step Δ (.compare mode) (.app f x) (.app g y)
  /-- Read a domain from computation of the left function; both checking
  premises recurse in this same family. -/
  | appComputed : ScopedCompute Step Δ f (.lam A body) →
      ComputedJointCheck Step Δ (.compare false) f g →
      ComputedJointCheck Step Δ (.carrier A) x y →
      ComputedJointCheck Step Δ (.compare mode) (.app f x) (.app g y)
  | proj : ComputedJointCheck Step Δ (.compare false) m m' →
      ComputedJointCheck Step Δ (.compare mode) (.proj s i m) (.proj s i m')
  | lam : ComputedJointCheck Step Δ (.compare false) A A' → ComputedJointCheck Step (A :: Δ) (.compare mode) b b' →
      ComputedJointCheck Step Δ (.compare mode) (.lam A b) (.lam A' b')
  | forallE : ComputedJointCheck Step Δ (.compare false) A A' → ComputedJointCheck Step (A :: Δ) (.compare false) B B' →
      ComputedJointCheck Step Δ (.compare mode) (.forallE A B) (.forallE A' B')
  /-- Equal witnessed sorts align independently supplied domain typings. -/
  | lamSorted : DomainSort Δ A u → DomainSort Δ A' u → ComputedJointCheck Step Δ (.compare true) A A' →
      ComputedJointCheck Step (A :: Δ) (.compare mode) b b' →
      ComputedJointCheck Step Δ (.compare mode) (.lam A b) (.lam A' b')
  /-- Pi domains and codomains are types, so shared witnessed sorts suffice
  for common-mode recursive comparison at both positions. -/
  | forallSorted : DomainSort Δ A u → DomainSort Δ A' u → ComputedJointCheck Step Δ (.compare true) A A' →
      DomainSort (A :: Δ) B v → DomainSort (A :: Δ) B' v →
      ComputedJointCheck Step (A :: Δ) (.compare true) B B' →
      ComputedJointCheck Step Δ (.compare mode) (.forallE A B) (.forallE A' B')
  | lamCommon : ComputedJointCheck Step (A :: Δ) (.compare true) b b' →
      ComputedJointCheck Step Δ (.compare true) (.lam A b) (.lam A' b')
  | etaBodyL : DomainSort Δ A u →
      ComputedJointCheck Step (A :: Δ) (.compare true) b (.app (f.liftN 1) (etaArgument u)) →
      ComputedJointCheck Step Δ (.compare true) (.lam A b) f
  | etaBodyR : DomainSort Δ A u →
      ComputedJointCheck Step (A :: Δ) (.compare true) (.app (f.liftN 1) (etaArgument u)) b →
      ComputedJointCheck Step Δ (.compare true) f (.lam A b)
  /-- Source constructor parameters determine a typed projected expansion.
  Every retained field recursively checks against its projection of the major. -/
  | structFields {family : Name} {info : VProjectionInfo} {ls : List VLevel}
      {ps fields : List ProofShape} {m : ProofShape}
      (hi : env.projections family info) (hx : info.nindices = 0)
      (hp : ps.length = info.nparams) (hf : fields.length = info.numFields)
      (hadm : (info.resultLevel.inst ls).IsNeverZero ∨ StructureReplay.ProofFields env univs info ls)
      (H : ∀ i (h : i < fields.length), fields[i] ≠ .proof →
        ComputedJointCheck Step Δ (.compare true) fields[i] (.proj family i m)) :
      ComputedJointCheck Step Δ (.compare true) (mkApps (.const info.ctorName ls) (ps ++ fields)) m
  /-- Displayed lambda domains align lambda-headed eta in inferred mode. -/
  | etaLams : ComputedJointCheck Step Δ (.compare false) A D →
      (EtaHead (.lam A b) (.lam D f) ∨ EtaHead (.lam D f) (.lam A b)) →
      ComputedJointCheck Step Δ (.compare mode) (.lam A b) (.lam D f)
  | compute : ScopedCompute Step Δ a a' → ScopedCompute Step Δ b b' → ComputedJointCheck Step Δ (.compare mode) a' b' →
      ComputedJointCheck Step Δ (.compare mode) a b
  | symm : ComputedJointCheck Step Δ (.compare mode) a b → ComputedJointCheck Step Δ (.compare mode) b a
  | carrierIntro (hi : env.projections family info) (hx : info.nindices = 0)
      (hp : ps.length = info.nparams)
      (hadm : (info.resultLevel.inst ls).IsNeverZero ∨ StructureReplay.ProofFields env univs info ls)
      (H : ∀ i, i < info.numFields → ¬ StructureReplay.ProofField env univs info ls i →
        ComputedJointCheck Step Δ (.compare true) (.proj family i a) (.proj family i b)) :
      ComputedJointCheck Step Δ (.carrier (mkApps (.const family ls) ps)) a b
  | carrierChecked : ComputedJointCheck Step Δ (.compare true) a b → ComputedJointCheck Step Δ (.carrier A) a b
  | carrierSubsingleton : SubsingletonCarrier A → ComputedJointCheck Step Δ (.carrier A) a b
  | carrierFunction : DomainSort Δ A u →
      ComputedJointCheck Step (A :: Δ) (.carrier B)
        (.app (a.liftN 1) (etaArgument u)) (.app (b.liftN 1) (etaArgument u)) →
      ComputedJointCheck Step Δ (.carrier (.forallE A B)) a b
  | carrierSymm : ComputedJointCheck Step Δ (.carrier A) a b → ComputedJointCheck Step Δ (.carrier A) b a
  | carrierCompute : ScopedCompute Step Δ A A' → ComputedJointCheck Step Δ (.carrier A') a b →
      ComputedJointCheck Step Δ (.carrier A) a b
  | carrierReduce : ScopedCompute Step Δ a a' → ScopedCompute Step Δ b b' →
      ComputedJointCheck Step Δ (.carrier A) a' b' → ComputedJointCheck Step Δ (.carrier A) a b
  | carrierNested (hi : env.projections family info) (hx : info.nindices = 0)
      (hp : ps.length = info.nparams)
      (hadm : (info.resultLevel.inst ls).IsNeverZero ∨ StructureReplay.ProofFields env univs info ls)
      (HT : ProjTele env univs family info ls doms result)
      (H : ∀ i (hj : i < info.numFields), ¬ StructureReplay.ProofField env univs info ls i →
        ComputedJointCheck Step Δ
          (.carrier (projectionType family info doms i (by have := HT.numFields; omega) ps a))
          (.proj family i a) (.proj family i b)) :
      ComputedJointCheck Step Δ (.carrier (mkApps (.const family ls) ps)) a b

/-- The ordinary comparison view of the joint grammar. -/
abbrev ComputedJointCompare (Step : List ProofShape → ProofShape → ProofShape → Prop)
    (Δ : List ProofShape) (mode : Bool) (a b : ProofShape) : Prop :=
  ComputedJointCheck Step Δ (.compare mode) a b

/-- The explicit-carrier view of the same joint grammar. -/
abbrev ComputedJointCarrierGuard (Step : List ProofShape → ProofShape → ProofShape → Prop)
    (Δ : List ProofShape) (A a b : ProofShape) : Prop :=
  ComputedJointCheck Step Δ (.carrier A) a b

/-- Every original joint certificate embeds recursively. -/
theorem JointCheck.computed
    (H : JointCheck Step Δ kind a b) : ComputedJointCheck Step Δ kind a b := by
  induction H with
  | leaf H => exact .leaf H
  | app _ _ ihf ihx => exact .app ihf ihx
  | appCarrier R _ _ ihf ihx => exact .appCarrier R ihf ihx
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

/-- Primitive inclusion preserves the enlarged recursive checker. -/
theorem ComputedJointCheck.mono
    (hstep : ∀ {Δ a b}, Step Δ a b → Step' Δ a b)
    (H : ComputedJointCheck Step Δ kind a b) : ComputedJointCheck Step' Δ kind a b := by
  induction H with
  | leaf H => exact .leaf H
  | app _ _ ihf ihx => exact .app ihf ihx
  | appCarrier R _ _ ihf ihx => exact .appCarrier (R.mono hstep) ihf ihx
  | appComputed R _ _ ihf ihx => exact .appComputed (R.mono hstep) ihf ihx
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
  | compute Ra Rb _ ih => exact .compute (Ra.mono hstep) (Rb.mono hstep) ih
  | symm _ ih => exact .symm ih
  | carrierIntro hi hx hp hadm _ ih => exact .carrierIntro hi hx hp hadm ih
  | carrierChecked _ ih => exact .carrierChecked ih
  | carrierSubsingleton H => exact .carrierSubsingleton H
  | carrierFunction S _ ih => exact .carrierFunction S ih
  | carrierSymm _ ih => exact .carrierSymm ih
  | carrierCompute R _ ih => exact .carrierCompute (R.mono hstep) ih
  | carrierReduce Ra Rb _ ih => exact .carrierReduce (Ra.mono hstep) (Rb.mono hstep) ih
  | carrierNested hi hx hp hadm HT _ ih => exact .carrierNested hi hx hp hadm HT ih

end ProofShape

open ProofShape

/-- The earlier local computed-domain certificate is a special case of this
recursive checker, with both old recursive premises embedded. -/
theorem ComputedLambdaApplication.recursive
    (H : ComputedLambdaApplication Step Δ a b) : ComputedJointCompare Step Δ mode a b := by
  cases H with
  | intro RF HF HX => exact .appComputed RF HF.computed HX.computed

end Lean4Lean.VEnv.Strengthening
