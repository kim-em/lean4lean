import Lean4Lean.Theory.Typing.Strengthening.ProofErasureApplicationComparison

/-! # Mutually recursive comparison and explicit-carrier checking

A single inductive family has comparison and carrier modes. Application
comparison uses carrier checking, and carrier checking uses the same comparison
family again. There is no bound on the number of these alternations.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params]
namespace ProofShape

/-- Ordinary checking modes and explicit-carrier checking share one induction. -/
inductive JointCheckKind where
  | compare : Bool → JointCheckKind
  | carrier : ProofShape → JointCheckKind

/-- Comparison and carrier checking recurse into each other at arbitrary depth.
All previous comparison constructors and carrier constructors are retained. -/
inductive JointCheck (Step : List ProofShape → ProofShape → ProofShape → Prop) :
    List ProofShape → JointCheckKind → ProofShape → ProofShape → Prop where
  | leaf : ScopedLeaf mode a b → JointCheck Step Δ (.compare mode) a b
  | app : JointCheck Step Δ (.compare false) f f' → JointCheck Step Δ (.compare true) a a' →
      JointCheck Step Δ (.compare mode) (.app f a) (.app f' a')
  /-- A recovered domain licenses carrier comparison at the argument, while
  the inferred function comparison recursively uses this enlarged language. -/
  | appCarrier : ScopedTypeRecovery Step Δ f (.forallE A B) →
      JointCheck Step Δ (.compare false) f g → JointCheck Step Δ (.carrier A) x y →
      JointCheck Step Δ (.compare mode) (.app f x) (.app g y)
  | proj : JointCheck Step Δ (.compare false) m m' →
      JointCheck Step Δ (.compare mode) (.proj s i m) (.proj s i m')
  | lam : JointCheck Step Δ (.compare false) A A' → JointCheck Step (A :: Δ) (.compare mode) b b' →
      JointCheck Step Δ (.compare mode) (.lam A b) (.lam A' b')
  | forallE : JointCheck Step Δ (.compare false) A A' → JointCheck Step (A :: Δ) (.compare false) B B' →
      JointCheck Step Δ (.compare mode) (.forallE A B) (.forallE A' B')
  /-- Equal witnessed sorts align independently supplied domain typings. -/
  | lamSorted : DomainSort Δ A u → DomainSort Δ A' u → JointCheck Step Δ (.compare true) A A' →
      JointCheck Step (A :: Δ) (.compare mode) b b' →
      JointCheck Step Δ (.compare mode) (.lam A b) (.lam A' b')
  /-- Pi domains and codomains are types, so shared witnessed sorts suffice
  for common-mode recursive comparison at both positions. -/
  | forallSorted : DomainSort Δ A u → DomainSort Δ A' u → JointCheck Step Δ (.compare true) A A' →
      DomainSort (A :: Δ) B v → DomainSort (A :: Δ) B' v →
      JointCheck Step (A :: Δ) (.compare true) B B' →
      JointCheck Step Δ (.compare mode) (.forallE A B) (.forallE A' B')
  | lamCommon : JointCheck Step (A :: Δ) (.compare true) b b' →
      JointCheck Step Δ (.compare true) (.lam A b) (.lam A' b')
  | etaBodyL : DomainSort Δ A u →
      JointCheck Step (A :: Δ) (.compare true) b (.app (f.liftN 1) (etaArgument u)) →
      JointCheck Step Δ (.compare true) (.lam A b) f
  | etaBodyR : DomainSort Δ A u →
      JointCheck Step (A :: Δ) (.compare true) (.app (f.liftN 1) (etaArgument u)) b →
      JointCheck Step Δ (.compare true) f (.lam A b)
  /-- Source constructor parameters determine a typed projected expansion.
  Every retained field recursively checks against its projection of the major. -/
  | structFields {family : Name} {info : VProjectionInfo} {ls : List VLevel}
      {ps fields : List ProofShape} {m : ProofShape}
      (hi : env.projections family info) (hx : info.nindices = 0)
      (hp : ps.length = info.nparams) (hf : fields.length = info.numFields)
      (hadm : (info.resultLevel.inst ls).IsNeverZero ∨ StructureReplay.ProofFields env univs info ls)
      (H : ∀ i (h : i < fields.length), fields[i] ≠ .proof →
        JointCheck Step Δ (.compare true) fields[i] (.proj family i m)) :
      JointCheck Step Δ (.compare true) (mkApps (.const info.ctorName ls) (ps ++ fields)) m
  /-- Displayed lambda domains align lambda-headed eta in inferred mode. -/
  | etaLams : JointCheck Step Δ (.compare false) A D →
      (EtaHead (.lam A b) (.lam D f) ∨ EtaHead (.lam D f) (.lam A b)) →
      JointCheck Step Δ (.compare mode) (.lam A b) (.lam D f)
  | compute : ScopedCompute Step Δ a a' → ScopedCompute Step Δ b b' → JointCheck Step Δ (.compare mode) a' b' →
      JointCheck Step Δ (.compare mode) a b
  | symm : JointCheck Step Δ (.compare mode) a b → JointCheck Step Δ (.compare mode) b a
  | carrierIntro (hi : env.projections family info) (hx : info.nindices = 0)
      (hp : ps.length = info.nparams)
      (hadm : (info.resultLevel.inst ls).IsNeverZero ∨ StructureReplay.ProofFields env univs info ls)
      (H : ∀ i, i < info.numFields → ¬ StructureReplay.ProofField env univs info ls i →
        JointCheck Step Δ (.compare true) (.proj family i a) (.proj family i b)) :
      JointCheck Step Δ (.carrier (mkApps (.const family ls) ps)) a b
  | carrierChecked : JointCheck Step Δ (.compare true) a b → JointCheck Step Δ (.carrier A) a b
  | carrierSubsingleton : SubsingletonCarrier A → JointCheck Step Δ (.carrier A) a b
  | carrierFunction : DomainSort Δ A u →
      JointCheck Step (A :: Δ) (.carrier B)
        (.app (a.liftN 1) (etaArgument u)) (.app (b.liftN 1) (etaArgument u)) →
      JointCheck Step Δ (.carrier (.forallE A B)) a b
  | carrierSymm : JointCheck Step Δ (.carrier A) a b → JointCheck Step Δ (.carrier A) b a
  | carrierCompute : ScopedCompute Step Δ A A' → JointCheck Step Δ (.carrier A') a b →
      JointCheck Step Δ (.carrier A) a b
  | carrierReduce : ScopedCompute Step Δ a a' → ScopedCompute Step Δ b b' →
      JointCheck Step Δ (.carrier A) a' b' → JointCheck Step Δ (.carrier A) a b
  | carrierNested (hi : env.projections family info) (hx : info.nindices = 0)
      (hp : ps.length = info.nparams)
      (hadm : (info.resultLevel.inst ls).IsNeverZero ∨ StructureReplay.ProofFields env univs info ls)
      (HT : ProjTele env univs family info ls doms result)
      (H : ∀ i (hj : i < info.numFields), ¬ StructureReplay.ProofField env univs info ls i →
        JointCheck Step Δ
          (.carrier (projectionType family info doms i (by have := HT.numFields; omega) ps a))
          (.proj family i a) (.proj family i b)) :
      JointCheck Step Δ (.carrier (mkApps (.const family ls) ps)) a b

/-- The ordinary comparison view of the joint grammar. -/
abbrev JointCompare (Step : List ProofShape → ProofShape → ProofShape → Prop)
    (Δ : List ProofShape) (mode : Bool) (a b : ProofShape) : Prop :=
  JointCheck Step Δ (.compare mode) a b

/-- The explicit-carrier view of the same joint grammar. -/
abbrev JointCarrierGuard (Step : List ProofShape → ProofShape → ProofShape → Prop)
    (Δ : List ProofShape) (A a b : ProofShape) : Prop :=
  JointCheck Step Δ (.carrier A) a b

/-- Every previous scoped comparison embeds structurally, with the same modes,
contexts, and primitive computations. -/
theorem ScopedCompare.joint (H : ScopedCompare Step Δ mode a b) :
    JointCompare Step Δ mode a b := by
  induction H with
  | leaf H => exact .leaf H
  | app _ _ ihf ihx => exact .app ihf ihx
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

/-- Every old carrier guard embeds; its retained comparisons can now use
joint checking on subsequent construction. Static proof fields remain skipped. -/
theorem StructureCarrierGuard.joint (H : StructureCarrierGuard Step Δ A a b) :
    JointCarrierGuard Step Δ A a b := by
  induction H with
  | intro hi hx hp hadm H =>
    apply JointCheck.carrierIntro hi hx hp hadm
    intro i hj hn
    rcases H i hj with HP | HC
    · exact (hn HP).elim
    · exact HC.joint
  | checked H => exact .carrierChecked H.joint
  | subsingleton H => exact .carrierSubsingleton H
  | function S H ih => exact .carrierFunction S ih
  | symm H ih => exact .carrierSymm ih
  | compute R H ih => exact .carrierCompute R ih
  | reduce Ra Rb H ih => exact .carrierReduce Ra Rb ih
  | nested hi hx hp hadm HT H ih => exact .carrierNested hi hx hp hadm HT ih

/-- Every previous recursive application comparison embeds in the joint grammar. -/
theorem ApplicationCompare.joint
    (H : ApplicationCompare Step Δ mode a b) : JointCompare Step Δ mode a b := by
  induction H with
  | leaf H => exact .leaf H
  | app _ _ ihf ihx => exact .app ihf ihx
  | appCarrier R _ HX ihf => exact .appCarrier R ihf HX.joint
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
/-- Primitive inclusion transports recovery, carrier guards and all recursive
comparisons simultaneously. -/
theorem JointCheck.mono
    (hstep : ∀ {Δ a b}, Step Δ a b → Step' Δ a b)
    (H : JointCheck Step Δ kind a b) : JointCheck Step' Δ kind a b := by
  induction H with
  | leaf H => exact .leaf H
  | app _ _ ihf ihx => exact .app ihf ihx
  | appCarrier R _ _ ihf ihx => exact .appCarrier (R.mono hstep) ihf ihx
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
end Lean4Lean.VEnv.Strengthening
