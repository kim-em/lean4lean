import Lean4Lean.Theory.Typing.Strengthening.SeparatedPatternMatching

/-! # Confluence of closed computation with separated ordinary patterns

Fixed pattern structure is preserved away from a rule's root. At the root,
pattern uniqueness identifies both rules and smaller capture computations join.
Together with beta, delta and projections this gives raw separated confluence,
and typed confluence of the original stored/selected-structure collection.
Actual singleton prefixes and equivalent-universe closure are outside this result.
-/
namespace Lean4Lean.VEnv.Strengthening.PureObservation
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params] {D : Definitions}

private def SeparatedDiamondBelow (D : Definitions) (n : Nat) : Prop :=
  ∀ {a b c}, sizeOf a < n → SeparatedPar D a b → SeparatedPar D a c →
    ∃ out, SeparatedPar D b out ∧ SeparatedPar D c out

private theorem separated_projection_root_join (hr : ∀ {c}, env.Rigid c → ∀ levels rhs, ¬ D.unfolds c levels rhs)
    (IH : SeparatedDiamondBelow D (sizeOf (VExpr.proj family index (mkApps (.const info.ctorName ls) args))))
    (hi : env.projections family info) (hl : args.length = info.nparams + info.numFields)
    (hg : args[info.nparams + index]? = some field) (RF : SeparatedPar D field field')
    (R : SeparatedPar D (.proj family index (mkApps (.const info.ctorName ls) args)) out) :
    ∃ join, SeparatedPar D field' join ∧ SeparatedPar D out join := by
  have hf : sizeOf field < sizeOf (VExpr.proj family index (mkApps (.const info.ctorName ls) args)) := by
    have h := sizeOf_mkApps_arg (f := .const info.ctorName ls) (List.mem_of_getElem? hg)
    simp; omega
  generalize he : VExpr.proj family index (mkApps (.const info.ctorName ls) args) = source at R
  cases R with
  | proj RM =>
    cases he
    obtain ⟨args', rfl, HA⟩ := RM.rigid_spine_paths (projection_ctor_rigid hi) (hr (projection_ctor_rigid hi))
    obtain ⟨field₁, hg₁, RF₁⟩ := forall₂_selected HA hg
    obtain ⟨join, H1, H2⟩ := IH hf RF RF₁
    exact ⟨join, H1, .projIota hi (HA.length_eq.symm.trans hl) hg₁ H2⟩
  | projIota hi' hl' hg' RF' =>
    obtain ⟨hfamily, hindex, hmajor⟩ := VExpr.proj.inj he
    cases hfamily
    cases hindex
    cases henv.ordered.projections_unique hi hi'
    have hargs := congrArg getAppArgs hmajor
    simp only [getAppArgs_mkApps, getAppArgs, List.nil_append] at hargs
    cases hargs
    cases Option.some.inj (hg.symm.trans hg')
    exact IH hf RF RF'
  | pattern _ hm _ _ _ => rw [← he] at hm; cases hm
  | bvar | sort | const | delta | app | lam | forallE | beta => cases he

private theorem separated_capture_join {p : Pattern} {source : VExpr}
    {captures captures1 captures2 : p.Path → VExpr}
    (IH : SeparatedDiamondBelow D (sizeOf source))
    (hm : p.Matches source levels captures)
    (H1 : ∀ path, SeparatedPar D (captures path) (captures1 path))
    (H2 : ∀ path, SeparatedPar D (captures path) (captures2 path)) :
    ∃ common : p.Path → VExpr,
      (∀ path, SeparatedPar D (captures1 path) (common path)) ∧
      (∀ path, SeparatedPar D (captures2 path) (common path)) := by
  classical
  have H path := IH (matches_capture_size hm path) (H1 path) (H2 path)
  exact ⟨fun path => Classical.choose (H path),
    fun path => (Classical.choose_spec (H path)).1,
    fun path => (Classical.choose_spec (H path)).2⟩

private theorem separated_pattern_root_join
    (hr : ∀ {c}, env.Rigid c → ∀ levels rhs, ¬ D.unfolds c levels rhs)
    (IH : SeparatedDiamondBelow D (sizeOf source))
    (hp : Pat p r) (hm : p.Matches source levels captures)
    (hc : CheckFromTyping env univs p r levels)
    (hn : ∀ rhs, ¬ D.unfolds p.headConst levels rhs)
    (HC : ∀ path, SeparatedPar D (captures path) (captures' path))
    (R : SeparatedPar D source out) :
    ∃ join, SeparatedPar D (r.1.apply levels captures') join ∧ SeparatedPar D out join := by
  have hf := PatternSkeleton.of_match hr hp hm hn
  have matching {middle capsm} (HM : p.Matches middle levels capsm)
      (HCm : ∀ path, SeparatedPar D (captures path) (capsm path)) :
      ∃ join, SeparatedPar D (r.1.apply levels captures') join ∧ SeparatedPar D middle join := by
    obtain ⟨common, H1, H2⟩ := separated_capture_join IH hm HC HCm
    exact ⟨_, SeparatedPar.apply_pat r.1 H1, .pattern hp HM hc hn H2⟩
  cases R with
  | const => exact matching hm (fun _ => .refl _)
  | delta HD => cases hm; cases hf with | const HF => exact (HF _ HD).elim
  | app RF RA =>
    cases hm with
    | var hm => exact (pat_not_var hp).elim
    | app hmf hma =>
      cases hf with | app hsf hsa =>
        obtain ⟨capsf, HMF, HCF⟩ := RF.preserve_match hp (.appL .refl)
          (by intro he; have h := congrArg sizeOf he; simp at h <;> omega) hmf hsf
        obtain ⟨capsa, HMA, HCA⟩ := RA.preserve_match hp (.appR .refl)
          (by intro he; have h := congrArg sizeOf he; simp at h <;> omega) hma hsa
        exact matching (.app HMF HMA) (fun path => path.casesOn HCF HCA)
  | pattern hp' hm' hc' hn' HC' =>
    obtain ⟨_, _, _, hi, _⟩ := Pattern.matches_inter.1 ⟨⟨_, _, hm'⟩, ⟨_, _, hm⟩⟩
    obtain ⟨rfl, _, ⟨⟩⟩ := pat_uniq hp hp' .refl hi
    obtain ⟨rfl, rfl⟩ := hm.uniq hm'
    obtain ⟨common, H1, H2⟩ := separated_capture_join IH hm HC HC'
    exact ⟨_, SeparatedPar.apply_pat r.1 H1, SeparatedPar.apply_pat r.1 H2⟩
  | beta => cases hm with | var hm | app hm => cases hm
  | bvar | sort | lam | forallE | proj | projIota => cases hm

private theorem separated_diamond_aux (hd : D.Deterministic)
    (hr : ∀ {c}, env.Rigid c → ∀ levels rhs, ¬ D.unfolds c levels rhs) : ∀ n, SeparatedDiamondBelow D n := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro a b c hn R1 R2
    have IH : SeparatedDiamondBelow D (sizeOf a) := ih _ hn
    cases R1 with
    | bvar =>
      cases R2 with
      | bvar => exact ⟨_, .bvar, .bvar⟩
      | pattern _ hm => cases hm
    | sort =>
      cases R2 with
      | sort => exact ⟨_, .sort, .sort⟩
      | pattern _ hm => cases hm
    | const =>
      cases R2 with
      | const => exact ⟨_, .const, .const⟩
      | delta H => exact ⟨_, .delta H, .refl _⟩
      | pattern hp hm hc hn HC => exact ⟨_, .pattern hp hm hc hn HC, .refl _⟩
    | delta H =>
      cases R2 with
      | const => exact ⟨_, .refl _, .delta H⟩
      | delta H' => cases hd H H'; exact ⟨_, .refl _, .refl _⟩
      | pattern _ hm _ hn _ => cases hm; exact (hn _ H).elim
    | app Rf Ra =>
      cases R2 with
      | app Rf' Ra' =>
        obtain ⟨f, HF, HF'⟩ := IH (by simp; omega) Rf Rf'
        obtain ⟨a, HA, HA'⟩ := IH (by simp; omega) Ra Ra'
        exact ⟨.app f a, .app HF HA, .app HF' HA'⟩
      | beta Rb' Ra' =>
        cases Rf with
        | pattern _ hm => cases hm
        | lam RA Rb =>
          obtain ⟨b, HB, HB'⟩ := IH (by simp; omega) Rb Rb'
          obtain ⟨a, HA, HA'⟩ := IH (by simp; omega) Ra Ra'
          exact ⟨b.inst a, .beta HB HA, HB'.inst HA'⟩
      | pattern hp hm hc hn HC =>
        obtain ⟨join, H1, H2⟩ := separated_pattern_root_join hr IH hp hm hc hn HC (.app Rf Ra)
        exact ⟨join, H2, H1⟩
    | beta Rb Ra =>
      cases R2 with
      | app Rf' Ra' =>
        cases Rf' with
        | pattern _ hm => cases hm
        | lam RA' Rb' =>
          obtain ⟨b, HB, HB'⟩ := IH (by simp; omega) Rb Rb'
          obtain ⟨a, HA, HA'⟩ := IH (by simp; omega) Ra Ra'
          exact ⟨b.inst a, HB.inst HA, .beta HB' HA'⟩
      | beta Rb' Ra' =>
        obtain ⟨b, HB, HB'⟩ := IH (by simp; omega) Rb Rb'
        obtain ⟨a, HA, HA'⟩ := IH (by simp; omega) Ra Ra'
        exact ⟨b.inst a, HB.inst HA, HB'.inst HA'⟩
      | pattern _ hm => cases hm with | var hm | app hm => cases hm
    | lam RA Rb =>
      cases R2 with
      | lam RA' Rb' =>
        obtain ⟨A, HA, HA'⟩ := IH (by simp; omega) RA RA'
        obtain ⟨b, HB, HB'⟩ := IH (by simp; omega) Rb Rb'
        exact ⟨.lam A b, .lam HA HB, .lam HA' HB'⟩
      | pattern _ hm => cases hm
    | forallE RA RB =>
      cases R2 with
      | forallE RA' RB' =>
        obtain ⟨A, HA, HA'⟩ := IH (by simp; omega) RA RA'
        obtain ⟨B, HB, HB'⟩ := IH (by simp; omega) RB RB'
        exact ⟨.forallE A B, .forallE HA HB, .forallE HA' HB'⟩
      | pattern _ hm => cases hm
    | proj RM =>
      cases R2 with
      | proj RM' =>
        obtain ⟨m, HM, HM'⟩ := IH (by simp; omega) RM RM'
        exact ⟨.proj _ _ m, .proj HM, .proj HM'⟩
      | projIota hi hl hg RF =>
        obtain ⟨join, H1, H2⟩ := separated_projection_root_join hr IH hi hl hg RF (.proj RM)
        exact ⟨join, H2, H1⟩
      | pattern _ hm => cases hm
    | projIota hi hl hg RF => exact separated_projection_root_join hr IH hi hl hg RF R2
    | pattern hp hm hc hn HC => exact separated_pattern_root_join hr IH hp hm hc hn HC R2

/-- Exact parallel diamond for beta, delta, projections and separated ordinary
patterns. No source typing, termination or strengthening premise is needed. -/
theorem SeparatedPar.diamond (hd : D.Deterministic)
    (hr : ∀ {c}, env.Rigid c → ∀ levels rhs, ¬ D.unfolds c levels rhs)
    (R1 : SeparatedPar D a b) (R2 : SeparatedPar D a c) :
    ∃ out, SeparatedPar D b out ∧ SeparatedPar D c out :=
  separated_diamond_aux hd hr (sizeOf a + 1) (by omega) R1 R2

private theorem separated_parallel_map (f : VExpr → VExpr)
    (hf : ∀ {a b}, SeparatedPar D a b → SeparatedPar D (f a) (f b))
    (R : ReflTransGen (SeparatedPar D) a b) : ReflTransGen (SeparatedPar D) (f a) (f b) := by
  induction R with
  | rfl => exact .rfl
  | tail _ R ih => exact ih.tail (hf R)

private theorem separated_parallel_map2 (f : VExpr → VExpr → VExpr)
    (hf : ∀ {a b c d}, SeparatedPar D a b → SeparatedPar D c d → SeparatedPar D (f a c) (f b d))
    (R1 : ReflTransGen (SeparatedPar D) a b) (R2 : ReflTransGen (SeparatedPar D) c d) :
    ReflTransGen (SeparatedPar D) (f a c) (f b d) :=
  (separated_parallel_map (fun x => f x c) (fun R => hf R (.refl _)) R1).trans
    (separated_parallel_map (fun x => f b x) (fun R => hf (.refl _) R) R2)

private theorem compute_toSeparatedParallel (R : Compute D e e') :
    ReflTransGen (SeparatedPar D) e e' := by
  induction R with
  | refl => exact .rfl
  | trans _ _ ih1 ih2 => exact ih1.trans ih2
  | beta => exact .tail .rfl (.beta (.refl _) (.refl _))
  | delta H => exact .tail .rfl (.delta H)
  | app _ _ ih1 ih2 => exact separated_parallel_map2 _ SeparatedPar.app ih1 ih2
  | lam _ _ ih1 ih2 => exact separated_parallel_map2 _ SeparatedPar.lam ih1 ih2
  | forallE _ _ ih1 ih2 => exact separated_parallel_map2 _ SeparatedPar.forallE ih1 ih2
  | proj _ ih => exact separated_parallel_map _ SeparatedPar.proj ih

/-- Finite computation, including projection roots, serializes into parallel
steps without changing its endpoints. -/
private theorem projection_toSeparatedParallel (R : ProjectionCompute D e e') :
    ReflTransGen (SeparatedPar D) e e' := by
  induction R with
  | base R => exact compute_toSeparatedParallel R
  | trans _ _ ih1 ih2 => exact ih1.trans ih2
  | projIota hi hl hg => exact .tail .rfl (.projIota hi hl hg (.refl _))
  | app _ _ ih1 ih2 => exact separated_parallel_map2 _ SeparatedPar.app ih1 ih2
  | lam _ _ ih1 ih2 => exact separated_parallel_map2 _ SeparatedPar.lam ih1 ih2
  | forallE _ _ ih1 ih2 => exact separated_parallel_map2 _ SeparatedPar.forallE ih1 ih2
  | proj _ ih => exact separated_parallel_map _ SeparatedPar.proj ih

/-- Every finite separated computation serializes into parallel steps. -/
theorem SeparatedPatternCompute.toParallel (R : SeparatedPatternCompute D e e') :
    ReflTransGen (SeparatedPar D) e e' := by
  induction R with
  | base R => exact projection_toSeparatedParallel R
  | trans _ _ ih1 ih2 => exact ih1.trans ih2
  | pattern hp hm hc hn => exact .tail .rfl (.pattern hp hm hc hn (fun _ => .refl _))
  | app _ _ ih1 ih2 => exact separated_parallel_map2 _ SeparatedPar.app ih1 ih2
  | lam _ _ ih1 ih2 => exact separated_parallel_map2 _ SeparatedPar.lam ih1 ih2
  | forallE _ _ ih1 ih2 => exact separated_parallel_map2 _ SeparatedPar.forallE ih1 ih2
  | proj _ ih => exact separated_parallel_map _ SeparatedPar.proj ih

private theorem separated_parallel_toCompute (R : ReflTransGen (SeparatedPar D) e e') :
    SeparatedPatternCompute D e e' := by
  induction R with
  | rfl => exact .base (.base .refl)
  | tail _ R ih => exact ih.trans R.toCompute

private theorem separated_parallel_strip (hd : D.Deterministic)
    (hr : ∀ {c}, env.Rigid c → ∀ levels rhs, ¬ D.unfolds c levels rhs) (R1 : SeparatedPar D a b)
    (R2 : ReflTransGen (SeparatedPar D) a c) :
    ∃ out, ReflTransGen (SeparatedPar D) b out ∧ SeparatedPar D c out := by
  induction R2 with
  | rfl => exact ⟨b, .rfl, R1⟩
  | tail _ R ih =>
    obtain ⟨out0, HB, HC⟩ := ih
    obtain ⟨out, R', HC'⟩ := R.diamond hd hr HC
    exact ⟨out, HB.tail HC', R'⟩

private theorem separated_parallel_confluent (hd : D.Deterministic)
    (hr : ∀ {c}, env.Rigid c → ∀ levels rhs, ¬ D.unfolds c levels rhs)
    (R1 : ReflTransGen (SeparatedPar D) a b) (R2 : ReflTransGen (SeparatedPar D) a c) :
    ∃ out, ReflTransGen (SeparatedPar D) b out ∧ ReflTransGen (SeparatedPar D) c out := by
  induction R1 with
  | rfl => exact ⟨c, R2, .rfl⟩
  | tail _ R ih =>
    obtain ⟨out0, HB, HC⟩ := ih
    obtain ⟨out, RB, RC⟩ := separated_parallel_strip hd hr R HB
    exact ⟨out, RB, HC.tail RC⟩

/-- Raw finite computation with separated ordinary patterns joins exactly under
fixed-universe declaration determinism and preservation of every rigid head. -/
theorem SeparatedPatternCompute.confluent (hd : D.Deterministic)
    (hr : ∀ {c}, env.Rigid c → ∀ levels rhs, ¬ D.unfolds c levels rhs)
    (R1 : SeparatedPatternCompute D a b) (R2 : SeparatedPatternCompute D a c) :
    ∃ out, SeparatedPatternCompute D b out ∧ SeparatedPatternCompute D c out := by
  obtain ⟨out, HB, HC⟩ := separated_parallel_confluent hd hr R1.toParallel R2.toParallel
  exact ⟨out, separated_parallel_toCompute HB, separated_parallel_toCompute HC⟩

/-- Typed ordinary-pattern computation over the actual stored-definition and
selected-structure collection is confluent. Overlapping patterns are first
simulated in the separated presentation; its raw diamond supplies the join. -/
theorem PatternCompute.registeredStructure_confluent
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : VExpr.WF env univs Γ a)
    (R1 : PatternCompute (RegisteredStructure.definitions (Definitions.ofEnv env univs henv)) a b)
    (R2 : PatternCompute (RegisteredStructure.definitions (Definitions.ofEnv env univs henv)) a c) :
    ∃ out, PatternCompute (RegisteredStructure.definitions (Definitions.ofEnv env univs henv)) b out ∧
      PatternCompute (RegisteredStructure.definitions (Definitions.ofEnv env univs henv)) c out :=
  PatternCompute.confluent_of_separated hcon
    (fun H1 H2 => H1.confluent (fun H1 H2 => RegisteredStructure.definitions_ofEnv_unique H1 H2)
      (fun hrig _ _ => RegisteredStructure.definitions_ofEnv_no_rigid hrig) H2)
    hΓ ht R1 R2

end Lean4Lean.VEnv.Strengthening.PureObservation
