import Lean4Lean.Theory.Typing.Strengthening.ProjectionParallel

/-! # Confluence of closed computation with constructor projections

The parallel diamond uses exact declaration determinism and constructor
rigidity. The only new root overlap selects the same original field on both
sides, using uniqueness of registered projection metadata. No source typing,
normalization or strengthening front is assumed.
-/
namespace Lean4Lean.VEnv.Strengthening.PureObservation
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params] {D : Definitions}

private def ProjectionDiamondBelow (D : Definitions) (n : Nat) : Prop :=
  ∀ {a b c}, sizeOf a < n → ProjectionPar D a b → ProjectionPar D a c →
    ∃ out, ProjectionPar D b out ∧ ProjectionPar D c out

private theorem projection_root_join (hr : ConstructorObservation.ConstructorRigid D)
    (IH : ProjectionDiamondBelow D (sizeOf (VExpr.proj family index (mkApps (.const info.ctorName ls) args))))
    (hi : env.projections family info) (hl : args.length = info.nparams + info.numFields)
    (hg : args[info.nparams + index]? = some field) (RF : ProjectionPar D field field')
    (R : ProjectionPar D (.proj family index (mkApps (.const info.ctorName ls) args)) out) :
    ∃ join, ProjectionPar D field' join ∧ ProjectionPar D out join := by
  have hf : sizeOf field < sizeOf (VExpr.proj family index (mkApps (.const info.ctorName ls) args)) := by
    have h := sizeOf_mkApps_arg (f := .const info.ctorName ls) (List.mem_of_getElem? hg)
    simp; omega
  generalize he : VExpr.proj family index (mkApps (.const info.ctorName ls) args) = source at R
  cases R with
  | proj RM =>
    cases he
    obtain ⟨args', rfl, HA⟩ := RM.rigid_spine_paths (hr _ _ hi)
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
  | bvar | sort | const | delta | app | lam | forallE | beta => cases he

private theorem projection_diamond_aux (hd : D.Deterministic)
    (hr : ConstructorObservation.ConstructorRigid D) : ∀ n, ProjectionDiamondBelow D n := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro a b c hn R1 R2
    have IH : ProjectionDiamondBelow D (sizeOf a) := ih _ hn
    cases R1 with
    | bvar => cases R2; exact ⟨_, .bvar, .bvar⟩
    | sort => cases R2; exact ⟨_, .sort, .sort⟩
    | const =>
      cases R2 with
      | const => exact ⟨_, .const, .const⟩
      | delta H => exact ⟨_, .delta H, .refl _⟩
    | delta H =>
      cases R2 with
      | const => exact ⟨_, .refl _, .delta H⟩
      | delta H' => cases hd H H'; exact ⟨_, .refl _, .refl _⟩
    | app Rf Ra =>
      cases R2 with
      | app Rf' Ra' =>
        obtain ⟨f, HF, HF'⟩ := IH (by simp; omega) Rf Rf'
        obtain ⟨a, HA, HA'⟩ := IH (by simp; omega) Ra Ra'
        exact ⟨.app f a, .app HF HA, .app HF' HA'⟩
      | beta Rb' Ra' =>
        cases Rf with
        | lam RA Rb =>
          obtain ⟨b, HB, HB'⟩ := IH (by simp; omega) Rb Rb'
          obtain ⟨a, HA, HA'⟩ := IH (by simp; omega) Ra Ra'
          exact ⟨b.inst a, .beta HB HA, HB'.inst HA'⟩
    | beta Rb Ra =>
      cases R2 with
      | app Rf' Ra' =>
        cases Rf' with
        | lam RA' Rb' =>
          obtain ⟨b, HB, HB'⟩ := IH (by simp; omega) Rb Rb'
          obtain ⟨a, HA, HA'⟩ := IH (by simp; omega) Ra Ra'
          exact ⟨b.inst a, HB.inst HA, .beta HB' HA'⟩
      | beta Rb' Ra' =>
        obtain ⟨b, HB, HB'⟩ := IH (by simp; omega) Rb Rb'
        obtain ⟨a, HA, HA'⟩ := IH (by simp; omega) Ra Ra'
        exact ⟨b.inst a, HB.inst HA, HB'.inst HA'⟩
    | lam RA Rb =>
      cases R2 with
      | lam RA' Rb' =>
        obtain ⟨A, HA, HA'⟩ := IH (by simp; omega) RA RA'
        obtain ⟨b, HB, HB'⟩ := IH (by simp; omega) Rb Rb'
        exact ⟨.lam A b, .lam HA HB, .lam HA' HB'⟩
    | forallE RA RB =>
      cases R2 with
      | forallE RA' RB' =>
        obtain ⟨A, HA, HA'⟩ := IH (by simp; omega) RA RA'
        obtain ⟨B, HB, HB'⟩ := IH (by simp; omega) RB RB'
        exact ⟨.forallE A B, .forallE HA HB, .forallE HA' HB'⟩
    | proj RM =>
      cases R2 with
      | proj RM' =>
        obtain ⟨m, HM, HM'⟩ := IH (by simp; omega) RM RM'
        exact ⟨.proj _ _ m, .proj HM, .proj HM'⟩
      | projIota hi hl hg RF =>
        obtain ⟨join, H1, H2⟩ := projection_root_join hr IH hi hl hg RF (.proj RM)
        exact ⟨join, H2, H1⟩
    | projIota hi hl hg RF => exact projection_root_join hr IH hi hl hg RF R2

/-- Exact parallel diamond including constructor projection, under the actual
metadata's uniqueness and non-unfolding constructor heads. -/
theorem ProjectionPar.diamond (hd : D.Deterministic)
    (hr : ConstructorObservation.ConstructorRigid D)
    (R1 : ProjectionPar D a b) (R2 : ProjectionPar D a c) :
    ∃ out, ProjectionPar D b out ∧ ProjectionPar D c out :=
  projection_diamond_aux hd hr (sizeOf a + 1) (by omega) R1 R2

private theorem projection_parallel_map (f : VExpr → VExpr)
    (hf : ∀ {a b}, ProjectionPar D a b → ProjectionPar D (f a) (f b))
    (R : ReflTransGen (ProjectionPar D) a b) : ReflTransGen (ProjectionPar D) (f a) (f b) := by
  induction R with
  | rfl => exact .rfl
  | tail _ R ih => exact ih.tail (hf R)

private theorem projection_parallel_map2 (f : VExpr → VExpr → VExpr)
    (hf : ∀ {a b c d}, ProjectionPar D a b → ProjectionPar D c d → ProjectionPar D (f a c) (f b d))
    (R1 : ReflTransGen (ProjectionPar D) a b) (R2 : ReflTransGen (ProjectionPar D) c d) :
    ReflTransGen (ProjectionPar D) (f a c) (f b d) :=
  (projection_parallel_map (fun x => f x c) (fun R => hf R (.refl _)) R1).trans
    (projection_parallel_map (fun x => f b x) (fun R => hf (.refl _) R) R2)

private theorem compute_toProjectionParallel (R : Compute D e e') :
    ReflTransGen (ProjectionPar D) e e' := by
  induction R with
  | refl => exact .rfl
  | trans _ _ ih1 ih2 => exact ih1.trans ih2
  | beta => exact .tail .rfl (.beta (.refl _) (.refl _))
  | delta H => exact .tail .rfl (.delta H)
  | app _ _ ih1 ih2 => exact projection_parallel_map2 _ ProjectionPar.app ih1 ih2
  | lam _ _ ih1 ih2 => exact projection_parallel_map2 _ ProjectionPar.lam ih1 ih2
  | forallE _ _ ih1 ih2 => exact projection_parallel_map2 _ ProjectionPar.forallE ih1 ih2
  | proj _ ih => exact projection_parallel_map _ ProjectionPar.proj ih

/-- Finite computation, including projection roots, serializes into parallel
steps without changing its endpoints. -/
theorem ProjectionCompute.toParallel (R : ProjectionCompute D e e') :
    ReflTransGen (ProjectionPar D) e e' := by
  induction R with
  | base R => exact compute_toProjectionParallel R
  | trans _ _ ih1 ih2 => exact ih1.trans ih2
  | projIota hi hl hg => exact .tail .rfl (.projIota hi hl hg (.refl _))
  | app _ _ ih1 ih2 => exact projection_parallel_map2 _ ProjectionPar.app ih1 ih2
  | lam _ _ ih1 ih2 => exact projection_parallel_map2 _ ProjectionPar.lam ih1 ih2
  | forallE _ _ ih1 ih2 => exact projection_parallel_map2 _ ProjectionPar.forallE ih1 ih2
  | proj _ ih => exact projection_parallel_map _ ProjectionPar.proj ih

private theorem projection_parallel_toCompute (R : ReflTransGen (ProjectionPar D) e e') :
    ProjectionCompute D e e' := by
  induction R with
  | rfl => exact .base .refl
  | tail _ R ih => exact ih.trans R.toCompute

private theorem projection_parallel_strip (hd : D.Deterministic)
    (hr : ConstructorObservation.ConstructorRigid D) (R1 : ProjectionPar D a b)
    (R2 : ReflTransGen (ProjectionPar D) a c) :
    ∃ out, ReflTransGen (ProjectionPar D) b out ∧ ProjectionPar D c out := by
  induction R2 with
  | rfl => exact ⟨b, .rfl, R1⟩
  | tail _ R ih =>
    obtain ⟨out0, HB, HC⟩ := ih
    obtain ⟨out, R', HC'⟩ := R.diamond hd hr HC
    exact ⟨out, HB.tail HC', R'⟩

private theorem projection_parallel_confluent (hd : D.Deterministic)
    (hr : ConstructorObservation.ConstructorRigid D)
    (R1 : ReflTransGen (ProjectionPar D) a b) (R2 : ReflTransGen (ProjectionPar D) a c) :
    ∃ out, ReflTransGen (ProjectionPar D) b out ∧ ReflTransGen (ProjectionPar D) c out := by
  induction R1 with
  | rfl => exact ⟨c, R2, .rfl⟩
  | tail _ R ih =>
    obtain ⟨out0, HB, HC⟩ := ih
    obtain ⟨out, RB, RC⟩ := projection_parallel_strip hd hr R HB
    exact ⟨out, RB, HC.tail RC⟩

/-- Arbitrary raw finite beta/delta/projection computations join exactly under
fixed-universe determinism and non-unfolding constructor heads. -/
theorem ProjectionCompute.confluent (hd : D.Deterministic)
    (hr : ConstructorObservation.ConstructorRigid D)
    (R1 : ProjectionCompute D a b) (R2 : ProjectionCompute D a c) :
    ∃ out, ProjectionCompute D b out ∧ ProjectionCompute D c out := by
  obtain ⟨out, HB, HC⟩ := projection_parallel_confluent hd hr R1.toParallel R2.toParallel
  exact ⟨out, projection_parallel_toCompute HB, projection_parallel_toCompute HC⟩

/-- The stored-definition and selected-structure collection satisfies all the
hypotheses of beta/delta/projection confluence. -/
theorem ProjectionCompute.registeredStructure_confluent
    (R1 : ProjectionCompute (RegisteredStructure.definitions
      (Definitions.ofEnv env univs henv)) a b)
    (R2 : ProjectionCompute (RegisteredStructure.definitions
      (Definitions.ofEnv env univs henv)) a c) :
    ∃ out, ProjectionCompute (RegisteredStructure.definitions
      (Definitions.ofEnv env univs henv)) b out ∧
      ProjectionCompute (RegisteredStructure.definitions
        (Definitions.ofEnv env univs henv)) c out :=
  R1.confluent (fun H1 H2 => RegisteredStructure.definitions_ofEnv_unique H1 H2)
    (RegisteredStructure.definitions_rigid ConstructorObservation.ConstructorRigid.ofEnv) R2

end Lean4Lean.VEnv.Strengthening.PureObservation
