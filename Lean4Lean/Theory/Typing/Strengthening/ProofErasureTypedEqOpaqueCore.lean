import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypedEqCoreExclusion
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureOpaqueCoreSimulation

/-! # Typed opaque simulation for Eq heads at arbitrary arity

An unsaturated Eq prefix can be inspected by an untyped visible pattern.
Actual source typing excludes the complete Eq root instead: its major erases
to proof. Other visible patterns cannot inspect a marked Eq-headed prefix.
The simulation therefore retains a typed source at every recursive core step.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private head_lift from Lean4Lean.Theory.Typing.Strengthening.ProofErasureOpaqueVariants
open private typed_eq_pattern_no_match
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypedEqCoreExclusion
variable [Params] {D : Definitions} {Guard : ProofShape → ProofShape → Prop}

omit [Params] in
private theorem head_spine (H : e.constHead = some c) :
    ∃ ls args, e = ProofShape.mkApps (.const c ls) args := by
  induction e with
  | const d ls => cases Option.some.inj H; exact ⟨ls, [], rfl⟩
  | app f x ih _ =>
    obtain ⟨ls, args, rfl⟩ := ih H
    exact ⟨ls, args ++ [x], ProofShape.mkApps_snoc.symm⟩
  | proof | bvar | sort | lam | forallE | proj => cases H

omit [Params] in
/-- Substitution cannot change an existing constant head. -/
theorem ProofShape.const_head_subst {e : ProofShape} (H : e.constHead = some c) :
    (e.subst τ).constHead = some c := by
  induction e with
  | const => exact H
  | app _ _ ih _ => exact ih H
  | proof | bvar | sort | lam | forallE | proj => cases H

/-- Ordinary level-core paths preserve every actually typed Eq head,
including unsaturated and oversaturated spines. Typing is used at the selected
root, so no assumption about the ancestry or position of the major is needed. -/
theorem ProofShape.Compute.typed_eq_head
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hD : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (HT : TypedSource Δ e) (HH : e.constHead = some ``Eq.rec)
    (R : ProofShape.Compute (ErasedLevelCore D) e out) : out.constHead = some ``Eq.rec := by
  obtain ⟨ls, args, rfl⟩ := head_spine HH
  have RS := R.scoped (Δ := Δ) (fun H => .base H)
  rcases RS.const_spine_or_cut (Good := fun _ => LevelPrimitive univs)
    (fun H => level_primitive_spine_roots univs ``Eq.rec (Δ := []) H) with
    ⟨ls', args', rfl, _, _⟩ | ⟨ls', pre, pending, target, _, _, RP, HR, HN, _⟩
  · exact constHead_mkApps _ _
  · rcases HR with HR | HR
    · exact (typed_eq_no_core_root heq hreg hoff hD
        (RP.spine_cut_source_typed (erased_level_core_descent hs) HT)
        (constHead_mkApps _ _) HR).elim
    · exact (HN HR).elim

omit [Params] in
private theorem opaque_app_parts
    (V : OpaqueVariant Guard n (.app f x) out)
    (hn : ∀ {a b}, Guard a b → ProofShape.app f x ≠ a.liftN n) :
    ∃ g y, out = .app g y ∧ OpaqueVariant Guard n f g ∧ OpaqueVariant Guard n x y := by
  generalize E : ProofShape.app f x = source at V
  cases V with
  | refl => cases E; exact ⟨_, _, rfl, .refl, .refl⟩
  | app VF VX => cases E; exact ⟨_, _, rfl, VF, VX⟩
  | marked HG => exact (hn HG E).elim
  | proj | lam | forallE => cases E

omit [Params] in
private theorem varN_eq_head_opaque
    (hshape : ∀ {a b}, Guard a b → a.constHead = some ``Eq.rec)
    (hne : c ≠ ``Eq.rec)
    (H : Matches ((Pattern.const c).varN count) a ls caps)
    (V : OpaqueVariant Guard n a b) :
    ∃ caps', Matches ((Pattern.const c).varN count) b ls caps' ∧
      ∀ i, OpaqueVariant Guard n (caps i) (caps' i) := by
  have excluded {a b source k ls' cs} (HG : Guard a b)
      (HM : Matches ((Pattern.const c).varN k) source ls' cs)
      (E : source = a.liftN n) : False := by
    have HH := HM.constHead
    rw [E, head_lift, hshape HG, Pattern.constHead_eq, Pattern.headConst_varN,
      Pattern.headConst] at HH
    exact hne (Option.some.inj HH).symm
  induction count generalizing a b with
  | zero =>
    cases H
    generalize E : ProofShape.const c ls = source at V
    cases V with
    | refl => cases E; exact ⟨nofun, .const, nofun⟩
    | marked HG => exact (excluded (k := 0) HG Matches.const E).elim
    | app | proj | lam | forallE => cases E
  | succ count ih =>
    cases H with
    | var HM =>
      obtain ⟨g, y, rfl, VF, VX⟩ := opaque_app_parts V
        (fun HG E => excluded (k := count+1) HG (.var HM) E)
      obtain ⟨caps', HM', HC⟩ := ih HM VF
      refine ⟨_, .var HM', ?_⟩
      intro i; cases i with
      | none => exact VX
      | some i => exact HC i

omit [Params] in
private theorem constant_spine_eq_head
    (hshape : ∀ {a b}, Guard a b → a.constHead = some ``Eq.rec) (hne : c ≠ ``Eq.rec)
    (V : OpaqueVariant Guard n (ProofShape.mkApps (.const c ls) args) b) :
    ∃ args', b = ProofShape.mkApps (.const c ls) args' ∧
      List.Forall₂ (OpaqueVariant Guard n) args args' := by
  induction args using List.snoc_induction generalizing b with
  | nil =>
    generalize E : ProofShape.const c ls = source at V
    cases V with
    | refl => cases E; exact ⟨[], rfl, .nil⟩
    | marked HG =>
      have HH := congrArg constHead E
      rw [head_lift, hshape HG] at HH
      exact (hne (Option.some.inj HH)).elim
    | app | proj | lam | forallE => cases E
  | snoc args x ih =>
    rw [ProofShape.mkApps_snoc] at V
    obtain ⟨g, y, rfl, VF, VX⟩ := opaque_app_parts V (by
      intro a b HG E
      have HH := congrArg constHead E
      simp only [constHead, constHead_mkApps, head_lift, hshape HG] at HH
      exact hne (Option.some.inj HH))
    obtain ⟨args', rfl, HA⟩ := ih VF
    exact ⟨args' ++ [y], ProofShape.mkApps_snoc.symm, HA.append' (.cons VX .nil)⟩

private theorem matches_eq_head_opaque
    (heq : env.HasCanonicalEq)
    (hshape : ∀ {a b}, Guard a b → a.constHead = some ``Eq.rec)
    (hp : Pat p r) (hne : p.constHead ≠ some ``Eq.rec)
    (H : Matches p a ls caps) (V : OpaqueVariant Guard n a b) :
    ∃ caps', Matches p b ls caps' ∧ ∀ i, OpaqueVariant Guard n (caps i) (caps' i) := by
  obtain ⟨sp, rfl⟩ := pat_simple hp
  cases sp with
  | defn c =>
    exact varN_eq_head_opaque (count := 0) (c := c) hshape
      (fun E => hne (by subst c; rfl)) H V
  | iota c major ctor fields =>
    have hc : c ≠ ``Eq.rec := by
      intro E
      subst c
      apply hne
      simp only [Pattern.constHead_eq, SimplePattern.iota_headConst]
    have hctor : ctor ≠ ``Eq.rec := by
      intro E
      have HR := pat_ctor_rigid hp
      rw [E] at HR
      obtain ⟨doms, hclosed, _, hpat⟩ := heq.2.2.2
      exact HR.pats _ _ hpat (SimplePattern.iota_headConst _ _ _ _)
    cases H with
    | app HF HX =>
      obtain ⟨g, y, rfl, VF, VX⟩ := opaque_app_parts V (by
        intro a b HG E
        have HH := (Matches.app HF HX).constHead
        simp only [E, head_lift, hshape HG, Pattern.constHead_eq,
          Pattern.headConst, Pattern.headConst_varN] at HH
        exact hc (Option.some.inj HH).symm)
      obtain ⟨cf, HF', HCF⟩ := varN_eq_head_opaque hshape hc HF VF
      obtain ⟨cx, HX', HCX⟩ := varN_eq_head_opaque hshape hctor HX VX
      refine ⟨_, .app HF' HX', ?_⟩
      intro i; cases i with
      | inl i => exact HCF i
      | inr i => exact HCX i

private theorem typed_core_target (hs : D.Sound env univs) (HT : TypedSource Δ a)
    (R : ProofShape.Compute (ErasedLevelCore D) a b) : TypedSource Δ b := by
  obtain ⟨Γ, e, T, hΓ, EΓ, ht, Ee⟩ := HT
  obtain ⟨e', HE, EE⟩ := proofErase_scoped_compute_realize (erased_level_core_descent hs)
    hΓ ht EΓ Ee (R.scoped (fun H => .base H))
  exact ⟨Γ, e', T, hΓ, EΓ, HE.hasType.2, EE⟩

/-- Every typed core root has a matching payload path for arbitrary Eq-headed
marks. Source typing excludes Eq patterns before other patterns are simulated;
no saturation assumption or target-head reduction is required. -/
theorem typed_eq_opaque_level_core_root
    (heq : env.HasCanonicalEq)
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hshape : ∀ {a b}, Guard a b → a.constHead = some ``Eq.rec)
    (hg : ∀ {a b a'}, Guard a b → ProofShape.Compute (ErasedLevelCore D) a a' → Guard a' b)
    (HT : TypedSource Δ a)
    (R : ErasedLevelCore D a out) (V : OpaqueVariant Guard n a b) :
    ∃ out', ProofShape.Compute (ErasedLevelCore D) b out' ∧ OpaqueVariant Guard n out out' := by
  cases V with
  | refl => exact ⟨_, .base R, .refl⟩
  | marked HG =>
    obtain ⟨a', RA, E⟩ := (ProofShape.Compute.base R).level_core_lift_inv
    refine ⟨_, .refl, ?_⟩
    rw [E]
    exact .marked (hg HG RA)
  | app VF VX =>
    rcases R with ((R | R) | R) | R
    · cases R
    · cases R with
      | select hp hc hm =>
        obtain ⟨caps', HM, HC⟩ := matches_eq_head_opaque heq hshape hp
          (fun E => typed_eq_pattern_no_match heq hreg hoff HT (hm.constHead.trans E) hp hm)
          hm (.app VF VX)
        exact ⟨_, .base (.inl (.inl (.inr (.select hp hc HM)))), HC _⟩
      | apply hp hc hm =>
        obtain ⟨caps', HM, HC⟩ := matches_eq_head_opaque heq hshape hp
          (fun E => typed_eq_pattern_no_match heq hreg hoff HT (hm.constHead.trans E) hp hm)
          hm (.app VF VX)
        exact ⟨_, .base (.inl (.inl (.inr (.apply hp hc HM)))), .app (HC _) (HC _)⟩
    · cases R with
      | intro hp hc ht hm =>
        obtain ⟨caps', HM, HC⟩ := matches_eq_head_opaque heq hshape hp
          (fun E => typed_eq_pattern_no_match heq hreg hoff HT (hm.constHead.trans E) hp hm)
          hm (.app VF VX)
        refine ⟨_, .base (.inl (.inr (.intro hp hc ht HM))), OpaqueVariant.refl.mkApps_pair ?_⟩
        apply List.forall₂_of_getElem (by simp)
        intro i hi hi'
        simp only [List.getElem_map]
        exact HC _
    · cases R
  | @proj n m m' s i VM =>
    rcases R with ((R | R) | R) | R
    · cases R with
      | @projIota _ info args _ ls field hi hlen hget =>
        have hne : info.ctorName ≠ ``Eq.rec := by
          intro E
          have HR := projection_ctor_rigid hi
          rw [E] at HR
          obtain ⟨doms, hclosed, _, hp⟩ := heq.2.2.2
          exact HR.pats _ _ hp (SimplePattern.iota_headConst _ _ _ _)
        obtain ⟨args', rfl, HA⟩ := constant_spine_eq_head hshape hne VM
        obtain ⟨hj, HE⟩ := List.getElem?_eq_some_iff.1 hget
        have hj' : info.nparams + i < args'.length := by rw [← HA.length_eq]; exact hj
        refine ⟨args'[info.nparams + i]'hj', .base (.inl (.inl (.inl
          (.projIota hi (HA.length_eq.symm.trans hlen) (List.getElem?_eq_getElem hj'))))), ?_⟩
        rw [← HE]
        exact HA.getElem_of _ hj hj'
    · cases R with
      | select _ _ hm => cases hm
      | apply _ _ hm => cases hm
    · cases R with | intro _ _ _ hm => cases hm
    · cases R
  | lam VA VB =>
    rcases R with R | R
    · exact (erased_iota_primitive_head R).elim
    · cases R
  | forallE VA VB =>
    rcases R with R | R
    · exact (erased_iota_primitive_head R).elim
    · cases R

/-- Arbitrary finite level-core paths preserve opaque Eq-headed marks when
the source has a typed realization. Every recursive component retains its
actual source scope, and transitivity replays typing at the intermediate term. -/
theorem ProofShape.OpaqueVariant.typed_eq_core_left
    (hs : D.Sound env univs)
    (heq : env.HasCanonicalEq)
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hshape : ∀ {a b}, Guard a b → a.constHead = some ``Eq.rec)
    (hg : ∀ {a b a'}, Guard a b → ProofShape.Compute (ErasedLevelCore D) a a' → Guard a' b)
    (HT : TypedSource Δ a)
    (R : ProofShape.Compute (ErasedLevelCore D) a a') (V : OpaqueVariant Guard n a b) :
    ∃ b', ProofShape.Compute (ErasedLevelCore D) b b' ∧ OpaqueVariant Guard n a' b' := by
  induction R generalizing Δ n b with
  | base R => exact typed_eq_opaque_level_core_root heq hreg hoff hshape hg HT R V
  | trans R₁ _ ih₁ ih₂ =>
    obtain ⟨b₁, RB, V₁⟩ := ih₁ HT V
    obtain ⟨b₂, RC, V₂⟩ := ih₂ (typed_core_target hs HT R₁) V₁
    exact ⟨b₂, RB.trans RC, V₂⟩
  | @app f f' x x' RF RX ihf ihx =>
    generalize E : ProofShape.app f x = source at V
    cases V with
    | refl => cases E; exact ⟨_, .app RF RX, .refl⟩
    | app VF VX =>
      cases E
      obtain ⟨g, RG, VG⟩ := ihf ((ScopedHole.appFn .hole x).typed HT) VF
      obtain ⟨y, RY, VY⟩ := ihx ((ScopedHole.appArg f .hole).typed HT) VX
      exact ⟨_, .app RG RY, .app VG VY⟩
    | marked HG =>
      obtain ⟨a', RA', EO⟩ := (E ▸ ProofShape.Compute.app RF RX).level_core_lift_inv
      refine ⟨_, .refl, ?_⟩; rw [EO]; exact .marked (hg HG RA')
    | proj | lam | forallE => cases E
  | @proj m m' s i R ih =>
    generalize E : ProofShape.proj s i m = source at V
    cases V with
    | refl => cases E; exact ⟨_, .proj R, .refl⟩
    | proj V =>
      cases E
      obtain ⟨b, RB, VB⟩ := ih ((ScopedHole.proj s i .hole).typed HT) V
      exact ⟨_, .proj RB, .proj VB⟩
    | marked HG =>
      obtain ⟨a', RA', EO⟩ := (E ▸ ProofShape.Compute.proj R).level_core_lift_inv
      refine ⟨_, .refl, ?_⟩; rw [EO]; exact .marked (hg HG RA')
    | app | lam | forallE => cases E
  | @lam A A' body body' RA RB ihA ihB =>
    generalize E : ProofShape.lam A body = source at V
    cases V with
    | refl => cases E; exact ⟨_, .lam RA RB, .refl⟩
    | lam VA VB =>
      cases E
      obtain ⟨C, RC, VC⟩ := ihA ((ScopedHole.lamDomain .hole body).typed HT) VA
      obtain ⟨d, RD, VD⟩ := ihB ((ScopedHole.lamBody A .hole).typed HT) VB
      exact ⟨_, .lam RC RD, .lam VC VD⟩
    | marked HG =>
      obtain ⟨a', RA', EO⟩ := (E ▸ ProofShape.Compute.lam RA RB).level_core_lift_inv
      refine ⟨_, .refl, ?_⟩; rw [EO]; exact .marked (hg HG RA')
    | app | proj | forallE => cases E
  | @forallE A A' body body' RA RB ihA ihB =>
    generalize E : ProofShape.forallE A body = source at V
    cases V with
    | refl => cases E; exact ⟨_, .forallE RA RB, .refl⟩
    | forallE VA VB =>
      cases E
      obtain ⟨C, RC, VC⟩ := ihA ((ScopedHole.piDomain .hole body).typed HT) VA
      obtain ⟨d, RD, VD⟩ := ihB ((ScopedHole.piBody A .hole).typed HT) VB
      exact ⟨_, .forallE RC RD, .forallE VC VD⟩
    | marked HG =>
      obtain ⟨a', RA', EO⟩ := (E ▸ ProofShape.Compute.forallE RA RB).level_core_lift_inv
      refine ⟨_, .refl, ?_⟩; rw [EO]; exact .marked (hg HG RA')
    | app | proj | lam => cases E
  | beta R =>
    obtain ⟨b', RB, VB⟩ := V.beta_left (Guard := Guard) (fun H => hshape H) (fun H R => hg H (.beta R)) R
    exact ⟨b', .beta RB, VB⟩

end Lean4Lean.VEnv.Strengthening
