import Lean4Lean.Theory.Typing.Strengthening.ProofErasureOpaqueVariants
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureNeutralKCore

/-! # Visible patterns cannot inspect a proof-major cast occurrence

An opaque marked occurrence is a complete six-argument Eq recursor with an
erased proof major. A visible pattern can capture this occurrence but cannot
inspect it as a constructor or as a shorter recursor prefix.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private spineCount match_varN_count from Lean4Lean.Theory.Typing.Strengthening.ProofErasureNeutralKCore
namespace ProofShape
variable {Guard : ProofShape → ProofShape → Prop}

/-- The syntactic shape retained by an uncontracted proof-major cast. -/
def EqCastShape (e : ProofShape) : Prop :=
  ∃ v w α a M m b, e = eqRec v w α a M m b .proof

/-- Inserting binders preserves a blocked cast's head, arity and proof major. -/
theorem EqCastShape.liftN (H : EqCastShape e) : EqCastShape (e.liftN n k) := by
  obtain ⟨v, w, α, a, M, m, b, rfl⟩ := H
  exact ⟨v, w, _, _, _, _, _, rfl⟩

/-- A blocked cast always has the canonical recursor head. -/
theorem EqCastShape.head (H : EqCastShape e) : e.constHead = some ``Eq.rec := by
  obtain ⟨v, w, α, a, M, m, b, rfl⟩ := H
  rfl

private theorem EqCastShape.last (H : EqCastShape e) : ∃ f, e = .app f .proof := by
  obtain ⟨v, w, α, a, M, m, b, rfl⟩ := H
  exact ⟨_, rfl⟩

private theorem not_varN (H : EqCastShape e)
    (hm : Matches ((Pattern.const c).varN count) e ls caps)
    (hn : c ≠ ``Eq.rec ∨ count ≤ 5) : False := by
  rcases hn with hn | hn
  · exact hn (Option.some.inj (by simpa only [Pattern.constHead_eq, Pattern.headConst_varN, Pattern.headConst] using hm.constHead.symm.trans H.head))
  · obtain ⟨v, w, α, a, M, m, b, rfl⟩ := H
    have HC := match_varN_count hm
    change 6 = count at HC
    omega

private theorem app_parts
    (V : OpaqueVariant Guard n (.app f x) out)
    (hn : ∀ {a b}, Guard a b → ProofShape.app f x ≠ a.liftN n) :
    ∃ g y, out = .app g y ∧ OpaqueVariant Guard n f g ∧ OpaqueVariant Guard n x y := by
  generalize E : ProofShape.app f x = source at V
  cases V with
  | refl => cases E; exact ⟨_, _, rfl, .refl, .refl⟩
  | app VF VX => cases E; exact ⟨_, _, rfl, VF, VX⟩
  | marked HG => exact (hn HG E).elim
  | proj | lam | forallE => cases E

/-- Constant-and-capture prefixes retain all corresponding captures when the
head is not Eq.rec or the prefix is shorter than a full cast. -/
theorem Matches.varN_opaque
    (hshape : ∀ {a b}, Guard a b → EqCastShape a)
    (hn : c ≠ ``Eq.rec ∨ count ≤ 5)
    (H : Matches ((Pattern.const c).varN count) a ls caps)
    (V : OpaqueVariant Guard n a b) :
    ∃ caps', Matches ((Pattern.const c).varN count) b ls caps' ∧
      ∀ i, OpaqueVariant Guard n (caps i) (caps' i) := by
  induction count generalizing a b with
  | zero =>
    cases H
    generalize E : ProofShape.const c ls = source at V
    cases V with
    | refl => cases E; exact ⟨nofun, .const, nofun⟩
    | marked HG => exact (not_varN (count := 0) (c := c) (hshape HG).liftN (E ▸ Matches.const) (.inr (by decide))).elim
    | app | proj | lam | forallE => cases E
  | succ count ih =>
    cases H with
    | var HM =>
      obtain ⟨g, y, rfl, VF, VX⟩ := app_parts V (fun HG E =>
        not_varN (hshape HG).liftN (E ▸ Matches.var HM) hn)
      obtain ⟨caps', HM', HC⟩ := ih (hn.elim Or.inl (fun h => .inr (by omega))) HM VF
      refine ⟨_, .var HM', ?_⟩
      intro i; cases i with
      | none => exact VX
      | some i => exact HC i

/-- Constructor spines with a non-Eq.rec head retain their paired arguments. -/
theorem OpaqueVariant.constant_spine
    (hshape : ∀ {a b}, Guard a b → EqCastShape a) (hne : c ≠ ``Eq.rec)
    (V : OpaqueVariant Guard n (ProofShape.mkApps (.const c ls) args) b) :
    ∃ args', b = ProofShape.mkApps (.const c ls) args' ∧
      List.Forall₂ (OpaqueVariant Guard n) args args' := by
  induction args using List.snoc_induction generalizing b with
  | nil =>
    generalize E : ProofShape.const c ls = source at V
    cases V with
    | refl => cases E; exact ⟨[], rfl, .nil⟩
    | marked HG =>
      have H := (congrArg constHead E).trans (hshape HG).liftN.head
      exact (hne (Option.some.inj H)).elim
    | app | proj | lam | forallE => cases E
  | snoc args x ih =>
    rw [ProofShape.mkApps_snoc] at V
    obtain ⟨g, y, rfl, VF, VX⟩ := app_parts V (by
      intro a b HG E
      have H := (congrArg constHead E).trans (hshape HG).liftN.head
      simp only [constHead, constHead_mkApps] at H
      exact hne (Option.some.inj H))
    obtain ⟨args', rfl, HA⟩ := ih VF
    exact ⟨args' ++ [y], ProofShape.mkApps_snoc.symm, HA.append' (.cons VX .nil)⟩

/-- Corresponding heads and argument lists form corresponding spines. -/
theorem OpaqueVariant.mkApps_pair (V : OpaqueVariant Guard n f g)
    (H : List.Forall₂ (OpaqueVariant Guard n) args args') :
    OpaqueVariant Guard n (ProofShape.mkApps f args) (ProofShape.mkApps g args') := by
  induction H generalizing f g with
  | nil => exact V
  | cons HX _ ih => exact ih (.app V HX)

variable [Params]

/-- A registered visible pattern keeps the same universe list and paired
captures. Canonical Eq registration rules out inspecting a marked cast at any
recursor-prefix or constructor position. -/
theorem Matches.opaque_variant
    (heq : env.HasCanonicalEq)
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hshape : ∀ {a b}, Guard a b → EqCastShape a)
    (hp : Pat p r) (H : Matches p a ls caps) (V : OpaqueVariant Guard n a b) :
    ∃ caps', Matches p b ls caps' ∧ ∀ i, OpaqueVariant Guard n (caps i) (caps' i) := by
  obtain ⟨sp, rfl⟩ := pat_simple hp
  cases sp with
  | defn c => exact Matches.varN_opaque (count := 0) (c := c) hshape (.inr (by decide)) H V
  | iota c major ctor fields =>
    have hctor : ctor ≠ ``Eq.rec := by
      intro E
      have HR := pat_ctor_rigid hp
      rw [E] at HR
      obtain ⟨doms, hclosed, _, hpat⟩ := heq.2.2.2
      exact HR.pats _ _ hpat (SimplePattern.iota_headConst _ _ _ _)
    have hc : c ≠ ``Eq.rec ∨ major ≤ 5 := by
      by_cases E : c = ``Eq.rec
      · subst c
        have HM := ConstructorObservation.recursor_major_offset hreg hp
        rw [hoff] at HM
        exact .inr (by omega)
      · exact .inl E
    cases H with
    | app HF HX =>
      obtain ⟨g, y, rfl, VF, VX⟩ := app_parts V (by
        intro a b HG E
        obtain ⟨f, EF⟩ := (hshape HG).liftN.last
        exact HX.ne_proof (ProofShape.app.inj (E.trans EF)).2)
      obtain ⟨cf, HF', HCF⟩ := HF.varN_opaque hshape hc VF
      obtain ⟨cx, HX', HCX⟩ := HX.varN_opaque hshape (.inl hctor) VX
      refine ⟨_, .app HF' HX', ?_⟩
      intro i; cases i with
      | inl i => exact HCF i
      | inr i => exact HCX i

end ProofShape
end Lean4Lean.VEnv.Strengthening
