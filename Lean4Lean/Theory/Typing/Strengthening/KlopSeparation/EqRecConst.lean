import Lean4Lean.Theory.Typing.Strengthening.KlopSeparation.EqRecRules

/-! # Soundness: `Eq.rec` is an element of its declared type

The six binder types of `Eq.rec.{v, u}` are given the semantic judgment in their contexts,
the body `recBody` is a semantic term of the result type in the six-binder context
(`recBody_semD`, from `RecArgs.recBody_mem` and `recBody_rel`), and six abstractions give
`recLam_semD`. `recDen_eq` identifies `⟦Eq.rec⟧` with that abstraction.
-/

namespace Lean4Lean
namespace VEnv.Strengthening

open Classical

section Types
variable (v u : VLevel)

/-- The binder types of `Eq.rec.{v, u}` and its result type. -/
def rA1 : VExpr := .sort u
def rA2 : VExpr := .bvar 0
def rA3 : VExpr := motiveOf v u (.bvar 1) (.bvar 0)
def rA4 : VExpr := .app (.app (.bvar 0) (.bvar 1)) (reflS u (.bvar 2) (.bvar 1))
def rA5 : VExpr := .bvar 3
def rA6 : VExpr := eqS u (.bvar 4) (.bvar 3) (.bvar 0)
def rR : VExpr := .app (.app (.bvar 3) (.bvar 1)) (.bvar 0)

def rΓ1 : List VExpr := [rA1 u]
def rΓ2 : List VExpr := [rA2, rA1 u]
def rΓ3 : List VExpr := [rA3 v u, rA2, rA1 u]
def rΓ4 : List VExpr := [rA4 u, rA3 v u, rA2, rA1 u]
def rΓ5 : List VExpr := [rA5, rA4 u, rA3 v u, rA2, rA1 u]
def rΓ6 : List VExpr := [rA6 u, rA5, rA4 u, rA3 v u, rA2, rA1 u]

end Types

namespace SetModel
variable {𝕋 : SetModel} {v u : VLevel}

local infix:50 " ∈ₛ " => 𝕋.mem

theorem rS1 : 𝕋.Sem [] (rA1 u) (rA1 u) (.sort (.succ u)) := sem_sort rfl

theorem rS2 : 𝕋.Sem (rΓ1 u) rA2 rA2 (.sort u) := sem_bvar (Lookup.zero (ty := rA1 u))

theorem rS3 : 𝕋.Sem (rΓ2 u) (rA3 v u) (rA3 v u)
    (.sort (.imax u (.imax .zero (.succ v)))) := by
  have hα : 𝕋.Sem (rΓ2 u) (.bvar 1) (.bvar 1) (.sort u) :=
    sem_bvar (Lookup.succ (Lookup.zero (ty := rA1 u)))
  have hα' : 𝕋.Sem (.bvar 1 :: rΓ2 u) (.bvar 2) (.bvar 2) (.sort u) :=
    sem_bvar (Lookup.succ (Lookup.succ (Lookup.zero (ty := rA1 u))))
  have ha' : 𝕋.Sem (.bvar 1 :: rΓ2 u) (.bvar 1) (.bvar 1) (.bvar 2) :=
    sem_bvar (Lookup.succ (Lookup.zero (ty := rA2) (Γ := [rA1 u])))
  have hb' : 𝕋.Sem (.bvar 1 :: rΓ2 u) (.bvar 0) (.bvar 0) (.bvar 2) :=
    sem_bvar (Lookup.zero (ty := .bvar 1) (Γ := rΓ2 u))
  exact Sem.forallE hα (Sem.forallE (Sem.eqApp hα' ha' hb') (sem_sort rfl) (semU_sort v))
    (SemU.forallE (Sem.eqApp hα' ha' hb') (sem_sort rfl)
      (semU_prop _) (semU_sort v))

theorem rU1 : 𝕋.SemU [] (rA1 u) (.sort (.succ u)) := semU_sort u

theorem rU2 : 𝕋.SemU (rΓ1 u) rA2 (.sort u) := semU_bvar (Lookup.zero (ty := rA1 u))

theorem rU3 : 𝕋.SemU (rΓ2 u) (rA3 v u) (.sort (.imax u (.imax .zero (.succ v)))) := by
  have hα : 𝕋.Sem (rΓ2 u) (.bvar 1) (.bvar 1) (.sort u) :=
    sem_bvar (Lookup.succ (Lookup.zero (ty := rA1 u)))
  have hαU : 𝕋.SemU (rΓ2 u) (.bvar 1) (.sort u) :=
    semU_bvar (Lookup.succ (Lookup.zero (ty := rA1 u)))
  have hα' : 𝕋.Sem (.bvar 1 :: rΓ2 u) (.bvar 2) (.bvar 2) (.sort u) :=
    sem_bvar (Lookup.succ (Lookup.succ (Lookup.zero (ty := rA1 u))))
  have ha' : 𝕋.Sem (.bvar 1 :: rΓ2 u) (.bvar 1) (.bvar 1) (.bvar 2) :=
    sem_bvar (Lookup.succ (Lookup.zero (ty := rA2) (Γ := [rA1 u])))
  have hb' : 𝕋.Sem (.bvar 1 :: rΓ2 u) (.bvar 0) (.bvar 0) (.bvar 2) :=
    sem_bvar (Lookup.zero (ty := .bvar 1) (Γ := rΓ2 u))
  have hinU := SemU.forallE (Sem.eqApp hα' ha' hb') (sem_sort (l := v) rfl)
    (semU_prop _) (semU_sort v)
  exact SemU.forallE hα (Sem.forallE (Sem.eqApp hα' ha' hb') (sem_sort rfl) (semU_sort v))
    hαU hinU

theorem rS4 : 𝕋.Sem (rΓ3 v u) (rA4 u) (rA4 u) (.sort v) := by
  have hα : 𝕋.Sem (rΓ3 v u) (.bvar 2) (.bvar 2) (.sort u) :=
    sem_bvar (Lookup.succ (Lookup.succ (Lookup.zero (ty := rA1 u))))
  have ha : 𝕋.Sem (rΓ3 v u) (.bvar 1) (.bvar 1) (.bvar 2) :=
    sem_bvar (Lookup.succ (Lookup.zero (ty := rA2) (Γ := [rA1 u])))
  have hM : 𝕋.Sem (rΓ3 v u) (.bvar 0) (.bvar 0) (motiveOf v u (.bvar 2) (.bvar 1)) :=
    sem_bvar (Lookup.zero (ty := rA3 v u) (Γ := rΓ2 u))
  exact Sem.fibApp hα ha hM ha (Sem.reflApp hα ha)

theorem rU4 : 𝕋.SemU (rΓ3 v u) (rA4 u) (.sort v) := by
  have hα : 𝕋.Sem (rΓ3 v u) (.bvar 2) (.bvar 2) (.sort u) :=
    sem_bvar (Lookup.succ (Lookup.succ (Lookup.zero (ty := rA1 u))))
  have ha : 𝕋.Sem (rΓ3 v u) (.bvar 1) (.bvar 1) (.bvar 2) :=
    sem_bvar (Lookup.succ (Lookup.zero (ty := rA2) (Γ := [rA1 u])))
  have haU : 𝕋.SemU (rΓ3 v u) (.bvar 1) (.bvar 2) :=
    semU_bvar (Lookup.succ (Lookup.zero (ty := rA2) (Γ := [rA1 u])))
  have hM : 𝕋.Sem (rΓ3 v u) (.bvar 0) (.bvar 0) (motiveOf v u (.bvar 2) (.bvar 1)) :=
    sem_bvar (Lookup.zero (ty := rA3 v u) (Γ := rΓ2 u))
  have hMU : 𝕋.SemU (rΓ3 v u) (.bvar 0) (motiveOf v u (.bvar 2) (.bvar 1)) :=
    semU_bvar (Lookup.zero (ty := rA3 v u) (Γ := rΓ2 u))
  exact SemU.fibApp hα ha hM ha (Sem.reflApp hα ha) hMU haU

theorem rU5 : 𝕋.SemU (rΓ4 v u) rA5 (.sort u) :=
  semU_bvar (Lookup.succ (Lookup.succ (Lookup.succ (Lookup.zero (ty := rA1 u)))))

theorem rU6 : 𝕋.SemU (rΓ5 v u) (rA6 u) (.sort .zero) :=
  semU_prop _

theorem rS5 : 𝕋.Sem (rΓ4 v u) rA5 rA5 (.sort u) :=
  sem_bvar (Lookup.succ (Lookup.succ (Lookup.succ (Lookup.zero (ty := rA1 u)))))

theorem rS6 : 𝕋.Sem (rΓ5 v u) (rA6 u) (rA6 u) (.sort .zero) := by
  have hα : 𝕋.Sem (rΓ5 v u) (.bvar 4) (.bvar 4) (.sort u) :=
    sem_bvar (Lookup.succ (Lookup.succ (Lookup.succ (Lookup.succ (Lookup.zero (ty := rA1 u))))))
  have ha : 𝕋.Sem (rΓ5 v u) (.bvar 3) (.bvar 3) (.bvar 4) :=
    sem_bvar (Lookup.succ (Lookup.succ (Lookup.succ
      (Lookup.zero (ty := rA2) (Γ := [rA1 u])))))
  have hb : 𝕋.Sem (rΓ5 v u) (.bvar 0) (.bvar 0) (.bvar 4) :=
    sem_bvar (Lookup.zero (ty := rA5) (Γ := rΓ4 v u))
  exact Sem.eqApp hα ha hb

/-- The variables of the six-binder context. -/
theorem rVars :
    𝕋.Sem (rΓ6 v u) (.bvar 5) (.bvar 5) (.sort u) ∧
    𝕋.Sem (rΓ6 v u) (.bvar 4) (.bvar 4) (.bvar 5) ∧
    𝕋.Sem (rΓ6 v u) (.bvar 3) (.bvar 3) (motiveOf v u (.bvar 5) (.bvar 4)) ∧
    𝕋.Sem (rΓ6 v u) (.bvar 2) (.bvar 2)
      (.app (.app (.bvar 3) (.bvar 4)) (reflS u (.bvar 5) (.bvar 4))) ∧
    𝕋.Sem (rΓ6 v u) (.bvar 1) (.bvar 1) (.bvar 5) ∧
    𝕋.Sem (rΓ6 v u) (.bvar 0) (.bvar 0) (eqS u (.bvar 5) (.bvar 4) (.bvar 1)) :=
  ⟨sem_bvar (Lookup.succ (Lookup.succ (Lookup.succ (Lookup.succ (Lookup.succ
      (Lookup.zero (ty := rA1 u))))))),
    sem_bvar (Lookup.succ (Lookup.succ (Lookup.succ (Lookup.succ
      (Lookup.zero (ty := rA2) (Γ := [rA1 u])))))),
    sem_bvar (Lookup.succ (Lookup.succ (Lookup.succ
      (Lookup.zero (ty := rA3 v u) (Γ := rΓ2 u))))),
    sem_bvar (Lookup.succ (Lookup.succ (Lookup.zero (ty := rA4 u) (Γ := rΓ3 v u)))),
    sem_bvar (Lookup.succ (Lookup.zero (ty := rA5) (Γ := rΓ4 v u))),
    sem_bvar (Lookup.zero (ty := rA6 u) (Γ := rΓ5 v u))⟩

theorem rSR : 𝕋.Sem (rΓ6 v u) rR rR (.sort v) :=
  Sem.fibApp rVars.1 rVars.2.1 rVars.2.2.1 rVars.2.2.2.2.1 rVars.2.2.2.2.2

theorem rUR : 𝕋.SemU (rΓ6 v u) rR (.sort v) :=
  SemU.fibApp rVars.1 rVars.2.1 rVars.2.2.1 rVars.2.2.2.2.1 rVars.2.2.2.2.2
    (semU_bvar (Lookup.succ (Lookup.succ (Lookup.succ
      (Lookup.zero (ty := rA3 v u) (Γ := rΓ2 u))))))
    (semU_bvar (Lookup.succ (Lookup.zero (ty := rA5) (Γ := rΓ4 v u))))

/-- A valuation of the six-binder context supplies the arguments of `Eq.rec`. -/
theorem recArgs_of_valOK {ρ : Nat → 𝕋.S} {w : Nat → PVal} (hρ : 𝕋.ValOK (rΓ6 v u) ρ w) :
    𝕋.RecArgs u v (ρ 5) (ρ 4) (ρ 3) (ρ 2) (ρ 1) ∧ ρ 0 = 𝕋.star := by
  obtain ⟨h5, h4, h3, h2, h1, h0⟩ := rVars (𝕋 := 𝕋) (v := v) (u := u)
  have m5 : 𝕋.mem (ρ 5) (𝕋.El (𝕋.sortDen u)) := (h5 ρ w hρ).2.2.1
  have m4 : 𝕋.mem (ρ 4) (𝕋.El (ρ 5)) := (h4 ρ w hρ).2.2.1
  have m3 := (h3 ρ w hρ).2.2.1
  rw [den_motiveOf (ρ := ρ) (α := .bvar 5) (a := .bvar 4) m5 m4] at m3
  have m2 := (h2 ρ w hρ).2.2.1
  have e2 : 𝕋.den ρ (.app (.app (.bvar 3) (.bvar 4)) (reflS u (.bvar 5) (.bvar 4))) =
      𝕋.Fib (ρ 3) (ρ 4) := by
    show 𝕋.mkApp (𝕋.mkApp (ρ 3) (ρ 4)) (𝕋.den ρ (reflS u (.bvar 5) (.bvar 4))) = _
    rw [den_reflS]; rfl
  rw [e2] at m2
  have m1 : 𝕋.mem (ρ 1) (𝕋.El (ρ 5)) := (h1 ρ w hρ).2.2.1
  have m0 := (h0 ρ w hρ).2.2.1
  have e0 : 𝕋.den ρ (eqS u (.bvar 5) (.bvar 4) (.bvar 1)) =
      𝕋.cand (𝕋.eqCand (ρ 5) (ρ 4) (ρ 1)) :=
    den_eqApp (ρ := ρ) (A := .bvar 5) (x := .bvar 4) (y := .bvar 1) m5 m4 m1
  rw [e0] at m0
  obtain ⟨hs, hne⟩ := 𝕋.mem_El_cand.1 m0
  have hαv := (mem_sortDen m5).1
  exact ⟨⟨m5, m4, m3, m2, m1, ((eqCand_nonempty_iff hαv.isPER).1 hne).2⟩, hs⟩

/-- The body of `Eq.rec` as a semantic term. -/
noncomputable def recBodyD (𝕋 : SetModel) (ρ : Nat → 𝕋.S) : 𝕋.S :=
  𝕋.recBody (ρ 5) (ρ 4) (ρ 3) (ρ 2) (ρ 1)

/-- **The body of `Eq.rec` is a semantic term of the result type.** -/
theorem recBody_semD : 𝕋.SemD (rΓ6 v u) 𝕋.recBodyD rR := by
  intro ρ w hρ
  obtain ⟨H, h0⟩ := recArgs_of_valOK hρ
  have hR : 𝕋.den ρ rR = 𝕋.Fib (ρ 3) (ρ 1) := by
    show 𝕋.mkApp (𝕋.mkApp (ρ 3) (ρ 1)) (ρ 0) = _
    rw [h0]; rfl
  refine ⟨by rw [hR]; exact H.recBody_mem, fun ρ' w' hρ' hr => ?_⟩
  obtain ⟨H', -⟩ := recArgs_of_valOK hρ'
  obtain ⟨h5, h4, h3, h2, h1, -⟩ := rVars (𝕋 := 𝕋) (v := v) (u := u)
  have r3 := ((h3 ρ w hρ).2.2.2.2 ρ' w' hρ' hr).2
  rw [den_motiveOf (ρ := ρ) (α := .bvar 5) (a := .bvar 4) H.hα H.ha] at r3
  have r2 := ((h2 ρ w hρ).2.2.2.2 ρ' w' hρ' hr).2
  have e2 : 𝕋.den ρ (.app (.app (.bvar 3) (.bvar 4)) (reflS u (.bvar 5) (.bvar 4))) =
      𝕋.Fib (ρ 3) (ρ 4) := by
    show 𝕋.mkApp (𝕋.mkApp (ρ 3) (ρ 4)) (𝕋.den ρ (reflS u (.bvar 5) (.bvar 4))) = _
    rw [den_reflS]; rfl
  rw [e2] at r2
  have r1 : 𝕋.Rel (ρ 5) (ρ 1) (ρ' 1) := ((h1 ρ w hρ).2.2.2.2 ρ' w' hρ' hr).2
  rw [hR]
  exact recBody_rel H H' r3 r2 r1

/-- **The body of `Eq.rec` satisfies the uniformity clause.** It is `•` where the fibre is a
proposition, an element of `T` in the exceptional case, and otherwise the minor premise, which
is uniform for the fibre over `a` and hence for the similar fibre over `b`. -/
theorem recBody_semDU : 𝕋.SemDU (rΓ6 v u) 𝕋.recBodyD rR := by
  intro n I ρ w hρ hctx
  have args := fun i => recArgs_of_valOK (hρ i)
  have hR : (fun i => 𝕋.den (ρ i) rR) = fun i => 𝕋.Fib (ρ i 3) (ρ i 1) := funext fun i => by
    show 𝕋.mkApp (𝕋.mkApp (ρ i 3) (ρ i 1)) (ρ i 0) = _
    rw [(args i).2]; rfl
  rw [hR]
  have h2U : 𝕋.SemU (rΓ6 v u) (.bvar 2)
      (.app (.app (.bvar 3) (.bvar 4)) (reflS u (.bvar 5) (.bvar 4))) :=
    semU_bvar (Lookup.succ (Lookup.succ (Lookup.zero (ty := rA4 u) (Γ := rΓ3 v u))))
  have h2 : 𝕋.Unif n I
      (fun i => 𝕋.den (ρ i) (.app (.app (.bvar 3) (.bvar 4)) (reflS u (.bvar 5) (.bvar 4))))
      (fun i => ρ i 2) := h2U n I ρ w hρ hctx
  have e2 : (fun i => 𝕋.den (ρ i)
      (.app (.app (.bvar 3) (.bvar 4)) (reflS u (.bvar 5) (.bvar 4)))) =
      fun i => 𝕋.Fib (ρ i 3) (ρ i 4) := funext fun i => by
    show 𝕋.mkApp (𝕋.mkApp (ρ i 3) (ρ i 4)) (𝕋.den (ρ i) (reflS u (.bvar 5) (.bvar 4))) = _
    rw [den_reflS]; rfl
  rw [e2] at h2
  refine Unif.cover (fun i => 𝕋.IsCand (𝕋.Fib (ρ i 3) (ρ i 1)))
    (unif_of_small (fun i => .inl (isBase_of_isCand i.2)) _) ?_
  refine Unif.cover (fun i : {i // ¬ 𝕋.IsCand (𝕋.Fib (ρ i 3) (ρ i 1))} =>
      ρ i.1 5 = 𝕋.tT ∧ 𝕋.Fib (ρ i.1 3) (ρ i.1 1) = 𝕋.tT ∧ ρ i.1 4 ≠ ρ i.1 1)
    (unif_of_small (fun i => ?_) _) ?_
  · show 𝕋.Small n (𝕋.Fib (ρ i.1.1 3) (ρ i.1.1 1))
    rw [i.2.2.1]; exact .inl (.inr (.inl kind_tT))
  · have eS : (fun j : {i : {i // ¬ 𝕋.IsCand (𝕋.Fib (ρ i 3) (ρ i 1))} //
          ¬ (ρ i.1 5 = 𝕋.tT ∧ 𝕋.Fib (ρ i.1 3) (ρ i.1 1) = 𝕋.tT ∧ ρ i.1 4 ≠ ρ i.1 1)} =>
        𝕋.recBodyD (ρ j.1.1)) = fun j => ρ j.1.1 2 := funext fun j => by
      show 𝕋.recBody _ _ _ _ _ = _
      unfold recBody
      rw [if_neg (show ¬ 𝕋.IsCand (𝕋.mkApp (𝕋.mkApp (ρ j.1.1 3) (ρ j.1.1 1)) 𝕋.star) from j.1.2),
        if_neg (show ¬ (ρ j.1.1 5 = 𝕋.tT ∧
          𝕋.mkApp (𝕋.mkApp (ρ j.1.1 3) (ρ j.1.1 1)) 𝕋.star = 𝕋.tT ∧ ρ j.1.1 4 ≠ ρ j.1.1 1)
          from j.2)]
    rw [eS]
    exact Unif.sim (fun j => (args j.1.1).1.fib_a_valid.tyRel_sim (args j.1.1).1.fib_b_valid
      (args j.1.1).1.fib_ab) (Unif.comp h2 fun j => Subtype.val (Subtype.val j))

/-! ### Six abstractions -/

/-- The declared type of `Eq.rec.{v, u}` as a telescope over the binder types. -/
def recTy (v u : VLevel) : VExpr :=
  .forallE (rA1 u) (.forallE rA2 (.forallE (rA3 v u) (.forallE (rA4 u) (.forallE rA5
    (.forallE (rA6 u) rR)))))

/-- The six-fold abstraction of the body over the denotations of the binder types. -/
noncomputable def recLamD (𝕋 : SetModel) (v u : VLevel) (ρ : Nat → 𝕋.S) : 𝕋.S :=
  𝕋.mkLam (𝕋.den ρ (rA1 u)) fun x1 =>
  𝕋.mkLam (𝕋.den (𝕋.cons x1 ρ) rA2) fun x2 =>
  𝕋.mkLam (𝕋.den (𝕋.cons x2 (𝕋.cons x1 ρ)) (rA3 v u)) fun x3 =>
  𝕋.mkLam (𝕋.den (𝕋.cons x3 (𝕋.cons x2 (𝕋.cons x1 ρ))) (rA4 u)) fun x4 =>
  𝕋.mkLam (𝕋.den (𝕋.cons x4 (𝕋.cons x3 (𝕋.cons x2 (𝕋.cons x1 ρ)))) rA5) fun x5 =>
  𝕋.mkLam (𝕋.den (𝕋.cons x5 (𝕋.cons x4 (𝕋.cons x3 (𝕋.cons x2 (𝕋.cons x1 ρ))))) (rA6 u))
    fun x6 => 𝕋.recBodyD
      (𝕋.cons x6 (𝕋.cons x5 (𝕋.cons x4 (𝕋.cons x3 (𝕋.cons x2 (𝕋.cons x1 ρ))))))

/-- The six-fold abstraction is a semantic term of the declared type of `Eq.rec`. -/
theorem recLam_semD : 𝕋.SemD [] (𝕋.recLamD v u) (recTy v u) := by
  have t6 := Sem.forallE (𝕋 := 𝕋) (rS6 (v := v) (u := u)) rSR rUR
  have tU6 := SemU.forallE (𝕋 := 𝕋) (rS6 (v := v) (u := u)) rSR rU6 rUR
  have t5 := Sem.forallE (𝕋 := 𝕋) (rS5 (v := v) (u := u)) t6 tU6
  have tU5 := SemU.forallE (𝕋 := 𝕋) (rS5 (v := v) (u := u)) t6 rU5 tU6
  have t4 := Sem.forallE (𝕋 := 𝕋) (rS4 (v := v) (u := u)) t5 tU5
  have tU4 := SemU.forallE (𝕋 := 𝕋) (rS4 (v := v) (u := u)) t5 rU4 tU5
  have t3 := Sem.forallE (𝕋 := 𝕋) (rS3 (v := v) (u := u)) t4 tU4
  have tU3 := SemU.forallE (𝕋 := 𝕋) (rS3 (v := v) (u := u)) t4 rU3 tU4
  have t2 := Sem.forallE (𝕋 := 𝕋) (rS2 (u := u)) t3 tU3
  have tU2 := SemU.forallE (𝕋 := 𝕋) (rS2 (u := u)) t3 rU2 tU3
  have d6 := SemD.lam (𝕋 := 𝕋) (rS6 (v := v) (u := u)) rSR recBody_semD rU6 rUR recBody_semDU
  have e6 := SemDU.lam (𝕋 := 𝕋) (rS6 (v := v) (u := u)) rSR
    (fun ρ w h => (recBody_semD ρ w h).1) rU6 rUR recBody_semDU
  have d5 := SemD.lam (𝕋 := 𝕋) (rS5 (v := v) (u := u)) t6 d6 rU5 tU6 e6
  have e5 := SemDU.lam (𝕋 := 𝕋) (rS5 (v := v) (u := u)) t6 (fun ρ w h => (d6 ρ w h).1)
    rU5 tU6 e6
  have d4 := SemD.lam (𝕋 := 𝕋) (rS4 (v := v) (u := u)) t5 d5 rU4 tU5 e5
  have e4 := SemDU.lam (𝕋 := 𝕋) (rS4 (v := v) (u := u)) t5 (fun ρ w h => (d5 ρ w h).1)
    rU4 tU5 e5
  have d3 := SemD.lam (𝕋 := 𝕋) (rS3 (v := v) (u := u)) t4 d4 rU3 tU4 e4
  have e3 := SemDU.lam (𝕋 := 𝕋) (rS3 (v := v) (u := u)) t4 (fun ρ w h => (d4 ρ w h).1)
    rU3 tU4 e4
  have d2 := SemD.lam (𝕋 := 𝕋) (rS2 (u := u)) t3 d3 rU2 tU3 e3
  have e2 := SemDU.lam (𝕋 := 𝕋) (rS2 (u := u)) t3 (fun ρ w h => (d3 ρ w h).1) rU2 tU3 e3
  exact SemD.lam rS1 t2 d2 rU1 tU2 e2

/-- **`⟦Eq.rec.{v, u}⟧` is the six-fold abstraction.** -/
theorem recDen_eq (ρ : Nat → 𝕋.S) : 𝕋.recDen v u = 𝕋.recLamD v u ρ := by
  unfold recDen recLamD
  refine mkLam_congr fun α hα => ?_
  refine mkLam_congr fun a ha => ?_
  have h3 : 𝕋.den (𝕋.cons a (𝕋.cons α ρ)) (rA3 v u) = 𝕋.motiveTy v α a :=
    den_motiveOf (ρ := 𝕋.cons a (𝕋.cons α ρ)) (α := .bvar 1) (a := .bvar 0) hα ha
  rw [h3]
  refine mkLam_congr fun M hM => ?_
  have h4 : 𝕋.den (𝕋.cons M (𝕋.cons a (𝕋.cons α ρ))) (rA4 u) =
      𝕋.mkApp (𝕋.mkApp M a) 𝕋.star := by
    show 𝕋.mkApp (𝕋.mkApp M a) (𝕋.den _ (reflS u (.bvar 2) (.bvar 1))) = _
    rw [den_reflS]
  rw [h4]
  refine mkLam_congr fun m hm => ?_
  refine mkLam_congr fun b hb => ?_
  have h6 : 𝕋.den (𝕋.cons b (𝕋.cons m (𝕋.cons M (𝕋.cons a (𝕋.cons α ρ))))) (rA6 u) =
      𝕋.cand (𝕋.eqCand α a b) :=
    den_eqApp (ρ := 𝕋.cons b (𝕋.cons m (𝕋.cons M (𝕋.cons a (𝕋.cons α ρ)))))
      (A := .bvar 4) (x := .bvar 3) (y := .bvar 0) hα ha hb
  rw [h6]
  exact mkLam_congr fun t ht => rfl

/-- `⟦Eq.rec.{v, u}⟧` is an element of the denotation of its declared type. -/
theorem recDen_mem (ρ : Nat → 𝕋.S) : 𝕋.recDen v u ∈ₛ 𝕋.El (𝕋.den ρ (recTy v u)) := by
  rw [recDen_eq ρ]
  exact (recLam_semD ρ (fun _ => .bot) (𝕋.valOK_nil ρ _)).1

theorem recTy_eq (ls : List VLevel) :
    canonicalEqRecType.instL ls = recTy (ls.getD 0 .zero) (ls.getD 1 .zero) := by
  simp [canonicalEqRecType, canonicalEqRecMotive, canonicalEqRecMinor, VExpr.instL, recTy,
    rA1, rA2, rA3, rA4, rA5, rA6, rR, motiveOf, eqS, reflS, VExpr.lift, VExpr.liftN, liftVar,
    VLevel.inst]

end SetModel
end VEnv.Strengthening
end Lean4Lean
