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

namespace UniverseTower
variable {𝕋 : UniverseTower} {v u : VLevel}

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
  exact Sem.forallE hα (Sem.forallE (Sem.eqApp hα' ha' hb') (sem_sort rfl))

theorem rS4 : 𝕋.Sem (rΓ3 v u) (rA4 u) (rA4 u) (.sort v) := by
  have hα : 𝕋.Sem (rΓ3 v u) (.bvar 2) (.bvar 2) (.sort u) :=
    sem_bvar (Lookup.succ (Lookup.succ (Lookup.zero (ty := rA1 u))))
  have ha : 𝕋.Sem (rΓ3 v u) (.bvar 1) (.bvar 1) (.bvar 2) :=
    sem_bvar (Lookup.succ (Lookup.zero (ty := rA2) (Γ := [rA1 u])))
  have hM : 𝕋.Sem (rΓ3 v u) (.bvar 0) (.bvar 0) (motiveOf v u (.bvar 2) (.bvar 1)) :=
    sem_bvar (Lookup.zero (ty := rA3 v u) (Γ := rΓ2 u))
  exact Sem.fibApp hα ha hM ha (Sem.reflApp hα ha)

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
noncomputable def recBodyD (𝕋 : UniverseTower) (ρ : Nat → 𝕋.S) : 𝕋.S :=
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

end UniverseTower
end VEnv.Strengthening
end Lean4Lean
