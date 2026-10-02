/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.SecB.W1FibReg

/-!
# TB.W1fib-d3: bounded 3-jets

A *3-jet* of `φ` on `U` (`JetOf U φ F`) is a chain `F 0, …, F 3` with `F 0 = φ` on `U` and
`F r` having derivative `F (r + 1)` at every point of `U` (`r < 3`). `JB U φ F A l` adds the bounds
`|F r| ≤ A l^r` (`r ≤ 3`). Jets are closed under constants, sums, scalar multiples, finite sums,
products (Leibniz, `jmul`: bound `8AB`), inverses (`jinv`, for `|F 0| ≥ 1/2`) and powers
(`jpow`); `jquad` is the jet of a quadratic polynomial. On an open set, `F r = φ^{(r)}`
(`JetOf.iteratedDeriv_eq`).
-/

@[expose] public section

namespace BiluLinial.Tight.SecB

/-- `F` is a 3-jet of `φ` on `U`. -/
def JetOf (U : Set ℝ) (φ : ℝ → ℝ) (F : ℕ → ℝ → ℝ) : Prop :=
  (∀ r < 3, ∀ t ∈ U, HasDerivAt (F r) (F (r + 1) t) t) ∧ ∀ t ∈ U, F 0 t = φ t

/-- `|F r t| ≤ A l^r` on `U` for `r ≤ 3`. -/
def JetLe (U : Set ℝ) (F : ℕ → ℝ → ℝ) (A l : ℝ) : Prop :=
  ∀ r ≤ 3, ∀ t ∈ U, |F r t| ≤ A * l ^ r

/-- A bounded 3-jet of `φ` on `U`. -/
def JB (U : Set ℝ) (φ : ℝ → ℝ) (F : ℕ → ℝ → ℝ) (A l : ℝ) : Prop :=
  JetOf U φ F ∧ JetLe U F A l

/-! ### Operations -/

noncomputable def jconst (c : ℝ) : ℕ → ℝ → ℝ := fun r _ => if r = 0 then c else 0

noncomputable def jadd (F G : ℕ → ℝ → ℝ) : ℕ → ℝ → ℝ := fun r t => F r t + G r t

noncomputable def jsub (F G : ℕ → ℝ → ℝ) : ℕ → ℝ → ℝ := fun r t => F r t - G r t

noncomputable def jsmul (c : ℝ) (F : ℕ → ℝ → ℝ) : ℕ → ℝ → ℝ := fun r t => c * F r t

noncomputable def jsum {ι : Type*} (s : Finset ι) (F : ι → ℕ → ℝ → ℝ) : ℕ → ℝ → ℝ :=
  fun r t => ∑ x ∈ s, F x r t

/-- The Leibniz jet of a product. -/
noncomputable def jmul (F G : ℕ → ℝ → ℝ) : ℕ → ℝ → ℝ := fun r t =>
  if r = 0 then F 0 t * G 0 t
  else if r = 1 then F 1 t * G 0 t + F 0 t * G 1 t
  else if r = 2 then F 2 t * G 0 t + 2 * (F 1 t * G 1 t) + F 0 t * G 2 t
  else F 3 t * G 0 t + 3 * (F 2 t * G 1 t) + 3 * (F 1 t * G 2 t) + F 0 t * G 3 t

/-- The jet of `c₀ + c₁ (t - t₀) + c₂ (t - t₀)²`. -/
noncomputable def jquad (c₀ c₁ c₂ t₀ : ℝ) : ℕ → ℝ → ℝ := fun r t =>
  if r = 0 then c₀ + c₁ * (t - t₀) + c₂ * (t - t₀) ^ 2
  else if r = 1 then c₁ + 2 * c₂ * (t - t₀)
  else if r = 2 then 2 * c₂
  else 0

/-- The jet of `1/g`. -/
noncomputable def jinv (G : ℕ → ℝ → ℝ) : ℕ → ℝ → ℝ := fun r t =>
  if r = 0 then (G 0 t)⁻¹
  else if r = 1 then -G 1 t / G 0 t ^ 2
  else if r = 2 then -G 2 t / G 0 t ^ 2 + 2 * G 1 t ^ 2 / G 0 t ^ 3
  else -G 3 t / G 0 t ^ 2 + 6 * (G 1 t * G 2 t) / G 0 t ^ 3 - 6 * G 1 t ^ 3 / G 0 t ^ 4

/-- The jet of `g^p` (`p ≥ 3`). -/
noncomputable def jpow (G : ℕ → ℝ → ℝ) (p : ℕ) : ℕ → ℝ → ℝ := fun r t =>
  if r = 0 then G 0 t ^ p
  else if r = 1 then p * G 0 t ^ (p - 1) * G 1 t
  else if r = 2 then p * ((p : ℝ) - 1) * G 0 t ^ (p - 2) * G 1 t ^ 2 + p * G 0 t ^ (p - 1) * G 2 t
  else p * ((p : ℝ) - 1) * ((p : ℝ) - 2) * G 0 t ^ (p - 3) * G 1 t ^ 3 +
    3 * (p * ((p : ℝ) - 1)) * G 0 t ^ (p - 2) * (G 1 t * G 2 t) + p * G 0 t ^ (p - 1) * G 3 t

/-! ### Jets -/

theorem lt_three_cases {r : ℕ} (hr : r < 3) : r = 0 ∨ r = 1 ∨ r = 2 := by omega

theorem le_three_cases {r : ℕ} (hr : r ≤ 3) : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 := by omega

theorem jetOf_const (U : Set ℝ) (c : ℝ) : JetOf U (fun _ => c) (jconst c) := by
  refine ⟨fun r _ t _ => ?_, fun t _ => by simp [jconst]⟩
  simp only [jconst, Nat.succ_ne_zero, if_false]
  exact hasDerivAt_const t _

theorem JetOf.add {U : Set ℝ} {φ ψ : ℝ → ℝ} {F G : ℕ → ℝ → ℝ} (hF : JetOf U φ F)
    (hG : JetOf U ψ G) : JetOf U (fun t => φ t + ψ t) (jadd F G) :=
  ⟨fun r hr t ht => (hF.1 r hr t ht).add (hG.1 r hr t ht),
    fun t ht => by simp only [jadd, hF.2 t ht, hG.2 t ht]⟩

theorem JetOf.sub {U : Set ℝ} {φ ψ : ℝ → ℝ} {F G : ℕ → ℝ → ℝ} (hF : JetOf U φ F)
    (hG : JetOf U ψ G) : JetOf U (fun t => φ t - ψ t) (jsub F G) :=
  ⟨fun r hr t ht => (hF.1 r hr t ht).sub (hG.1 r hr t ht),
    fun t ht => by simp only [jsub, hF.2 t ht, hG.2 t ht]⟩

theorem JetOf.smul {U : Set ℝ} {φ : ℝ → ℝ} {F : ℕ → ℝ → ℝ} (c : ℝ) (hF : JetOf U φ F) :
    JetOf U (fun t => c * φ t) (jsmul c F) :=
  ⟨fun r hr t ht => (hF.1 r hr t ht).const_mul c, fun t ht => by simp only [jsmul, hF.2 t ht]⟩

theorem JetOf.sum {ι : Type*} {U : Set ℝ} (s : Finset ι) {φ : ι → ℝ → ℝ}
    {F : ι → ℕ → ℝ → ℝ} (hF : ∀ x ∈ s, JetOf U (φ x) (F x)) :
    JetOf U (fun t => ∑ x ∈ s, φ x t) (jsum s F) :=
  ⟨fun r hr t ht => HasDerivAt.fun_sum fun x hx => (hF x hx).1 r hr t ht,
    fun t ht => Finset.sum_congr rfl fun x hx => (hF x hx).2 t ht⟩

theorem JetOf.congr {U : Set ℝ} {φ ψ : ℝ → ℝ} {F : ℕ → ℝ → ℝ} (hF : JetOf U φ F)
    (h : ∀ t ∈ U, φ t = ψ t) : JetOf U ψ F :=
  ⟨hF.1, fun t ht => (hF.2 t ht).trans (h t ht)⟩

theorem JetOf.mul {U : Set ℝ} {φ ψ : ℝ → ℝ} {F G : ℕ → ℝ → ℝ} (hF : JetOf U φ F)
    (hG : JetOf U ψ G) : JetOf U (fun t => φ t * ψ t) (jmul F G) := by
  refine ⟨fun r hr t ht => ?_, fun t ht => by simp only [jmul, if_pos, hF.2 t ht, hG.2 t ht]⟩
  have f0 := hF.1 0 (by norm_num) t ht
  have f1 := hF.1 1 (by norm_num) t ht
  have f2 := hF.1 2 (by norm_num) t ht
  have g0 := hG.1 0 (by norm_num) t ht
  have g1 := hG.1 1 (by norm_num) t ht
  have g2 := hG.1 2 (by norm_num) t ht
  rcases lt_three_cases hr with rfl | rfl | rfl
  · show HasDerivAt (fun t => F 0 t * G 0 t) (F 1 t * G 0 t + F 0 t * G 1 t) t
    exact f0.mul g0
  · show HasDerivAt (fun t => F 1 t * G 0 t + F 0 t * G 1 t)
      (F 2 t * G 0 t + 2 * (F 1 t * G 1 t) + F 0 t * G 2 t) t
    convert (f1.mul g0).add (f0.mul g1) using 1
    ring
  · show HasDerivAt (fun t => F 2 t * G 0 t + 2 * (F 1 t * G 1 t) + F 0 t * G 2 t)
      (F 3 t * G 0 t + 3 * (F 2 t * G 1 t) + 3 * (F 1 t * G 2 t) + F 0 t * G 3 t) t
    convert ((f2.mul g0).add ((f1.mul g1).const_mul 2)).add (f0.mul g2) using 1
    ring

theorem jetOf_quad (U : Set ℝ) (c₀ c₁ c₂ t₀ : ℝ) :
    JetOf U (fun t => c₀ + c₁ * (t - t₀) + c₂ * (t - t₀) ^ 2) (jquad c₀ c₁ c₂ t₀) := by
  refine ⟨fun r hr t _ => ?_, fun t _ => by simp [jquad]⟩
  have hs : HasDerivAt (fun t : ℝ => t - t₀) 1 t := (hasDerivAt_id t).sub_const t₀
  rcases lt_three_cases hr with rfl | rfl | rfl
  · show HasDerivAt (fun t => c₀ + c₁ * (t - t₀) + c₂ * (t - t₀) ^ 2) (c₁ + 2 * c₂ * (t - t₀)) t
    convert ((hs.const_mul c₁).const_add c₀).add ((hs.pow 2).const_mul c₂) using 1
    simp
    ring
  · show HasDerivAt (fun t => c₁ + 2 * c₂ * (t - t₀)) (2 * c₂) t
    convert (hs.const_mul (2 * c₂)).const_add c₁ using 1
    ring
  · show HasDerivAt (fun _ => 2 * c₂) 0 t
    exact hasDerivAt_const t _

theorem JetOf.inv {U : Set ℝ} {φ : ℝ → ℝ} {G : ℕ → ℝ → ℝ} (hG : JetOf U φ G)
    (h0 : ∀ t ∈ U, G 0 t ≠ 0) : JetOf U (fun t => (φ t)⁻¹) (jinv G) := by
  refine ⟨fun r hr t ht => ?_, fun t ht => by simp only [jinv, if_pos, hG.2 t ht]⟩
  have g0 := hG.1 0 (by norm_num) t ht
  have g1 := hG.1 1 (by norm_num) t ht
  have g2 := hG.1 2 (by norm_num) t ht
  have hz := h0 t ht
  rcases lt_three_cases hr with rfl | rfl | rfl
  · show HasDerivAt (fun t => (G 0 t)⁻¹) (-G 1 t / G 0 t ^ 2) t
    exact g0.inv hz
  · show HasDerivAt (fun t => -G 1 t / G 0 t ^ 2)
      (-G 2 t / G 0 t ^ 2 + 2 * G 1 t ^ 2 / G 0 t ^ 3) t
    convert g1.neg.div (g0.pow 2) (pow_ne_zero 2 hz) using 1
    simp only [Pi.pow_apply, Pi.neg_apply]
    field_simp
    ring
  · show HasDerivAt (fun t => -G 2 t / G 0 t ^ 2 + 2 * G 1 t ^ 2 / G 0 t ^ 3)
      (-G 3 t / G 0 t ^ 2 + 6 * (G 1 t * G 2 t) / G 0 t ^ 3 - 6 * G 1 t ^ 3 / G 0 t ^ 4) t
    convert (g2.neg.div (g0.pow 2) (pow_ne_zero 2 hz)).add
      (((g1.pow 2).const_mul 2).div (g0.pow 3) (pow_ne_zero 3 hz)) using 1
    simp only [Pi.pow_apply, Pi.neg_apply]
    field_simp
    ring

theorem JetOf.pow {U : Set ℝ} {φ : ℝ → ℝ} {G : ℕ → ℝ → ℝ} (hG : JetOf U φ G) {p : ℕ}
    (hp : 3 ≤ p) : JetOf U (fun t => φ t ^ p) (jpow G p) := by
  refine ⟨fun r hr t ht => ?_, fun t ht => by simp only [jpow, if_pos, hG.2 t ht]⟩
  have g0 := hG.1 0 (by norm_num) t ht
  have g1 := hG.1 1 (by norm_num) t ht
  have g2 := hG.1 2 (by norm_num) t ht
  have c1 : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; norm_num
  have c2 : ((p - 2 : ℕ) : ℝ) = (p : ℝ) - 2 := by rw [Nat.cast_sub (by omega)]; norm_num
  have e1 : p - 1 - 1 = p - 2 := by omega
  have e2 : p - 2 - 1 = p - 3 := by omega
  rcases lt_three_cases hr with rfl | rfl | rfl
  · show HasDerivAt (fun t => G 0 t ^ p) (p * G 0 t ^ (p - 1) * G 1 t) t
    exact g0.pow p
  · show HasDerivAt (fun t => p * G 0 t ^ (p - 1) * G 1 t)
      (p * ((p : ℝ) - 1) * G 0 t ^ (p - 2) * G 1 t ^ 2 + p * G 0 t ^ (p - 1) * G 2 t) t
    convert ((g0.pow (p - 1)).const_mul (p : ℝ)).mul g1 using 1
    simp only [Pi.pow_apply]
    rw [c1, e1]
    ring
  · show HasDerivAt (fun t => p * ((p : ℝ) - 1) * G 0 t ^ (p - 2) * G 1 t ^ 2 +
        p * G 0 t ^ (p - 1) * G 2 t)
      (p * ((p : ℝ) - 1) * ((p : ℝ) - 2) * G 0 t ^ (p - 3) * G 1 t ^ 3 +
        3 * (p * ((p : ℝ) - 1)) * G 0 t ^ (p - 2) * (G 1 t * G 2 t) +
          p * G 0 t ^ (p - 1) * G 3 t) t
    convert (((g0.pow (p - 2)).const_mul ((p : ℝ) * ((p : ℝ) - 1))).mul (g1.pow 2)).add
      (((g0.pow (p - 1)).const_mul (p : ℝ)).mul g2) using 1
    simp only [Pi.pow_apply]
    rw [c1, c2, e1, e2]
    ring

/-- On an open set, the jet is the chain of iterated derivatives. -/
theorem JetOf.iteratedDeriv_eq {U : Set ℝ} (hU : IsOpen U) {φ : ℝ → ℝ} {F : ℕ → ℝ → ℝ}
    (hF : JetOf U φ F) : ∀ r ≤ 3, ∀ t ∈ U, iteratedDeriv r φ t = F r t := by
  intro r
  induction r with
  | zero => intro _ t ht; rw [iteratedDeriv_zero, hF.2 t ht]
  | succ r ih =>
    intro hr t ht
    have heq : iteratedDeriv r φ =ᶠ[nhds t] F r :=
      Filter.eventually_of_mem (hU.mem_nhds ht) fun x hx => ih (by omega) x hx
    rw [iteratedDeriv_succ, heq.deriv_eq]
    exact (hF.1 r (by omega) t ht).deriv

/-! ### Bounds -/

theorem jb_const (U : Set ℝ) (c : ℝ) {l : ℝ} (hl : 0 ≤ l) :
    JB U (fun _ => c) (jconst c) |c| l := by
  refine ⟨jetOf_const U c, fun r _ t _ => ?_⟩
  by_cases h : r = 0
  · subst h; simp [jconst]
  · simp only [jconst, if_neg h, abs_zero]
    positivity

theorem JB.mono {U : Set ℝ} {φ : ℝ → ℝ} {F : ℕ → ℝ → ℝ} {A A' l : ℝ} (h : JB U φ F A l)
    (hA : A ≤ A') (hl : 0 ≤ l) : JB U φ F A' l :=
  ⟨h.1, fun r hr t ht => (h.2 r hr t ht).trans
    (mul_le_mul_of_nonneg_right hA (pow_nonneg hl r))⟩

theorem JB.congr {U : Set ℝ} {φ ψ : ℝ → ℝ} {F : ℕ → ℝ → ℝ} {A l : ℝ} (h : JB U φ F A l)
    (hφ : ∀ t ∈ U, φ t = ψ t) : JB U ψ F A l :=
  ⟨h.1.congr hφ, h.2⟩

theorem JB.add {U : Set ℝ} {φ ψ : ℝ → ℝ} {F G : ℕ → ℝ → ℝ} {A B l : ℝ} (hF : JB U φ F A l)
    (hG : JB U ψ G B l) : JB U (fun t => φ t + ψ t) (jadd F G) (A + B) l := by
  refine ⟨hF.1.add hG.1, fun r hr t ht => ?_⟩
  have := abs_add_le (F r t) (G r t)
  have h1 := hF.2 r hr t ht
  have h2 := hG.2 r hr t ht
  simp only [jadd]
  linarith [show (A + B) * l ^ r = A * l ^ r + B * l ^ r by ring]

theorem JB.sub {U : Set ℝ} {φ ψ : ℝ → ℝ} {F G : ℕ → ℝ → ℝ} {A B l : ℝ} (hF : JB U φ F A l)
    (hG : JB U ψ G B l) : JB U (fun t => φ t - ψ t) (jsub F G) (A + B) l := by
  refine ⟨hF.1.sub hG.1, fun r hr t ht => ?_⟩
  have := abs_sub (F r t) (G r t)
  have h1 := hF.2 r hr t ht
  have h2 := hG.2 r hr t ht
  simp only [jsub]
  linarith [show (A + B) * l ^ r = A * l ^ r + B * l ^ r by ring]

theorem JB.smul {U : Set ℝ} {φ : ℝ → ℝ} {F : ℕ → ℝ → ℝ} {A l : ℝ} (c : ℝ)
    (hF : JB U φ F A l) : JB U (fun t => c * φ t) (jsmul c F) (|c| * A) l := by
  refine ⟨hF.1.smul c, fun r hr t ht => ?_⟩
  simp only [jsmul, abs_mul]
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (hF.2 r hr t ht) (abs_nonneg c)

theorem JB.sum {ι : Type*} {U : Set ℝ} (s : Finset ι) {φ : ι → ℝ → ℝ} {F : ι → ℕ → ℝ → ℝ}
    {A : ι → ℝ} {l : ℝ} (hF : ∀ x ∈ s, JB U (φ x) (F x) (A x) l) :
    JB U (fun t => ∑ x ∈ s, φ x t) (jsum s F) (∑ x ∈ s, A x) l := by
  refine ⟨JetOf.sum s fun x hx => (hF x hx).1, fun r hr t ht => ?_⟩
  simp only [jsum]
  rw [Finset.sum_mul]
  exact (Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum fun x hx => (hF x hx).2 r hr t ht)

theorem JB.mul {U : Set ℝ} {φ ψ : ℝ → ℝ} {F G : ℕ → ℝ → ℝ} {A B l : ℝ} (hF : JB U φ F A l)
    (hG : JB U ψ G B l) (hA : 0 ≤ A) (hB : 0 ≤ B) (hl : 0 ≤ l) :
    JB U (fun t => φ t * ψ t) (jmul F G) (8 * (A * B)) l := by
  refine ⟨hF.1.mul hG.1, fun r hr t ht => ?_⟩
  have f : ∀ k ≤ 3, |F k t| ≤ A * l ^ k := fun k hk => hF.2 k hk t ht
  have g : ∀ k ≤ 3, |G k t| ≤ B * l ^ k := fun k hk => hG.2 k hk t ht
  have m : ∀ a b, a ≤ 3 → b ≤ 3 → |F a t * G b t| ≤ A * B * l ^ (a + b) := fun a b ha hb => by
    have := w1_abs_mul_le (f a ha) (g b hb)
    rw [pow_add]
    linarith [show A * l ^ a * (B * l ^ b) = A * B * (l ^ a * l ^ b) by ring]
  have hAB : 0 ≤ A * B := mul_nonneg hA hB
  have c3 : ∀ x : ℝ, |3 * x| = 3 * |x| := fun x => by rw [abs_mul]; norm_num
  have c2 : ∀ x : ℝ, |2 * x| = 2 * |x| := fun x => by rw [abs_mul]; norm_num
  have p00 : |F 0 t * G 0 t| ≤ A * B * l ^ 0 := m 0 0 (by norm_num) (by norm_num)
  have p10 : |F 1 t * G 0 t| ≤ A * B * l ^ 1 := m 1 0 (by norm_num) (by norm_num)
  have p01 : |F 0 t * G 1 t| ≤ A * B * l ^ 1 := m 0 1 (by norm_num) (by norm_num)
  have p20 : |F 2 t * G 0 t| ≤ A * B * l ^ 2 := m 2 0 (by norm_num) (by norm_num)
  have p11 : |F 1 t * G 1 t| ≤ A * B * l ^ 2 := m 1 1 (by norm_num) (by norm_num)
  have p02 : |F 0 t * G 2 t| ≤ A * B * l ^ 2 := m 0 2 (by norm_num) (by norm_num)
  have p30 : |F 3 t * G 0 t| ≤ A * B * l ^ 3 := m 3 0 (by norm_num) (by norm_num)
  have p21 : |F 2 t * G 1 t| ≤ A * B * l ^ 3 := m 2 1 (by norm_num) (by norm_num)
  have p12 : |F 1 t * G 2 t| ≤ A * B * l ^ 3 := m 1 2 (by norm_num) (by norm_num)
  have p03 : |F 0 t * G 3 t| ≤ A * B * l ^ 3 := m 0 3 (by norm_num) (by norm_num)
  have q0 : 0 ≤ A * B * l ^ 0 := mul_nonneg hAB (pow_nonneg hl 0)
  have q1 : 0 ≤ A * B * l ^ 1 := mul_nonneg hAB (pow_nonneg hl 1)
  have q2 : 0 ≤ A * B * l ^ 2 := mul_nonneg hAB (pow_nonneg hl 2)
  rcases le_three_cases hr with rfl | rfl | rfl | rfl
  · change |F 0 t * G 0 t| ≤ 8 * (A * B) * l ^ 0
    linarith
  · change |F 1 t * G 0 t + F 0 t * G 1 t| ≤ 8 * (A * B) * l ^ 1
    have := abs_add_le (F 1 t * G 0 t) (F 0 t * G 1 t)
    linarith
  · change |F 2 t * G 0 t + 2 * (F 1 t * G 1 t) + F 0 t * G 2 t| ≤ 8 * (A * B) * l ^ 2
    have := abs_add_le (F 2 t * G 0 t + 2 * (F 1 t * G 1 t)) (F 0 t * G 2 t)
    have := abs_add_le (F 2 t * G 0 t) (2 * (F 1 t * G 1 t))
    have := c2 (F 1 t * G 1 t)
    linarith
  · change |F 3 t * G 0 t + 3 * (F 2 t * G 1 t) + 3 * (F 1 t * G 2 t) + F 0 t * G 3 t| ≤
      8 * (A * B) * l ^ 3
    have := abs_add_le (F 3 t * G 0 t + 3 * (F 2 t * G 1 t) + 3 * (F 1 t * G 2 t))
      (F 0 t * G 3 t)
    have := abs_add_le (F 3 t * G 0 t + 3 * (F 2 t * G 1 t)) (3 * (F 1 t * G 2 t))
    have := abs_add_le (F 3 t * G 0 t) (3 * (F 2 t * G 1 t))
    have := c3 (F 2 t * G 1 t)
    have := c3 (F 1 t * G 2 t)
    have q3 : 0 ≤ A * B * l ^ 3 := mul_nonneg hAB (pow_nonneg hl 3)
    linarith

theorem abs_div_pow_le {x g X : ℝ} (k : ℕ) (hx : |x| ≤ X) (hg : 1 / 2 ≤ |g|) :
    |x / g ^ k| ≤ X * 2 ^ k := by
  have hg0 : 0 < |g| := by linarith
  rw [abs_div, abs_pow, div_le_iff₀ (pow_pos hg0 k)]
  have h1 : (1 / 2 : ℝ) ^ k ≤ |g| ^ k := pow_le_pow_left₀ (by norm_num) hg k
  have h2 : (2 : ℝ) ^ k * (1 / 2) ^ k = 1 := by rw [← mul_pow]; norm_num
  have hX : 0 ≤ X := (abs_nonneg x).trans hx
  calc |x| ≤ X := hx
    _ = X * 2 ^ k * (1 / 2) ^ k := by rw [mul_assoc, h2, mul_one]
    _ ≤ X * 2 ^ k * |g| ^ k := mul_le_mul_of_nonneg_left h1 (by positivity)

/-- Bounds for `1/g` when `|g| ≥ 1/2` and `|g^{(r)}| ≤ B l^r` (`r = 1, 2, 3`). -/
theorem JB.inv {U : Set ℝ} {φ : ℝ → ℝ} {G : ℕ → ℝ → ℝ} {B l : ℝ} (hG : JetOf U φ G)
    (h0 : ∀ t ∈ U, 1 / 2 ≤ |G 0 t|) (hB : 0 ≤ B) (hl : 0 ≤ l)
    (hr : ∀ r, 1 ≤ r → r ≤ 3 → ∀ t ∈ U, |G r t| ≤ B * l ^ r) :
    JB U (fun t => (φ t)⁻¹) (jinv G) (2 + 4 * B + 48 * B ^ 2 + 96 * B ^ 3) l := by
  refine ⟨hG.inv fun t ht h => by have := h0 t ht; rw [h, abs_zero] at this; linarith,
    fun r hr' t ht => ?_⟩
  have g0 := h0 t ht
  have g1 := hr 1 le_rfl (by norm_num) t ht
  have g2 := hr 2 (by norm_num) (by norm_num) t ht
  have g3 := hr 3 (by norm_num) le_rfl t ht
  have hA : ∀ c : ℝ, 0 ≤ c → c ≤ 2 + 4 * B + 48 * B ^ 2 + 96 * B ^ 3 → ∀ k : ℕ,
      c * l ^ k ≤ (2 + 4 * B + 48 * B ^ 2 + 96 * B ^ 3) * l ^ k := fun c _ hc k =>
    mul_le_mul_of_nonneg_right hc (pow_nonneg hl k)
  have hB2 : 0 ≤ B ^ 2 := sq_nonneg B
  have hB3 : 0 ≤ B ^ 3 := pow_nonneg hB 3
  rcases le_three_cases hr' with rfl | rfl | rfl | rfl
  · simp only [jinv, if_pos, pow_zero, mul_one]
    have := abs_div_pow_le 1 (le_refl |(1 : ℝ)|) g0
    rw [pow_one, div_eq_mul_inv, one_mul, abs_one] at this
    linarith
  · simp only [jinv, one_ne_zero, if_false, if_true]
    have := abs_div_pow_le 2 (show |-G 1 t| ≤ B * l ^ 1 by rwa [abs_neg]) g0
    refine this.trans ?_
    have := hA (4 * B) (by positivity) (by nlinarith) 1
    linarith [show B * l ^ 1 * 2 ^ 2 = 4 * B * l ^ 1 by ring]
  · simp only [jinv, OfNat.ofNat_ne_zero, if_false, if_true, show (2 : ℕ) ≠ 1 by norm_num]
    have a1 := abs_div_pow_le 2 (show |-G 2 t| ≤ B * l ^ 2 by rwa [abs_neg]) g0
    have hsq : |2 * G 1 t ^ 2| ≤ 2 * (B * l) ^ 2 := by
      rw [abs_mul, abs_pow, abs_two]
      have := pow_le_pow_left₀ (abs_nonneg _) (show |G 1 t| ≤ B * l by simpa using g1) 2
      linarith
    have a2 := abs_div_pow_le 3 hsq g0
    have := abs_add_le (-G 2 t / G 0 t ^ 2) (2 * G 1 t ^ 2 / G 0 t ^ 3)
    have := hA (4 * B + 16 * B ^ 2) (by positivity) (by nlinarith) 2
    nlinarith
  · simp only [jinv, OfNat.ofNat_ne_zero, if_false, show (3 : ℕ) ≠ 1 by norm_num,
      show (3 : ℕ) ≠ 2 by norm_num]
    have a1 := abs_div_pow_le 2 (show |-G 3 t| ≤ B * l ^ 3 by rwa [abs_neg]) g0
    have hb1 : |G 1 t| ≤ B * l := by simpa using g1
    have h12 : |6 * (G 1 t * G 2 t)| ≤ 6 * (B * l * (B * l ^ 2)) := by
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 6)]
      have := w1_abs_mul_le hb1 g2
      linarith
    have a2 := abs_div_pow_le 3 h12 g0
    have h13 : |6 * G 1 t ^ 3| ≤ 6 * (B * l) ^ 3 := by
      rw [abs_mul, abs_pow, abs_of_pos (by norm_num : (0 : ℝ) < 6)]
      have := pow_le_pow_left₀ (abs_nonneg _) hb1 3
      linarith
    have a3 := abs_div_pow_le 4 h13 g0
    have := abs_sub (-G 3 t / G 0 t ^ 2 + 6 * (G 1 t * G 2 t) / G 0 t ^ 3)
      (6 * G 1 t ^ 3 / G 0 t ^ 4)
    have := abs_add_le (-G 3 t / G 0 t ^ 2) (6 * (G 1 t * G 2 t) / G 0 t ^ 3)
    have := hA (4 * B + 48 * B ^ 2 + 96 * B ^ 3) (by positivity) (by nlinarith) 3
    nlinarith

end BiluLinial.Tight.SecB
