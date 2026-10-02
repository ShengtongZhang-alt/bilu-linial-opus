/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import BiluLinial.Tight.SecB.WTRemEnv

/-!
# The global clip factorization of the (WT5) observables (sub-node (R1′) of TB.WT5r°)

On the core support, for every star vector `x`,
`Φ H q_L = (1-q_A)₊^{e₁} (1-q_B)₊^{e₂} · G(x)` with `e₁ = p - #(+, unshifted)`,
`e₂ = p - #(-, unshifted)` and the smooth prefactor
`G = w₊^{s₊} w₋^{s₋} Π_t (c_t ñ_t) · c_e² · q_{c₊² L}`, where `w_b = 1/ψ_δ(1 - q_{A_{b,h}})` is the
globally smooth reciprocal of the shifted clip (equal to `1/(1 - q_{A_{b,h}})` on `{q_A, q_B < 1}`)
(`starObsQ_eq_clip`, `starObsT_eq_clip`).

The bookkeeping is the abstract list identity `list_prod_key`.
-/

@[expose] public section

namespace BiluLinial.Tight.SecB.WR

open Matrix SecA.CR

/-! ### The abstract list identity -/

/-- The factor attached to a key `(b, sh)`: `α⁻¹`/`β⁻¹` (unshifted) or `w₊`/`w₋` (shifted). -/
noncomputable def keyFac (α β wp wm : ℝ) (k : Bool × Bool) : ℝ :=
  if k.2 then (if k.1 then wp else wm) else (if k.1 then α⁻¹ else β⁻¹)

/-- The number of list entries with key `k`. -/
def cntK {T : Type*} (key : T → Bool × Bool) (k : Bool × Bool) (l : List T) : ℕ :=
  l.countP fun t => key t = k

theorem cntK_cons {T : Type*} (key : T → Bool × Bool) (k : Bool × Bool) (t : T) (l : List T) :
    cntK key k (t :: l) = cntK key k l + if key t = k then 1 else 0 := by
  simp [cntK, List.countP_cons]

theorem list_prod_key {T : Type*} (key : T → Bool × Bool) (dd f : T → ℝ) {α β : ℝ}
    (hα : α ≠ 0) (hβ : β ≠ 0) (wp wm : ℝ) :
    ∀ l : List T, (∀ t ∈ l, dd t = f t * keyFac α β wp wm (key t)) → ∀ E₁ E₂ : ℕ,
      cntK key (true, false) l ≤ E₁ → cntK key (false, false) l ≤ E₂ →
      α ^ E₁ * β ^ E₂ * (l.map dd).prod =
        α ^ (E₁ - cntK key (true, false) l) * β ^ (E₂ - cntK key (false, false) l) *
          wp ^ cntK key (true, true) l * wm ^ cntK key (false, true) l * (l.map f).prod
  | [], _, E₁, E₂, _, _ => by simp [cntK]
  | t :: l, hd, E₁, E₂, h1, h2 => by
    have hdt := hd t (List.mem_cons_self ..)
    have hdl : ∀ t' ∈ l, dd t' = f t' * keyFac α β wp wm (key t') :=
      fun t' ht' => hd t' (List.mem_cons_of_mem _ ht')
    have c1 := cntK_cons key (true, false) t l
    have c2 := cntK_cons key (false, false) t l
    have c3 := cntK_cons key (true, true) t l
    have c4 := cntK_cons key (false, true) t l
    rw [c1] at h1
    rw [c2] at h2
    have h1' : cntK key (true, false) l ≤ E₁ := by split_ifs at h1 <;> omega
    have h2' : cntK key (false, false) l ≤ E₂ := by split_ifs at h2 <;> omega
    have ih := list_prod_key key dd f hα hβ wp wm l hdl E₁ E₂ h1' h2'
    simp only [List.map_cons, List.prod_cons]
    rw [hdt]
    have e0 : α ^ E₁ * β ^ E₂ * (f t * keyFac α β wp wm (key t) * (l.map dd).prod) =
        f t * keyFac α β wp wm (key t) * (α ^ E₁ * β ^ E₂ * (l.map dd).prod) := by ring
    rw [e0, ih, c1, c2, c3, c4]
    rcases hkey : key t with ⟨b, sh⟩
    try simp only [hkey] at h1 h2
    cases b <;> cases sh <;>
      simp only [keyFac, Prod.mk.injEq, Bool.false_eq_true, Bool.true_eq_false, false_and,
        and_false, and_true, and_self, if_true, if_false, add_zero] at h1 h2 ⊢
    · -- (false, false): `β⁻¹`
      have hE : E₂ - cntK key (false, false) l = (E₂ - (cntK key (false, false) l + 1)) + 1 := by
        omega
      rw [hE, pow_succ]
      field_simp
    · -- (false, true): `w₋`
      ring
    · -- (true, false): `α⁻¹`
      have hE : E₁ - cntK key (true, false) l = (E₁ - (cntK key (true, false) l + 1)) + 1 := by
        omega
      rw [hE, pow_succ]
      field_simp
    · -- (true, true): `w₊`
      ring

/-! ### Contact-level objects -/

section Contact

variable {d p : ℕ}

/-- The shift of a factor: `h` (shifted) or `0`. -/
abbrev zOf (h : ℝ) (sh : Bool) : ℝ := if sh then h else 0

/-- The core value `c_t` of a factor `t = (k, b, sh)`. -/
noncomputable def fc (ct : Contact.{u} d p) (h : ℝ) (σ : Config ct.V) (i : ct.V)
    (t : ct.V × Bool × Bool) : ℝ :=
  cVal ct.G (aOf d p) (tau t.2.1) (zOf h t.2.2) (ct.ySrc t.2.1) σ ct.S i t.1

/-- The quadratic matrix of `ñ_t = 1 + q_{fN t}`. -/
noncomputable def fN (ct : Contact.{u} d p) (h : ℝ) (σ : Config ct.V) (i : ct.V)
    (t : ct.V × Bool × Bool) : Matrix (nbhd ct.G ct.S i) (nbhd ct.G ct.S i) ℝ :=
  nMat ct.G (aOf d p) (tau t.2.1) (zOf h t.2.2) (ct.ySrc t.2.1) σ ct.S i t.1

/-- The root matrix of branch `b` (`A` for `b = true`, `B` for `b = false`). -/
noncomputable abbrev Xb (ct : Contact.{u} d p) (b : Bool) (σ : Config ct.V) (i : ct.V) :
    Matrix (nbhd ct.G ct.S i) (nbhd ct.G ct.S i) ℝ :=
  rootMat ct.G (aOf d p) (tau b) (ct.ySrc b) σ ct.S i

/-- The shifted root matrix `A_{b,h}` of branch `b`. -/
noncomputable def Ash (ct : Contact.{u} d p) (h : ℝ) (b : Bool) (σ : Config ct.V) (i : ct.V) :
    Matrix (nbhd ct.G ct.S i) (nbhd ct.G ct.S i) ℝ :=
  Az ct.G (aOf d p) (tau b) h (ct.ySrc b) σ ct.S i

/-- The cutoff level `δ_b = h y_i/(D_i + h y_i)` (`1` at a zero source). -/
noncomputable def dlt (ct : Contact.{u} d p) (h : ℝ) (b : Bool) (i : ct.V) : ℝ :=
  if ct.ySrc b i = 0 then 1 else
    h * ct.ySrc b i / (diagD ct.G (aOf d p) (ct.ySrc b) ct.S i + h * ct.ySrc b i)

/-- The smooth reciprocal power `w_b^k = ψ_δ(1 - q_{A_{b,h}})^{-k}`. -/
noncomputable def wR (ct : Contact.{u} d p) (h : ℝ) (b : Bool) (σ : Config ct.V) (i : ct.V)
    (k : ℕ) : (nbhd ct.G ct.S i → ℝ) → ℝ :=
  fun x => (psiCut (dlt ct h b i) (quadFn 1 0 (-Ash ct h b σ i) x))⁻¹ ^ k

/-- The clip exponents and shifted counts. -/
def eOne (p : ℕ) {T : Type*} (l : List (T × Bool × Bool)) : ℕ :=
  p - cntK (fun t => t.2) (true, false) l

def eTwo (p : ℕ) {T : Type*} (l : List (T × Bool × Bool)) : ℕ :=
  p - cntK (fun t => t.2) (false, false) l

def sP {T : Type*} (e : Bool) (l : List (T × Bool × Bool)) : ℕ :=
  cntK (fun t => t.2) (true, true) l + 2 + if e then 2 else 0

def sM {T : Type*} (e : Bool) (l : List (T × Bool × Bool)) : ℕ :=
  cntK (fun t => t.2) (false, true) l + if e then 0 else 2

/-- The `k = i` core values `c_e`, `c₊`. -/
noncomputable def cE (ct : Contact.{u} d p) (h : ℝ) (e : Bool) (σ : Config ct.V) (i : ct.V) :
    ℝ :=
  cVal ct.G (aOf d p) (tau e) h (ct.ySrc e) σ ct.S i i

/-- The list prefactor `Π_t c_t ñ_t(x)`. -/
noncomputable def Pl (ct : Contact.{u} d p) (h : ℝ) (σ : Config ct.V) (i : ct.V)
    (l : List (ct.V × Bool × Bool)) (x : nbhd ct.G ct.S i → ℝ) : ℝ :=
  (l.map fun t => fc ct h σ i t * quadFn 1 0 (fN ct h σ i t) x).prod

/-- The smooth prefactor of `Φ H q_L`. -/
noncomputable def GQ (ct : Contact.{u} d p) (h : ℝ) (e dir : Bool) (i : ct.V)
    (l : List (ct.V × Bool × Bool)) (σ : Config ct.V) : (nbhd ct.G ct.S i → ℝ) → ℝ :=
  fun x => wR ct h true σ i (sP e l) x * wR ct h false σ i (sM e l) x * Pl ct h σ i l x *
    (cE ct h e σ i ^ 2 * qForm (cE ct h true σ i ^ 2 • kerL ct h e dir i σ) x)

/-- The smooth prefactor of `tr L · Φ H`. -/
noncomputable def GT (ct : Contact.{u} d p) (h : ℝ) (e dir : Bool) (i : ct.V)
    (l : List (ct.V × Bool × Bool)) (σ : Config ct.V) : (nbhd ct.G ct.S i → ℝ) → ℝ :=
  fun x => wR ct h true σ i (sP e l) x * wR ct h false σ i (sM e l) x * Pl ct h σ i l x *
    (cE ct h e σ i ^ 2 * (cE ct h true σ i ^ 2 * (kerL ct h e dir i σ).trace))

theorem ySrc_nonneg (ct : Contact.{u} d p) (b : Bool) (k : ct.V) : 0 ≤ ct.ySrc b k := by
  cases b
  · exact (ct.ctx.hym k).1
  · exact (ct.ctx.hyp k).1

theorem tau_sq (b : Bool) : tau b ^ 2 = 1 := by cases b <;> norm_num [tau]

theorem wtCore_pd (ct : Contact.{u} d p) {σ : Config ct.V} {i : ct.V}
    (hw : wtCore ct.G p (aOf d p) ct.yp ct.ym σ ct.S i ≠ 0) (b : Bool) :
    (precCore ct.G (aOf d p) (tau b) (ct.ySrc b) σ ct.S i).PosDef := by
  unfold wtCore at hw
  split_ifs at hw with hc
  · cases b
    · exact hc.2
    · exact hc.1
  · exact absurd rfl hw

/-- `q_{A_{b,h}} ≤ (D/(D + h y_i)) q_{X_b}`, so on `{q_{X_b} < 1}`:
`δ_b ≤ 1 - q_{A_{b,h}}` and `1 - q_{A_{b,h}} ≥ (1 - q_{X_b})/(1 + 2h)` (`y_i ≤ 2`). -/
theorem Ash_facts (ct : Contact.{u} d p) {h : ℝ} (hh : 0 < h) (b : Bool) {σ : Config ct.V}
    {i : ct.V} (hM : (precCore ct.G (aOf d p) (tau b) (ct.ySrc b) σ ct.S i).PosDef)
    (hy2 : ct.ySrc b i ≤ 2) (x : nbhd ct.G ct.S i → ℝ) (hx : qForm (Xb ct b σ i) x < 1) :
    0 < dlt ct h b i ∧ dlt ct h b i ≤ 1 - qForm (Ash ct h b σ i) x ∧
      (1 - qForm (Xb ct b σ i) x) / (1 + 2 * h) ≤ 1 - qForm (Ash ct h b σ i) x ∧
      qForm (Ash ct h b σ i) x ≤ qForm (Xb ct b σ i) x := by
  have hy := ySrc_nonneg ct b
  have hD1 : 1 ≤ diagD ct.G (aOf d p) (ct.ySrc b) ct.S i := FloorIns.one_le_diagD ct.G _ hy _ _
  have hDz := diagD_add_pos ct.G (aOf d p) hy ct.S i hh.le
  have hle : qForm (Ash ct h b σ i) x ≤ diagD ct.G (aOf d p) (ct.ySrc b) ct.S i /
      (diagD ct.G (aOf d p) (ct.ySrc b) ct.S i + h * ct.ySrc b i) * qForm (Xb ct b σ i) x :=
    qForm_Az_le ct.G hy hh.le hM x
  have hle' : qForm (Ash ct h b σ i) x ≤ qForm (Xb ct b σ i) x :=
    qForm_Az_le_root ct.G hy hh.le hM x
  have hqX := qForm_nonneg (SecA.rootMat_posSemidef ct.G hy hM) x
  have hzero : ct.ySrc b i = 0 → qForm (Ash ct h b σ i) x = 0 := fun h0 => by
    rw [Ash, qForm_Az_dot, h0]
    simp
  have hyi := hy i
  have hc0 : 0 ≤ diagD ct.G (aOf d p) (ct.ySrc b) ct.S i /
      (diagD ct.G (aOf d p) (ct.ySrc b) ct.S i + h * ct.ySrc b i) :=
    div_nonneg (by linarith) hDz.le
  have hc1 : diagD ct.G (aOf d p) (ct.ySrc b) ct.S i /
      (diagD ct.G (aOf d p) (ct.ySrc b) ct.S i + h * ct.ySrc b i) ≤ 1 :=
    (div_le_one hDz).2 (by nlinarith)
  refine ⟨?_, ?_, ?_, hle'⟩
  · unfold dlt
    split_ifs with h0
    · exact one_pos
    · have hy0 : 0 < ct.ySrc b i := lt_of_le_of_ne hyi (Ne.symm h0)
      positivity
  · unfold dlt
    split_ifs with h0
    · rw [hzero h0]
      norm_num
    · have e1 : h * ct.ySrc b i / (diagD ct.G (aOf d p) (ct.ySrc b) ct.S i + h * ct.ySrc b i) =
          1 - diagD ct.G (aOf d p) (ct.ySrc b) ct.S i /
            (diagD ct.G (aOf d p) (ct.ySrc b) ct.S i + h * ct.ySrc b i) := by
        field_simp
        ring
      rw [e1]
      nlinarith
  · have hlow : diagD ct.G (aOf d p) (ct.ySrc b) ct.S i /
        (diagD ct.G (aOf d p) (ct.ySrc b) ct.S i + h * ct.ySrc b i) *
          (1 - qForm (Xb ct b σ i) x) ≤ 1 - qForm (Ash ct h b σ i) x := by
      have : qForm (Ash ct h b σ i) x ≤ diagD ct.G (aOf d p) (ct.ySrc b) ct.S i /
          (diagD ct.G (aOf d p) (ct.ySrc b) ct.S i + h * ct.ySrc b i) *
            qForm (Xb ct b σ i) x := hle
      nlinarith
    have hfrac : 1 / (1 + 2 * h) ≤ diagD ct.G (aOf d p) (ct.ySrc b) ct.S i /
        (diagD ct.G (aOf d p) (ct.ySrc b) ct.S i + h * ct.ySrc b i) := by
      rw [div_le_div_iff₀ (by positivity) hDz]
      nlinarith
    have h1qX : 0 ≤ 1 - qForm (Xb ct b σ i) x := by linarith
    calc (1 - qForm (Xb ct b σ i) x) / (1 + 2 * h)
        = 1 / (1 + 2 * h) * (1 - qForm (Xb ct b σ i) x) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hfrac h1qX
      _ ≤ 1 - qForm (Ash ct h b σ i) x := hlow

theorem ySrc_le_two (hR : TRegime d p) (ct : Contact.{u} d p) (b : Bool) (k : ct.V) :
    ct.ySrc b k ≤ 2 := by
  have hs := SecA.sOf_le_two hR
  have hl : ct.lam * sOf d p ≤ 2 :=
    (mul_le_of_le_one_left hR.sOf_pos.le ct.ctx.lam_le_one).trans hs
  cases b
  · exact (ct.ctx.hym k).2.trans hl
  · exact (ct.ctx.hyp k).2.trans hl

/-- On `{q_A, q_B < 1}`, `w_b = 1/(1 - q_{A_{b,h}})`. -/
theorem wR_one_eq (ct : Contact.{u} d p) {h : ℝ} (hh : 0 < h) (b : Bool) {σ : Config ct.V}
    {i : ct.V} (hM : (precCore ct.G (aOf d p) (tau b) (ct.ySrc b) σ ct.S i).PosDef)
    (hy2 : ct.ySrc b i ≤ 2) (x : nbhd ct.G ct.S i → ℝ) (hx : qForm (Xb ct b σ i) x < 1) :
    wR ct h b σ i 1 x = (1 - qForm (Ash ct h b σ i) x)⁻¹ := by
  obtain ⟨hδ, hδq, -, -⟩ := Ash_facts ct hh b hM hy2 x hx
  simp only [wR, pow_one]
  rw [SecA.StarCalc.quadFn_one_zero_neg, psiCut_eq hδ (by linarith)]

/-- **Per-factor identity** on `{q_A, q_B < 1}`. -/
theorem diag_factor (ct : Contact.{u} d p) {h : ℝ} (hh : 0 < h) (hy2 : ∀ b k, ct.ySrc b k ≤ 2)
    {σ : Config ct.V} {i : ct.V} (hi : i ∈ ct.S)
    (hw : wtCore ct.G p (aOf d p) ct.yp ct.ym σ ct.S i ≠ 0) (x : nbhd ct.G ct.S i → ℝ)
    (hA : qForm (rootA ct σ i) x < 1) (hB : qForm (rootB ct σ i) x < 1)
    (t : ct.V × Bool × Bool) :
    diagSub ct.G (aOf d p) (if t.2.1 then 1 else -1) (if t.2.2 then h else 0) (ct.ySrc t.2.1) σ
        ct.S i x t.1 =
      fc ct h σ i t * quadFn 1 0 (fN ct h σ i t) x *
        keyFac (1 - qForm (rootA ct σ i) x) (1 - qForm (rootB ct σ i) x)
          (wR ct h true σ i 1 x) (wR ct h false σ i 1 x) t.2 := by
  obtain ⟨k, b, sh⟩ := t
  have hM := wtCore_pd ct hw b
  have hy := ySrc_nonneg ct b
  have hXb : qForm (Xb ct b σ i) x < 1 := by
    cases b
    · exact hB
    · exact hA
  have hz : (0 : ℝ) ≤ zOf h sh := by cases sh <;> simp [zOf, hh.le]
  obtain ⟨hδ, hδq, -, hle⟩ := Ash_facts ct hh b hM (hy2 b i) x hXb
  have hq : qForm (Az ct.G (aOf d p) (tau b) (zOf h sh) (ct.ySrc b) σ ct.S i) x <
      1 - 0 := by
    cases sh
    · simp only [zOf, Bool.false_eq_true, if_false, Az_zero, sub_zero]
      exact hXb
    · simp only [zOf, if_true, sub_zero]
      exact lt_of_le_of_lt hle hXb
  rw [sub_zero] at hq
  have hst := star_factor ct.G (tau_sq b) hy hz σ hi hM x hq k
  have hpos : 0 < 1 - qForm (Az ct.G (aOf d p) (tau b) (zOf h sh) (ct.ySrc b) σ ct.S i) x := by
    linarith
  have hdiag : diagSub ct.G (aOf d p) (tau b) (zOf h sh) (ct.ySrc b) σ ct.S i x k =
      cVal ct.G (aOf d p) (tau b) (zOf h sh) (ct.ySrc b) σ ct.S i k *
        quadFn 1 0 (nMat ct.G (aOf d p) (tau b) (zOf h sh) (ct.ySrc b) σ ct.S i k) x *
          (1 - qForm (Az ct.G (aOf d p) (tau b) (zOf h sh) (ct.ySrc b) σ ct.S i) x)⁻¹ := by
    rw [← hst]
    field_simp
  change diagSub ct.G (aOf d p) (tau b) (zOf h sh) (ct.ySrc b) σ ct.S i x k = _
  rw [hdiag]
  simp only [fc, fN]
  congr 1
  cases sh
  · simp only [zOf, Bool.false_eq_true, if_false, Az_zero, keyFac]
    cases b <;> rfl
  · simp only [zOf, if_true, keyFac]
    rw [show Az ct.G (aOf d p) (tau b) h (ct.ySrc b) σ ct.S i = Ash ct h b σ i from rfl,
      ← wR_one_eq ct hh b hM (hy2 b i) x hXb]
    cases b <;> rfl

theorem quadFn_zero_mat {ι : Type*} [Fintype ι] (x : ι → ℝ) :
    quadFn 1 0 (0 : Matrix ι ι ℝ) x = 1 := by
  simp [quadFn, qForm]

/-- The `k = i` diagonals: `y_i ((P̃(x) + hY)⁻¹)_ii = c_b w_b(x)`. -/
theorem diag_root (ct : Contact.{u} d p) {h : ℝ} (hh : 0 < h) (hy2 : ∀ b k, ct.ySrc b k ≤ 2)
    {σ : Config ct.V} {i : ct.V} (hi : i ∈ ct.S)
    (hw : wtCore ct.G p (aOf d p) ct.yp ct.ym σ ct.S i ≠ 0) (x : nbhd ct.G ct.S i → ℝ)
    (hA : qForm (rootA ct σ i) x < 1) (hB : qForm (rootB ct σ i) x < 1) (b : Bool) :
    diagSub ct.G (aOf d p) (if b then 1 else -1) h (ct.ySrc b) σ ct.S i x i =
      cE ct h b σ i * wR ct h b σ i 1 x := by
  have h1 := diag_factor ct hh hy2 hi hw x hA hB (i, b, true)
  simp only [if_true] at h1
  rw [h1]
  have hN : fN ct h σ i (i, b, true) = 0 := by simp [fN, nMat]
  rw [hN, quadFn_zero_mat, mul_one]
  simp only [fc, cE, keyFac, if_true, zOf]
  cases b <;> rfl

theorem qForm_smul' {ι : Type*} [Fintype ι] (c : ℝ) (M : Matrix ι ι ℝ) (x : ι → ℝ) :
    qForm (c • M) x = c * qForm M x := by
  simp [qForm, smul_mulVec, dotProduct_smul]

/-- `Φ H` on `{q_A, q_B < 1}` in factored form. -/
theorem phiH_eq (ct : Contact.{u} d p) {h : ℝ} (hh : 0 < h) (hy2 : ∀ b k, ct.ySrc b k ≤ 2)
    (e : Bool) {i : ct.V} (hi : i ∈ ct.S) (l : List (ct.V × Bool × Bool)) (hl : l.length < p)
    {σ : Config ct.V} (hw : wtCore ct.G p (aOf d p) ct.yp ct.ym σ ct.S i ≠ 0)
    (x : nbhd ct.G ct.S i → ℝ) (hA : qForm (rootA ct σ i) x < 1)
    (hB : qForm (rootB ct σ i) x < 1) :
    starPhi p (rootA ct σ i) (rootB ct σ i) x * wtHSub ct h e i l σ x =
      (1 - qForm (rootA ct σ i) x) ^ eOne p l * (1 - qForm (rootB ct σ i) x) ^ eTwo p l *
        (wR ct h true σ i (sP e l) x * wR ct h false σ i (sM e l) x * Pl ct h σ i l x *
          (cE ct h e σ i ^ 2 * cE ct h true σ i ^ 2)) := by
  set α := 1 - qForm (rootA ct σ i) x with hα
  set β := 1 - qForm (rootB ct σ i) x with hβ
  have hα0 : 0 < α := by linarith
  have hβ0 : 0 < β := by linarith
  have hphi : starPhi p (rootA ct σ i) (rootB ct σ i) x = α ^ p * β ^ p := by
    simp only [starPhi, clipF]
    rw [max_eq_left hα0.le, max_eq_left hβ0.le]
  have hcnt1 : cntK (fun t : ct.V × Bool × Bool => t.2) (true, false) l ≤ p :=
    (List.countP_le_length).trans hl.le
  have hcnt2 : cntK (fun t : ct.V × Bool × Bool => t.2) (false, false) l ≤ p :=
    (List.countP_le_length).trans hl.le
  have hlist := list_prod_key (fun t : ct.V × Bool × Bool => t.2)
    (fun t => diagSub ct.G (aOf d p) (if t.2.1 then 1 else -1) (if t.2.2 then h else 0)
      (ct.ySrc t.2.1) σ ct.S i x t.1)
    (fun t => fc ct h σ i t * quadFn 1 0 (fN ct h σ i t) x) hα0.ne' hβ0.ne' (wR ct h true σ i 1 x) (wR ct h false σ i 1 x) l
    (fun t _ => diag_factor ct hh hy2 hi hw x hA hB t) p p hcnt1 hcnt2
  have hE := diag_root ct hh hy2 hi hw x hA hB e
  have hP : diagSub ct.G (aOf d p) 1 h ct.yp σ ct.S i x i =
      cE ct h true σ i * wR ct h true σ i 1 x := diag_root ct hh hy2 hi hw x hA hB true
  rw [hphi, wtHSub, diagWSub, hE, hP]
  have key : ∀ X Y Z : ℝ, α ^ p * β ^ p * (X * Y ^ 2 * Z ^ 2) =
      (α ^ p * β ^ p * X) * Y ^ 2 * Z ^ 2 := fun X Y Z => by ring
  rw [key, hlist]
  simp only [wR, eOne, eTwo, sP, sM, Pl]
  cases e
  · simp only [Bool.false_eq_true, if_false, add_zero]
    ring
  · simp only [if_true, add_zero]
    ring

/-- **Global clip factorization** of `Φ H q_L` on the core support. -/
theorem starObsQ_eq_clip (ct : Contact.{u} d p) {h : ℝ} (hh : 0 < h)
    (hy2 : ∀ b k, ct.ySrc b k ≤ 2) (e dir : Bool) {i : ct.V} (hi : i ∈ ct.S)
    (l : List (ct.V × Bool × Bool)) (hl : l.length < p) {σ : Config ct.V}
    (hw : wtCore ct.G p (aOf d p) ct.yp ct.ym σ ct.S i ≠ 0) :
    starObsQ ct h e dir i l σ =
      clipObs (GQ ct h e dir i l σ) (eOne p l) (eTwo p l) (rootA ct σ i) (rootB ct σ i) := by
  funext x
  simp only [starObsQ, if_pos hw, clipObs]
  have he1 : 1 ≤ eOne p l := by
    have := (List.countP_le_length (p := fun t : ct.V × Bool × Bool => decide (t.2 = (true, false)))
      (l := l))
    simp only [eOne, cntK]
    omega
  have he2 : 1 ≤ eTwo p l := by
    have := (List.countP_le_length (p := fun t : ct.V × Bool × Bool => decide (t.2 = (false, false)))
      (l := l))
    simp only [eTwo, cntK]
    omega
  have hp1 : 1 ≤ p := by omega
  by_cases hU : qForm (rootA ct σ i) x < 1 ∧ qForm (rootB ct σ i) x < 1
  · have hα0 : 0 < 1 - qForm (rootA ct σ i) x := by linarith [hU.1]
    have hβ0 : 0 < 1 - qForm (rootB ct σ i) x := by linarith [hU.2]
    have hcA : clipF (rootA ct σ i) x = 1 - qForm (rootA ct σ i) x := max_eq_left hα0.le
    have hcB : clipF (rootB ct σ i) x = 1 - qForm (rootB ct σ i) x := max_eq_left hβ0.le
    rw [← mul_assoc, phiH_eq ct hh hy2 e hi l hl hw x hU.1 hU.2, hcA, hcB, GQ, qForm_smul']
    ring
  · have h0 : clipF (rootA ct σ i) x = 0 ∨ clipF (rootB ct σ i) x = 0 := by
      rcases not_and_or.1 hU with h | h
      · left
        exact max_eq_right (by linarith [not_lt.1 h])
      · right
        exact max_eq_right (by linarith [not_lt.1 h])
    have hphi : starPhi p (rootA ct σ i) (rootB ct σ i) x = 0 := by
      simp only [starPhi]
      rcases h0 with h | h <;> rw [h] <;> simp [zero_pow (by omega : p ≠ 0)]
    rw [hphi, zero_mul]
    rcases h0 with h | h <;> rw [h] <;> simp [zero_pow (by omega : eOne p l ≠ 0),
      zero_pow (by omega : eTwo p l ≠ 0)]

/-- **Global clip factorization** of `tr L · Φ H` on the core support. -/
theorem starObsT_eq_clip (ct : Contact.{u} d p) {h : ℝ} (hh : 0 < h)
    (hy2 : ∀ b k, ct.ySrc b k ≤ 2) (e dir : Bool) {i : ct.V} (hi : i ∈ ct.S)
    (l : List (ct.V × Bool × Bool)) (hl : l.length < p) {σ : Config ct.V}
    (hw : wtCore ct.G p (aOf d p) ct.yp ct.ym σ ct.S i ≠ 0) :
    starObsT ct h e dir i l σ =
      clipObs (GT ct h e dir i l σ) (eOne p l) (eTwo p l) (rootA ct σ i) (rootB ct σ i) := by
  funext x
  simp only [starObsT, if_pos hw, clipObs]
  have he1 : 1 ≤ eOne p l := by
    have := (List.countP_le_length (p := fun t : ct.V × Bool × Bool => decide (t.2 = (true, false)))
      (l := l))
    simp only [eOne, cntK]
    omega
  have he2 : 1 ≤ eTwo p l := by
    have := (List.countP_le_length (p := fun t : ct.V × Bool × Bool => decide (t.2 = (false, false)))
      (l := l))
    simp only [eTwo, cntK]
    omega
  have hp1 : 1 ≤ p := by omega
  by_cases hU : qForm (rootA ct σ i) x < 1 ∧ qForm (rootB ct σ i) x < 1
  · have hα0 : 0 < 1 - qForm (rootA ct σ i) x := by linarith [hU.1]
    have hβ0 : 0 < 1 - qForm (rootB ct σ i) x := by linarith [hU.2]
    have hcA : clipF (rootA ct σ i) x = 1 - qForm (rootA ct σ i) x := max_eq_left hα0.le
    have hcB : clipF (rootB ct σ i) x = 1 - qForm (rootB ct σ i) x := max_eq_left hβ0.le
    rw [phiH_eq ct hh hy2 e hi l hl hw x hU.1 hU.2, hcA, hcB, GT]
    ring
  · have h0 : clipF (rootA ct σ i) x = 0 ∨ clipF (rootB ct σ i) x = 0 := by
      rcases not_and_or.1 hU with h | h
      · left
        exact max_eq_right (by linarith [not_lt.1 h])
      · right
        exact max_eq_right (by linarith [not_lt.1 h])
    have hphi : starPhi p (rootA ct σ i) (rootB ct σ i) x = 0 := by
      simp only [starPhi]
      rcases h0 with h | h <;> rw [h] <;> simp [zero_pow (by omega : p ≠ 0)]
    rw [hphi, zero_mul, mul_zero]
    rcases h0 with h | h <;> rw [h] <;> simp [zero_pow (by omega : eOne p l ≠ 0),
      zero_pow (by omega : eTwo p l ≠ 0)]

end Contact

end BiluLinial.Tight.SecB.WR
