import QuaternionAlgebra
import IcosahedralData

/-!
Real evaluation of the exact icosahedral quaternion data. An integer pair
`(a,b)` represents `(a+b*s)/4`. Algebraic bridges require `s*s = 5` explicitly;
the final specialization uses the positive square root. Closure bridges take
the exact table theorem explicitly, so this module compiles independently of
the row proofs. The assembly module supplies the checked closure theorem.
These results do not establish representative coverage or containment symmetry.
-/
namespace Phinopert

/-- Evaluate all four integer pairs without their common denominator. -/
noncomputable def iqEvalRaw (s : ℝ) (p : IQ) : QuaternionCoords :=
  (ieval s p.1, ieval s p.2.1, ieval s p.2.2.1, ieval s p.2.2.2)

/-- Evaluate the stored scalar-first quaternion, including division by four. -/
noncomputable def iqEval (s : ℝ) (p : IQ) : QuaternionCoords :=
  (ieval s p.1 / 4, ieval s p.2.1 / 4,
   ieval s p.2.2.1 / 4, ieval s p.2.2.2 / 4)

theorem iqEval_eq_quarter_smul (s : ℝ) (p : IQ) :
    iqEval s p = (1 / 4 : ℝ) • iqEvalRaw s p := by
  ext <;> simp [iqEval, iqEvalRaw] <;> ring

theorem iqEvalRaw_scale (s : ℝ) (k : ℤ) (p : IQ) :
    iqEvalRaw s (iqScale k p) = (k : ℝ) • iqEvalRaw s p := by
  ext <;> simp [iqEvalRaw, iqScale, ieval_scale]

theorem iqEval_scale (s : ℝ) (k : ℤ) (p : IQ) :
    iqEval s (iqScale k p) = (k : ℝ) • iqEval s p := by
  ext <;> simp [iqEval, iqScale, ieval_scale] <;> ring

theorem iqEval_neg (s : ℝ) (p : IQ) :
    iqEval s (iqScale (-1) p) = -iqEval s p := by
  simpa using iqEval_scale s (-1) p

theorem iqEvalRaw_mul (s : ℝ) (hs : s*s = 5) (p q : IQ) :
    iqEvalRaw s (iqMul p q) = qProduct (iqEvalRaw s p) (iqEvalRaw s q) := by
  ext <;> simp [iqEvalRaw, iqMul, qProduct, ieval_sub, ieval_add, ieval_mul s hs]

theorem iqEvalRaw_norm (s : ℝ) (hs : s*s = 5) (p : IQ) :
    ieval s (iqNorm p) = qNormSq (iqEvalRaw s p) := by
  simp [iqNorm, ieval_add, ieval_mul s hs, qNormSq, iqEvalRaw, pow_two]

/-- Raw multiplication has denominator sixteen; `iqEval` itself divides by four. -/
theorem iqEval_mul (s : ℝ) (hs : s*s = 5) (p q : IQ) :
    qProduct (iqEval s p) (iqEval s q) = (1 / 4 : ℝ) • iqEval s (iqMul p q) := by
  ext <;>
    simp [iqEval, iqMul, qProduct, ieval_sub, ieval_add, ieval_mul s hs] <;> ring

theorem iqEval_norm (s : ℝ) (hs : s*s = 5) (p : IQ) :
    qNormSq (iqEval s p) = ieval s (iqNorm p) / 16 := by
  simp [iqEval, qNormSq, iqNorm, ieval_add, ieval_mul s hs]
  ring

/-- Convert a scaled integer witness to an actual Hamilton product. -/
theorem iqEval_product_of_witness (s : ℝ) (hs : s*s = 5)
    (p q r : IQ) (k : ℤ) (h : iqMul p q = iqScale (4*k) r) :
    qProduct (iqEval s p) (iqEval s q) = (k : ℝ) • iqEval s r := by
  rw [iqEval_mul s hs, h, iqEval_scale]
  ext <;> simp <;> ring

theorem icoRaw_eval_unit (s : ℝ) (hs : s*s = 5) {p : IQ} (hp : p ∈ icoRaw) :
    qNormSq (iqEval s p) = 1 := by
  rw [iqEval_norm s hs, ico_raw_unit hp]
  norm_num [ieval]

theorem icoSignedRaw_eval_unit (s : ℝ) (hs : s*s = 5)
    {p : IQ} (hp : p ∈ icoSignedRaw) : qNormSq (iqEval s p) = 1 := by
  rcases List.mem_append.mp hp with hp | hp
  · exact icoRaw_eval_unit s hs hp
  · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hp
    rw [iqEval_neg, qNormSq_neg]
    exact icoRaw_eval_unit s hs ha

/-- The actual finite set of evaluated signed quaternions. -/
noncomputable def icoReal (s : ℝ) : Finset QuaternionCoords := by
  classical
  exact (icoSignedRaw.map (iqEval s)).toFinset

theorem mem_icoReal_iff (s : ℝ) (q : QuaternionCoords) :
    q ∈ icoReal s ↔ ∃ p ∈ icoSignedRaw, iqEval s p = q := by
  classical
  simp [icoReal]

theorem icoReal_mem_of_raw (s : ℝ) {p : IQ} (hp : p ∈ icoRaw) :
    iqEval s p ∈ icoReal s :=
  (mem_icoReal_iff s _).mpr ⟨p, List.mem_append_left _ hp, rfl⟩

theorem icoReal_neg_mem_of_raw (s : ℝ) {p : IQ} (hp : p ∈ icoRaw) :
    -iqEval s p ∈ icoReal s := by
  apply (mem_icoReal_iff s _).mpr
  exact ⟨iqScale (-1) p,
    List.mem_append_right _ (List.mem_map.mpr ⟨p, hp, rfl⟩), iqEval_neg s p⟩

theorem mem_icoReal_iff_base (s : ℝ) (q : QuaternionCoords) :
    q ∈ icoReal s ↔ ∃ p ∈ icoRaw, q = iqEval s p ∨ q = -iqEval s p := by
  constructor
  · intro hq
    obtain ⟨p, hp, rfl⟩ := (mem_icoReal_iff s q).mp hq
    rcases List.mem_append.mp hp with hp | hp
    · exact ⟨p, hp, Or.inl rfl⟩
    · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hp
      exact ⟨a, ha, Or.inr (iqEval_neg s a)⟩
  · rintro ⟨p, hp, rfl | rfl⟩
    · exact icoReal_mem_of_raw s hp
    · exact icoReal_neg_mem_of_raw s hp

theorem icoReal_neg_closed (s : ℝ) {q : QuaternionCoords} (hq : q ∈ icoReal s) :
    -q ∈ icoReal s := by
  obtain ⟨p, hp, rfl | rfl⟩ := (mem_icoReal_iff_base s q).mp hq
  · exact icoReal_neg_mem_of_raw s hp
  · simpa using icoReal_mem_of_raw s hp

theorem icoReal_unit (s : ℝ) (hs : s*s = 5)
    {q : QuaternionCoords} (hq : q ∈ icoReal s) : qNormSq q = 1 := by
  obtain ⟨p, hp, rfl⟩ := (mem_icoReal_iff s q).mp hq
  exact icoSignedRaw_eval_unit s hs hp

theorem icoAt_mem_raw (i : Fin 60) : icoAt i.val ∈ icoRaw := by
  have hi : i.val < icoRaw.length := by simpa only [ico_raw_length] using i.isLt
  simp only [icoAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi,
    Option.getD_some]
  exact List.getElem_mem hi

theorem icoRaw_mem_index {p : IQ} (hp : p ∈ icoRaw) :
    ∃ i : Fin 60, icoAt i.val = p := by
  obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp hp
  refine ⟨⟨i, by simpa only [ico_raw_length] using hi⟩, ?_⟩
  simpa [icoAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi] using he

/-- Each base product is in the signed real set, using its table witness. -/
theorem icoReal_base_product_mem_of_table (s : ℝ) (hs : s*s = 5)
    (hclosure : ∀ i : Fin 60, IcoClosureRow i.val)
    {p q : IQ} (hp : p ∈ icoRaw) (hq : q ∈ icoRaw) :
    qProduct (iqEval s p) (iqEval s q) ∈ icoReal s := by
  obtain ⟨i, rfl⟩ := icoRaw_mem_index hp
  obtain ⟨j, rfl⟩ := icoRaw_mem_index hq
  obtain ⟨hm, ht, hsign⟩ := hclosure i j
  have hreal := iqEval_product_of_witness s hs _ _ _ _ hm
  have hmem := icoAt_mem_raw ⟨(icoWitness i.val j.val).1, ht⟩
  rcases hsign with hsign | hsign
  · simp only [hsign, Int.cast_one, one_smul] at hreal
    rw [hreal]
    exact icoReal_mem_of_raw s hmem
  · simp only [hsign, Int.cast_neg, Int.cast_one, neg_one_smul] at hreal
    rw [hreal]
    exact icoReal_neg_mem_of_raw s hmem

theorem icoReal_product_closed_of_table (s : ℝ) (hs : s*s = 5)
    (hclosure : ∀ i : Fin 60, IcoClosureRow i.val)
    {p q : QuaternionCoords} (hp : p ∈ icoReal s) (hq : q ∈ icoReal s) :
    qProduct p q ∈ icoReal s := by
  obtain ⟨a, ha, rfl | rfl⟩ := (mem_icoReal_iff_base s p).mp hp <;>
    obtain ⟨b, hb, rfl | rfl⟩ := (mem_icoReal_iff_base s q).mp hq
  · exact icoReal_base_product_mem_of_table s hs hclosure ha hb
  · rw [qProduct_neg_right]
    exact icoReal_neg_closed s (icoReal_base_product_mem_of_table s hs hclosure ha hb)
  · rw [qProduct_neg_left]
    exact icoReal_neg_closed s (icoReal_base_product_mem_of_table s hs hclosure ha hb)
  · rw [qProduct_neg_left, qProduct_neg_right, neg_neg]
    exact icoReal_base_product_mem_of_table s hs hclosure ha hb

theorem icoReal_coordinate_unit_mem (s : ℝ) {p : IQ} (hp : p ∈ icoCoordinateUnits) :
    iqEval s p ∈ icoReal s := by
  apply (mem_icoReal_iff s _).mpr
  exact ⟨p, of_decide_eq_true ((List.all_eq_true.mp ico_coordinate_units_check) p hp), rfl⟩

theorem icoReal_comparison_mem (s : ℝ) {p : IQ} (hp : p ∈ icoComparisons) :
    iqEval s p ∈ icoReal s := by
  apply (mem_icoReal_iff s _).mpr
  exact ⟨p, of_decide_eq_true ((List.all_eq_true.mp ico_comparisons_check) p hp), rfl⟩

/-- All eight signed coordinate units, written directly as real quaternions. -/
theorem icoReal_coordinate_units (s : ℝ) :
    ∀ q ∈ ([(-1,0,0,0), (1,0,0,0), (0,-1,0,0), (0,1,0,0),
      (0,0,-1,0), (0,0,1,0), (0,0,0,-1), (0,0,0,1)] : List QuaternionCoords),
      q ∈ icoReal s := by
  have h : ∀ q ∈ icoCoordinateUnits.map (iqEval s), q ∈ icoReal s := by
    intro q hq
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
    exact icoReal_coordinate_unit_mem s hp
  simpa [icoCoordinateUnits, iqEval, ieval] using h

theorem icoReal_one_mem (s : ℝ) : (1, (0 : Point)) ∈ icoReal s := by
  apply icoReal_coordinate_units s
  simp

theorem icoReal_nonempty (s : ℝ) : (icoReal s).Nonempty :=
  ⟨(1, (0 : Point)), icoReal_one_mem s⟩

/-- All twelve specified comparison quaternions, with the data's ordering. -/
theorem icoReal_comparisons (s : ℝ) :
    ∀ q ∈ icoComparisons.map (iqEval s), q ∈ icoReal s := by
  intro q hq
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
  exact icoReal_comparison_mem s hp

theorem icoReal_action_dot (s : ℝ) (hs : s*s = 5)
    {q : QuaternionCoords} (hq : q ∈ icoReal s) (u v : Point) :
    dot (qAction q u) (qAction q v) = dot u v :=
  qAction_dot_of_unit q (icoReal_unit s hs hq) u v

/-- The intended positive-root specialization, with no root axiom. -/
theorem icoReal_sqrt5_properties_of_table
    (hclosure : ∀ i : Fin 60, IcoClosureRow i.val) :
    0 < Real.sqrt (5 : ℝ) ∧
    (icoReal (Real.sqrt 5)).Nonempty ∧
    (∀ q ∈ icoReal (Real.sqrt 5), qNormSq q = 1) ∧
    (∀ p ∈ icoReal (Real.sqrt 5), ∀ q ∈ icoReal (Real.sqrt 5),
      qProduct p q ∈ icoReal (Real.sqrt 5)) := by
  have hs : Real.sqrt (5 : ℝ) * Real.sqrt 5 = 5 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)]
  refine ⟨Real.sqrt_pos.mpr (by norm_num), icoReal_nonempty _, ?_, ?_⟩
  · intro q hq
    exact icoReal_unit _ hs hq
  · intro p hp q hq
    exact icoReal_product_closed_of_table _ hs hclosure hp hq

end Phinopert

#print axioms Phinopert.iqEval_eq_quarter_smul
#print axioms Phinopert.iqEvalRaw_scale
#print axioms Phinopert.iqEval_scale
#print axioms Phinopert.iqEval_neg
#print axioms Phinopert.iqEvalRaw_mul
#print axioms Phinopert.iqEvalRaw_norm
#print axioms Phinopert.iqEval_mul
#print axioms Phinopert.iqEval_norm
#print axioms Phinopert.iqEval_product_of_witness
#print axioms Phinopert.icoRaw_eval_unit
#print axioms Phinopert.icoSignedRaw_eval_unit
#print axioms Phinopert.mem_icoReal_iff
#print axioms Phinopert.icoReal_mem_of_raw
#print axioms Phinopert.icoReal_neg_mem_of_raw
#print axioms Phinopert.mem_icoReal_iff_base
#print axioms Phinopert.icoReal_neg_closed
#print axioms Phinopert.icoReal_unit
#print axioms Phinopert.icoAt_mem_raw
#print axioms Phinopert.icoRaw_mem_index
#print axioms Phinopert.icoReal_base_product_mem_of_table
#print axioms Phinopert.icoReal_product_closed_of_table
#print axioms Phinopert.icoReal_coordinate_unit_mem
#print axioms Phinopert.icoReal_comparison_mem
#print axioms Phinopert.icoReal_coordinate_units
#print axioms Phinopert.icoReal_one_mem
#print axioms Phinopert.icoReal_nonempty
#print axioms Phinopert.icoReal_comparisons
#print axioms Phinopert.icoReal_action_dot
#print axioms Phinopert.icoReal_sqrt5_properties_of_table
