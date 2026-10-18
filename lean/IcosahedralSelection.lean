import RepresentativeSelection
import IcosahedralReal
import CayleyCompatibility

/-!
Actual icosahedral quaternion selection, conditional only on the finite closure
rows. This imports data and the conditional real bridge, not the closure-row
proof modules. It does not assert physical representative coverage.
-/
namespace Phinopert

/-- The actual signed quaternion list in the positive-root coordinate frame. -/
noncomputable def icoSelectionGroup : List QuaternionCoords :=
  icoSignedRaw.map (iqEval (Real.sqrt 5))

theorem mem_icoSelectionGroup (q : QuaternionCoords) :
    q ∈ icoSelectionGroup ↔ q ∈ icoReal (Real.sqrt 5) := by
  rw [mem_icoReal_iff]
  simp [icoSelectionGroup]

theorem icoSelectionGroup_unit {q : QuaternionCoords} (hq : q ∈ icoSelectionGroup) :
    qNormSq q = 1 :=
  icoReal_unit _ sqrt5_spec.1 ((mem_icoSelectionGroup q).mp hq)

theorem icoSelectionGroup_neg_closed {q : QuaternionCoords} (hq : q ∈ icoSelectionGroup) :
    -q ∈ icoSelectionGroup :=
  (mem_icoSelectionGroup _).mpr (icoReal_neg_closed _ ((mem_icoSelectionGroup q).mp hq))

theorem icoSelectionGroup_coordinate_units :
    ∀ e ∈ quaternionCoordinateUnits, e ∈ icoSelectionGroup := by
  intro e he
  apply (mem_icoSelectionGroup e).mpr
  apply icoReal_coordinate_units
  simp only [quaternionCoordinateUnits, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl <;> simp

theorem icoSelectionGroup_product_closed_of_table
    (htable : ∀ i : Fin 60, IcoClosureRow i.val)
    {g h : QuaternionCoords} (hg : g ∈ icoSelectionGroup) (hh : h ∈ icoSelectionGroup) :
    qProduct g h ∈ icoSelectionGroup := by
  apply (mem_icoSelectionGroup _).mpr
  exact icoReal_product_closed_of_table _ sqrt5_spec.1 htable
    ((mem_icoSelectionGroup g).mp hg) ((mem_icoSelectionGroup h).mp hh)

/-- All finite-group obligations have been discharged except the explicitly
supplied closure table. Both signed comparison families hold for one maximizer. -/
theorem ico_quaternion_selection_of_table
    (htable : ∀ i : Fin 60, IcoClosureRow i.val)
    (p j : QuaternionCoords)
    (hp : qNormSq p = 1) (hj : qNormSq j = 1)
    (hjj : qProduct j j = (-1, (0 : Point))) :
    ∃ q ∈ quaternionCandidates icoSelectionGroup p j,
      qNormSq q = 1 ∧ 1/2 ≤ q.1 ∧
      (∀ v ∈ quaternionCandidates icoSelectionGroup p j, v.1 ≤ q.1) ∧
      (∀ g ∈ icoSelectionGroup,
        (-q.1 ≤ (qProduct q g).1 ∧ (qProduct q g).1 ≤ q.1) ∧
        (-q.1 ≤ (qProduct (qProduct j q) g).1 ∧
          (qProduct (qProduct j q) g).1 ≤ q.1)) := by
  exact finite_quaternion_candidate_selection_signed icoSelectionGroup p j
    (fun _ hg _ hh => icoSelectionGroup_product_closed_of_table htable hg hh)
    (fun _ hg => icoSelectionGroup_neg_closed hg)
    icoSelectionGroup_coordinate_units
    (fun _ hg => icoSelectionGroup_unit hg) hp hj hjj

/-- Pure unit quaternion for the half-turn about the view (s,t,1). -/
noncomputable def icoViewHalfturn (s t : ℝ) : QuaternionCoords :=
  (0, s / Real.sqrt (1+s^2+t^2), t / Real.sqrt (1+s^2+t^2),
    1 / Real.sqrt (1+s^2+t^2))

theorem icoViewHalfturn_unit (s t : ℝ) : qNormSq (icoViewHalfturn s t) = 1 := by
  have hpos : 0 < 1+s^2+t^2 := by positivity
  have hn : Real.sqrt (1+s^2+t^2) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hpos)
  have hs := Real.sq_sqrt hpos.le
  dsimp [qNormSq, icoViewHalfturn]
  generalize hN : Real.sqrt (1+s^2+t^2) = N at *
  field_simp [hn]
  nlinarith

theorem icoViewHalfturn_square (s t : ℝ) :
    qProduct (icoViewHalfturn s t) (icoViewHalfturn s t) = (-1, (0 : Point)) := by
  have hu := icoViewHalfturn_unit s t
  dsimp [qNormSq, icoViewHalfturn] at hu
  simp only [one_div] at hu
  ext <;> simp [qProduct, icoViewHalfturn] <;> nlinarith [hu]

/-- The view-specialized actual-group theorem needs only a unit input p and
the closure table; all properties of the view half-turn are proved here. -/
theorem ico_view_selection_of_table
    (htable : ∀ i : Fin 60, IcoClosureRow i.val)
    (p : QuaternionCoords) (hp : qNormSq p = 1) (s t : ℝ) :
    ∃ q ∈ quaternionCandidates icoSelectionGroup p (icoViewHalfturn s t),
      qNormSq q = 1 ∧ 1/2 ≤ q.1 ∧
      (∀ v ∈ quaternionCandidates icoSelectionGroup p (icoViewHalfturn s t), v.1 ≤ q.1) ∧
      (∀ g ∈ icoSelectionGroup,
        (-q.1 ≤ (qProduct q g).1 ∧ (qProduct q g).1 ≤ q.1) ∧
        (-q.1 ≤ (qProduct (qProduct (icoViewHalfturn s t) q) g).1 ∧
          (qProduct (qProduct (icoViewHalfturn s t) q) g).1 ≤ q.1)) :=
  ico_quaternion_selection_of_table htable p (icoViewHalfturn s t) hp
    (icoViewHalfturn_unit s t) (icoViewHalfturn_square s t)

/-- Finite Cayley coordinates of a selected quaternion with positive scalar. -/
noncomputable def icoSelectedVector (q : QuaternionCoords) : Point :=
  (q.2.1 / q.1, q.2.2.1 / q.1, q.2.2.2 / q.1)

theorem ico_normalized_fold_identity (s t : ℝ) (q g : QuaternionCoords) (hq : q.1 ≠ 0) :
    Real.sqrt (1+s^2+t^2) * (qProduct (qProduct (icoViewHalfturn s t) q) g).1 =
      q.1 * (qProduct (qProduct (0, (s,t,1)) (1, icoSelectedVector q)) g).1 := by
  let N := Real.sqrt (1+s^2+t^2)
  have hn : N ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr (by positivity))
  have hj : icoViewHalfturn s t = (1/N) • ((0, (s,t,1)) : QuaternionCoords) := by
    ext <;> simp [icoViewHalfturn, N, div_eq_mul_inv] <;> ring
  have hnormal : q = q.1 • (1, icoSelectedVector q) := normalise_nonzero_scalar q hq
  have he : qProduct (qProduct (icoViewHalfturn s t) q) g =
      (1/N*q.1) • qProduct (qProduct (0, (s,t,1)) (1, icoSelectedVector q)) g := by
    calc
      _ = qProduct (qProduct ((1/N) • (0, (s,t,1)))
          (q.1 • (1, icoSelectedVector q))) g := by
        rw [hj]
        exact congrArg (fun z => qProduct (qProduct ((1/N) • (0, (s,t,1))) z) g) hnormal
      _ = _ := by
        simp only [qProduct_smul_left, qProduct_smul_right, smul_smul, mul_comm]
  have hc : N*(1/N*q.1) = q.1 := by
    rw [← mul_assoc, mul_one_div_cancel hn, one_mul]
  rw [he]
  change N * ((1/N*q.1) * _) = q.1 * _
  rw [← mul_assoc, hc]

/-- The signed left-half-turn comparisons imply the actual normalized fold
polynomial inequality. No bound on that polynomial is assumed. -/
theorem ico_normalized_fold_bound (s t : ℝ) (q g : QuaternionCoords)
    (hq : 0 < q.1)
    (hcomp : -q.1 ≤ (qProduct (qProduct (icoViewHalfturn s t) q) g).1 ∧
      (qProduct (qProduct (icoViewHalfturn s t) q) g).1 ≤ q.1) :
    (-g.1 * dot (s,t,1) (icoSelectedVector q) -
      dot g.2 ((s,t,1) + cross3 (s,t,1) (icoSelectedVector q)))^2 ≤ 1+s^2+t^2 := by
  let L := (qProduct (qProduct (0, (s,t,1)) (1, icoSelectedVector q)) g).1
  have he := ico_normalized_fold_identity s t q g (ne_of_gt hq)
  have hup := mul_le_mul_of_nonneg_left hcomp.2 (Real.sqrt_nonneg (1+s^2+t^2))
  have hlo := mul_le_mul_of_nonneg_left hcomp.1 (Real.sqrt_nonneg (1+s^2+t^2))
  rw [he] at hup hlo
  have hp : L ≤ Real.sqrt (1+s^2+t^2) := by
    apply (mul_le_mul_left hq).mp
    dsimp [L]
    nlinarith [hup]
  have hm : -L ≤ Real.sqrt (1+s^2+t^2) := by
    apply (mul_le_mul_left hq).mp
    dsimp [L]
    nlinarith [hlo]
  have hb := squared_fold_bound s t L hp hm
  dsimp [L] at hb
  rwa [qProduct_scalar_fold] at hb

/-- All sixty base fold inequalities follow simultaneously for the actual
selected representative (indeed the result holds for every signed entry). -/
theorem ico_view_selection_folds_of_table
    (htable : ∀ i : Fin 60, IcoClosureRow i.val)
    (p : QuaternionCoords) (hp : qNormSq p = 1) (s t : ℝ) :
    ∃ q ∈ quaternionCandidates icoSelectionGroup p (icoViewHalfturn s t),
      qNormSq q = 1 ∧ 1/2 ≤ q.1 ∧
      (∀ g ∈ icoSelectionGroup,
        (-q.1 ≤ (qProduct q g).1 ∧ (qProduct q g).1 ≤ q.1) ∧
        (-q.1 ≤ (qProduct (qProduct (icoViewHalfturn s t) q) g).1 ∧
          (qProduct (qProduct (icoViewHalfturn s t) q) g).1 ≤ q.1) ∧
        (-g.1 * dot (s,t,1) (icoSelectedVector q) -
          dot g.2 ((s,t,1) + cross3 (s,t,1) (icoSelectedVector q)))^2 ≤ 1+s^2+t^2) := by
  obtain ⟨q, hq, hu, hhalf, _, hcomp⟩ := ico_view_selection_of_table htable p hp s t
  refine ⟨q, hq, hu, hhalf, ?_⟩
  intro g hg
  exact ⟨(hcomp g hg).1, (hcomp g hg).2,
    ico_normalized_fold_bound s t q g (by linarith) (hcomp g hg).2⟩

end Phinopert

#print axioms Phinopert.mem_icoSelectionGroup
#print axioms Phinopert.icoSelectionGroup_unit
#print axioms Phinopert.icoSelectionGroup_neg_closed
#print axioms Phinopert.icoSelectionGroup_coordinate_units
#print axioms Phinopert.icoSelectionGroup_product_closed_of_table
#print axioms Phinopert.ico_quaternion_selection_of_table
#print axioms Phinopert.icoViewHalfturn_unit
#print axioms Phinopert.icoViewHalfturn_square
#print axioms Phinopert.ico_view_selection_of_table
#print axioms Phinopert.ico_normalized_fold_identity
#print axioms Phinopert.ico_normalized_fold_bound
#print axioms Phinopert.ico_view_selection_folds_of_table
