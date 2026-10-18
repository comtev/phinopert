import QuaternionAlgebra

/-!
Generic finite quaternion representative selection. The hypotheses concern
membership and algebra of the supplied list G, not the inequalities to be proved.
No actual symmetry group, vertex invariance, or physical coverage is asserted.
-/
namespace Phinopert

theorem qProduct_smul_left (a : ℝ) (p q : QuaternionCoords) :
    qProduct (a • p) q = a • qProduct p q := by
  ext <;> simp only [qProduct, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;> ring

theorem qProduct_smul_right (a : ℝ) (p q : QuaternionCoords) :
    qProduct p (a • q) = a • qProduct p q := by
  ext <;> simp only [qProduct, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;> ring

/-- The two candidate families, retaining both signs supplied by G. -/
noncomputable def quaternionCandidates (G : List QuaternionCoords)
    (p j : QuaternionCoords) : Finset QuaternionCoords := by
  classical
  exact ((G.map (qProduct p)) ++ (G.map (fun g => qProduct (qProduct j p) g))).toFinset

theorem mem_quaternionCandidates (G : List QuaternionCoords) (p j q : QuaternionCoords) :
    q ∈ quaternionCandidates G p j ↔
      (∃ g ∈ G, qProduct p g = q) ∨
      (∃ g ∈ G, qProduct (qProduct j p) g = q) := by
  classical
  simp [quaternionCandidates]

theorem quaternionCandidates_nonempty (G : List QuaternionCoords) (p j : QuaternionCoords)
    (hone : (1, (0 : Point)) ∈ G) : (quaternionCandidates G p j).Nonempty := by
  refine ⟨p, (mem_quaternionCandidates G p j p).mpr (Or.inl ?_)⟩
  exact ⟨(1, 0), hone, qProduct_one_right p⟩

theorem quaternionCandidates_right_closed (G : List QuaternionCoords) (p j : QuaternionCoords)
    (hclosed : ∀ g ∈ G, ∀ h ∈ G, qProduct g h ∈ G)
    {q g : QuaternionCoords} (hq : q ∈ quaternionCandidates G p j) (hg : g ∈ G) :
    qProduct q g ∈ quaternionCandidates G p j := by
  rcases (mem_quaternionCandidates G p j q).mp hq with ⟨h, hh, rfl⟩ | ⟨h, hh, rfl⟩
  · apply (mem_quaternionCandidates G p j _).mpr
    exact Or.inl ⟨qProduct h g, hclosed h hh g hg, (qProduct_assoc p h g).symm⟩
  · apply (mem_quaternionCandidates G p j _).mpr
    exact Or.inr ⟨qProduct h g, hclosed h hh g hg,
      (qProduct_assoc (qProduct j p) h g).symm⟩

theorem quaternionCandidates_neg_closed (G : List QuaternionCoords) (p j : QuaternionCoords)
    (hneg : ∀ g ∈ G, -g ∈ G)
    {q : QuaternionCoords} (hq : q ∈ quaternionCandidates G p j) :
    -q ∈ quaternionCandidates G p j := by
  rcases (mem_quaternionCandidates G p j q).mp hq with ⟨g, hg, rfl⟩ | ⟨g, hg, rfl⟩
  · exact (mem_quaternionCandidates G p j _).mpr
      (Or.inl ⟨-g, hneg g hg, qProduct_neg_right p g⟩)
  · exact (mem_quaternionCandidates G p j _).mpr
      (Or.inr ⟨-g, hneg g hg, qProduct_neg_right (qProduct j p) g⟩)

theorem quaternionCandidates_left_j_closed (G : List QuaternionCoords) (p j : QuaternionCoords)
    (hneg : ∀ g ∈ G, -g ∈ G) (hjj : qProduct j j = (-1, (0 : Point)))
    {q : QuaternionCoords} (hq : q ∈ quaternionCandidates G p j) :
    qProduct j q ∈ quaternionCandidates G p j := by
  rcases (mem_quaternionCandidates G p j q).mp hq with ⟨g, hg, rfl⟩ | ⟨g, hg, rfl⟩
  · exact (mem_quaternionCandidates G p j _).mpr
      (Or.inr ⟨g, hg, qProduct_assoc j p g⟩)
  · apply (mem_quaternionCandidates G p j _).mpr
    refine Or.inl ⟨-g, hneg g hg, ?_⟩
    have hm : qProduct (-1, (0 : Point)) p = -p := by
      have he : ((-1, (0 : Point)) : QuaternionCoords) = -(1, (0 : Point)) := by simp
      rw [he, qProduct_neg_left, qProduct_one_left]
    rw [← qProduct_assoc j (qProduct j p) g, ← qProduct_assoc j j p, hjj, hm,
      qProduct_neg_left, qProduct_neg_right]

theorem quaternionCandidates_unit (G : List QuaternionCoords) (p j : QuaternionCoords)
    (hG : ∀ g ∈ G, qNormSq g = 1) (hp : qNormSq p = 1) (hj : qNormSq j = 1)
    {q : QuaternionCoords} (hq : q ∈ quaternionCandidates G p j) : qNormSq q = 1 := by
  rcases (mem_quaternionCandidates G p j q).mp hq with ⟨g, hg, rfl⟩ | ⟨g, hg, rfl⟩
  · exact qProduct_unit p g hp (hG g hg)
  · exact qProduct_unit (qProduct j p) g (qProduct_unit j p hj hp) (hG g hg)

/-- Positive coordinate units; their negatives follow from sign closure. -/
def quaternionCoordinateUnits : List QuaternionCoords :=
  [(1, (0 : Point)), (0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1)]

/-- Actual right multipliers in G realize each signed scalar competitor. -/
theorem quaternion_signed_coordinate_multipliers (G : List QuaternionCoords)
    (hneg : ∀ g ∈ G, -g ∈ G)
    (hcoords : ∀ e ∈ quaternionCoordinateUnits, e ∈ G) (q : QuaternionCoords)
    (c : ℝ) (hc : c ∈ ([q.1, q.2.1, q.2.2.1, q.2.2.2] : List ℝ)) :
    (∃ g ∈ G, (qProduct q g).1 = c) ∧ (∃ g ∈ G, (qProduct q g).1 = -c) := by
  have flip : ∀ c : ℝ, (∃ g ∈ G, (qProduct q g).1 = c) →
      (∃ g ∈ G, (qProduct q g).1 = c) ∧ (∃ g ∈ G, (qProduct q g).1 = -c) := by
    intro c he
    refine ⟨he, ?_⟩
    obtain ⟨g, hg, heq⟩ := he
    refine ⟨-g, hneg g hg, ?_⟩
    rw [qProduct_neg_right]
    change -(qProduct q g).1 = -c
    rw [heq]
  apply flip
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · exact ⟨(1, 0), hcoords _ (by simp [quaternionCoordinateUnits]),
      congrArg Prod.fst (qProduct_one_right q)⟩
  · refine ⟨-((0, 1, 0, 0) : QuaternionCoords),
      hneg _ (hcoords _ (by simp [quaternionCoordinateUnits])), ?_⟩
    simp [qProduct]
  · refine ⟨-((0, 0, 1, 0) : QuaternionCoords),
      hneg _ (hcoords _ (by simp [quaternionCoordinateUnits])), ?_⟩
    simp [qProduct]
  · refine ⟨-((0, 0, 0, 1) : QuaternionCoords),
      hneg _ (hcoords _ (by simp [quaternionCoordinateUnits])), ?_⟩
    simp [qProduct]

theorem quaternionCandidates_coordinate_competitors (G : List QuaternionCoords)
    (p j : QuaternionCoords)
    (hclosed : ∀ g ∈ G, ∀ h ∈ G, qProduct g h ∈ G)
    (hneg : ∀ g ∈ G, -g ∈ G)
    (hcoords : ∀ e ∈ quaternionCoordinateUnits, e ∈ G)
    {q : QuaternionCoords} (hq : q ∈ quaternionCandidates G p j)
    (c : ℝ) (hc : c ∈ ([q.1, q.2.1, q.2.2.1, q.2.2.2] : List ℝ)) :
    (∃ v ∈ quaternionCandidates G p j, v.1 = c) ∧
    (∃ v ∈ quaternionCandidates G p j, v.1 = -c) := by
  obtain ⟨⟨g, hg, he⟩, ⟨h, hh, he'⟩⟩ :=
    quaternion_signed_coordinate_multipliers G hneg hcoords q c hc
  exact ⟨⟨qProduct q g, quaternionCandidates_right_closed G p j hclosed hq hg, he⟩,
    ⟨qProduct q h, quaternionCandidates_right_closed G p j hclosed hq hh, he'⟩⟩

/-- One maximizer gives BOTH comparison families, with a strictly positive
scalar even when the original quaternion p has scalar zero. The group and
coordinate hypotheses are finite membership facts, not assumed inequalities. -/
theorem finite_quaternion_candidate_selection (G : List QuaternionCoords)
    (p j : QuaternionCoords)
    (hclosed : ∀ g ∈ G, ∀ h ∈ G, qProduct g h ∈ G)
    (hneg : ∀ g ∈ G, -g ∈ G)
    (hcoords : ∀ e ∈ quaternionCoordinateUnits, e ∈ G)
    (hG : ∀ g ∈ G, qNormSq g = 1)
    (hp : qNormSq p = 1) (hj : qNormSq j = 1)
    (hjj : qProduct j j = (-1, (0 : Point))) :
    ∃ q ∈ quaternionCandidates G p j,
      qNormSq q = 1 ∧ 1/2 ≤ q.1 ∧
      (∀ v ∈ quaternionCandidates G p j, v.1 ≤ q.1) ∧
      (∀ g ∈ G, (qProduct q g).1 ≤ q.1 ∧
        (qProduct (qProduct j q) g).1 ≤ q.1) := by
  have hne := quaternionCandidates_nonempty G p j
    (hcoords _ (by simp [quaternionCoordinateUnits]))
  have hu : ∀ q ∈ quaternionCandidates G p j,
      q.1*q.1 + q.2.1*q.2.1 + q.2.2.1*q.2.2.1 + q.2.2.2*q.2.2.2 = 1 := by
    intro q hq
    simpa only [qNormSq, pow_two] using quaternionCandidates_unit G p j hG hp hj hq
  obtain ⟨q, hq, hhalf, hmax⟩ := finite_quaternion_representative
    (quaternionCandidates G p j) hne hu
    (fun q hq c hc => quaternionCandidates_coordinate_competitors G p j
      hclosed hneg hcoords hq c hc)
  refine ⟨q, hq, quaternionCandidates_unit G p j hG hp hj hq, hhalf, hmax, ?_⟩
  intro g hg
  exact ⟨hmax _ (quaternionCandidates_right_closed G p j hclosed hq hg),
    hmax _ (quaternionCandidates_right_closed G p j hclosed
      (quaternionCandidates_left_j_closed G p j hneg hjj hq) hg)⟩

/-- Maximality and the two closure operations imply all signed scalar
comparisons. Unit norm is not needed for this step. In particular, the lower
bounds are derived from the actual multipliers -g in G, not assumed. -/
theorem selected_quaternion_scalar_comparisons
    (S : Finset QuaternionCoords) (G : List QuaternionCoords) (q j : QuaternionCoords)
    (hq : q ∈ S) (hmax : ∀ v ∈ S, v.1 ≤ q.1)
    (hright : ∀ v ∈ S, ∀ g ∈ G, qProduct v g ∈ S)
    (hleft : ∀ v ∈ S, qProduct j v ∈ S)
    (hneg : ∀ g ∈ G, -g ∈ G) :
    ∀ g ∈ G,
      (-q.1 ≤ (qProduct q g).1 ∧ (qProduct q g).1 ≤ q.1) ∧
      (-q.1 ≤ (qProduct (qProduct j q) g).1 ∧
        (qProduct (qProduct j q) g).1 ≤ q.1) := by
  have bounds : ∀ v ∈ S, ∀ g ∈ G,
      -q.1 ≤ (qProduct v g).1 ∧ (qProduct v g).1 ≤ q.1 := by
    intro v hv g hg
    have hplus := hmax _ (hright v hv g hg)
    have hminus := hmax _ (hright v hv (-g) (hneg g hg))
    rw [qProduct_neg_right] at hminus
    change -(qProduct v g).1 ≤ q.1 at hminus
    exact ⟨by linarith, hplus⟩
  intro g hg
  exact ⟨bounds q hq g hg, bounds (qProduct j q) (hleft q hq) g hg⟩

/-- Complete signed selection interface for subsequent domain formulas.
The same selected unit quaternion satisfies both two-sided comparison families;
only finite group memberships, unit identities and j*j=-1 are hypotheses. -/
theorem finite_quaternion_candidate_selection_signed (G : List QuaternionCoords)
    (p j : QuaternionCoords)
    (hclosed : ∀ g ∈ G, ∀ h ∈ G, qProduct g h ∈ G)
    (hneg : ∀ g ∈ G, -g ∈ G)
    (hcoords : ∀ e ∈ quaternionCoordinateUnits, e ∈ G)
    (hG : ∀ g ∈ G, qNormSq g = 1)
    (hp : qNormSq p = 1) (hj : qNormSq j = 1)
    (hjj : qProduct j j = (-1, (0 : Point))) :
    ∃ q ∈ quaternionCandidates G p j,
      qNormSq q = 1 ∧ 1/2 ≤ q.1 ∧
      (∀ v ∈ quaternionCandidates G p j, v.1 ≤ q.1) ∧
      (∀ g ∈ G,
        (-q.1 ≤ (qProduct q g).1 ∧ (qProduct q g).1 ≤ q.1) ∧
        (-q.1 ≤ (qProduct (qProduct j q) g).1 ∧
          (qProduct (qProduct j q) g).1 ≤ q.1)) := by
  obtain ⟨q, hq, hunit, hhalf, hmax, _⟩ :=
    finite_quaternion_candidate_selection G p j hclosed hneg hcoords hG hp hj hjj
  refine ⟨q, hq, hunit, hhalf, hmax, ?_⟩
  exact selected_quaternion_scalar_comparisons (quaternionCandidates G p j) G q j hq hmax
    (fun v hv g hg => quaternionCandidates_right_closed G p j hclosed hv hg)
    (fun v hv => quaternionCandidates_left_j_closed G p j hneg hjj hv) hneg

end Phinopert

#print axioms Phinopert.mem_quaternionCandidates
#print axioms Phinopert.quaternionCandidates_nonempty
#print axioms Phinopert.quaternionCandidates_right_closed
#print axioms Phinopert.quaternionCandidates_neg_closed
#print axioms Phinopert.quaternionCandidates_left_j_closed
#print axioms Phinopert.quaternionCandidates_unit
#print axioms Phinopert.quaternion_signed_coordinate_multipliers
#print axioms Phinopert.quaternionCandidates_coordinate_competitors
#print axioms Phinopert.finite_quaternion_candidate_selection
#print axioms Phinopert.selected_quaternion_scalar_comparisons
#print axioms Phinopert.finite_quaternion_candidate_selection_signed
#print axioms Phinopert.qProduct_smul_left
#print axioms Phinopert.qProduct_smul_right
