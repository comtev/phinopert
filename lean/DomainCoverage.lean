import DomainComparisons
import IcosahedralSelection
import IcosahedralWalls

/-! The actual ordered 73 domain inequalities, and rotation representative
selection for a view already in the cone. Physical change-of-view equivalence
and arbitrary SO(3)-to-quaternion surjectivity are NOT asserted here. -/
namespace Phinopert

noncomputable def foldValue (s t : ℝ) (r : Point) (g : QuaternionCoords) : ℝ :=
  (-g.1*dot (s,t,1) r-dot g.2 ((s,t,1)+cross3 (s,t,1) r))^2-(1+s^2+t^2)

/-- Ordering: one cone form, twelve right-comparison forms, sixty folds in the
pinned model's quaternion order. Every boundary is retained by using ≤ 0. -/
noncomputable def domainValues (s t : ℝ) (r : Point) : List ℝ :=
  [phi*s+phi^2*t-1] ++ (comparisonForms phi r ++
    icoRaw.map (fun g => foldValue s t r (iqEval (Real.sqrt 5) g)))

theorem domainValues_length (s t : ℝ) (r : Point) : (domainValues s t r).length=73 := by
  simp only [domainValues,List.length_append,List.length_singleton,
    comparisonForms_length,List.length_map,ico_raw_length]

def InIcoDomain (s t : ℝ) (r : Point) : Prop :=
  0 ≤ s ∧ s ≤ 2/3 ∧ 0 ≤ t ∧ t ≤ 2/5 ∧
  (-2/5 ≤ r.1 ∧ r.1 ≤ 2/5) ∧ (-2/5 ≤ r.2.1 ∧ r.2.1 ≤ 2/5) ∧
  (-2/5 ≤ r.2.2 ∧ r.2.2 ≤ 2/5) ∧ ∀ f ∈ domainValues s t r, f ≤ 0

theorem selected_rotation_in_domain_of_table
    (htable : ∀ i : Fin 60, IcoClosureRow i.val)
    (p : QuaternionCoords) (hp : qNormSq p=1) (s t : ℝ)
    (hs : 0 ≤ s) (ht : 0 ≤ t) (hcone : phi*s+phi^2*t ≤ 1) :
    ∃ q ∈ quaternionCandidates icoSelectionGroup p (icoViewHalfturn s t),
      qNormSq q=1 ∧ 1/2 ≤ q.1 ∧ InIcoDomain s t (icoSelectedVector q) ∧
      (∀ x : Point, qAction q x = cayley (icoSelectedVector q) x) := by
  obtain ⟨q,hq,hunit,hhalf,hcomp⟩ := ico_view_selection_folds_of_table htable p hp s t
  have hpos : 0 < q.1 := by linarith
  have he : q=q.1 • (1,icoSelectedVector q) := normalise_nonzero_scalar q (ne_of_gt hpos)
  have hmax : ∀ g ∈ icoReal (Real.sqrt 5), (qProduct q g).1 ≤ q.1 := by
    intro g hg
    exact (hcomp g ((mem_icoSelectionGroup g).mpr hg)).1.2
  have hforms := comparisonForms_nonpos_of_scalar_max q q.1 (icoSelectedVector q) hpos he hmax
  obtain ⟨hrx,hry,hrz⟩ := comparisonForms_coordinate_bounds _ hforms
  have hview := view_cone_box _ s t sqrt5_spec.1 sqrt5_spec.2 hs ht hcone
  have hvalues : ∀ f ∈ domainValues s t (icoSelectedVector q), f ≤ 0 := by
    intro f hf
    rcases List.mem_append.mp hf with hf | hf
    · have heq : f=phi*s+phi^2*t-1 := List.mem_singleton.mp hf
      rw [heq]
      linarith
    · rcases List.mem_append.mp hf with hf | hf
      · exact hforms f hf
      · obtain ⟨g,hg,rfl⟩ := List.mem_map.mp hf
        have hg' := (mem_icoSelectionGroup _).mpr (icoReal_mem_of_raw (Real.sqrt 5) hg)
        have hb := (hcomp _ hg').2.2
        dsimp [foldValue]
        linarith
  refine ⟨q,hq,hunit,hhalf,⟨hs,hview.1,ht,hview.2,hrx,hry,hrz,hvalues⟩,?_⟩
  intro x
  have hn : qNormSq (q.1 • (1,icoSelectedVector q))=1 := by rw [← he]; exact hunit
  calc
    qAction q x = qAction (q.1 • (1,icoSelectedVector q)) x := by rw [← he]
    _ = cayley (icoSelectedVector q) x := quaternion_action_eq_cayley _ _ _ hn

end Phinopert
#print axioms Phinopert.domainValues_length
#print axioms Phinopert.selected_rotation_in_domain_of_table
