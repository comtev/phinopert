import IcosahedralReal
import IcosahedralVertexData

/-!
The integer vertex-action certificates imply invariance of the actual real
vertex set and its convex hull. Quaternion coordinates have denominator four;
vertex coordinates have denominator 800, and the action certificates have the
additional factor sixteen. Both quaternion signs induce the same action.

The final theorems concern every member of `icoReal (Real.sqrt 5)`, not every
rotation of three-dimensional space. They take the finite vertex-check table
explicitly and use the exact representative export. Unconditional wrappers
belong in the module that imports the completed row checks.
-/
namespace Phinopert

-- BEGIN GENERIC: independently checkable with Arithmetic + QuaternionAlgebra.

/-- Real evaluation of an integer vertex, including its denominator 800. -/
noncomputable def ipEval (s : ℝ) (p : IP) : Point :=
  (ieval s p.1 / 800, ieval s p.2.1 / 800, ieval s p.2.2 / 800)

theorem ipEval_scale (s : ℝ) (k : ℤ) (p : IP) :
    ipEval s (ipScale k p) = (k : ℝ) • ipEval s p := by
  apply Prod.ext
  · simp only [ipEval, ipScale, ieval_scale, Prod.smul_def, smul_eq_mul]
    ring
  · apply Prod.ext <;>
      simp only [ipEval, ipScale, ieval_scale, Prod.smul_def,
        smul_eq_mul] <;> ring

/-- The generic evaluator bridge, stated without the finite-data module. -/
theorem qAction_ieval (s : ℝ) (hs : s*s = 5) (q : IQ) (p : IP) :
    qAction (ieval s q.1 / 4, ieval s q.2.1 / 4,
      ieval s q.2.2.1 / 4, ieval s q.2.2.2 / 4) (ipEval s p) =
      (1 / 16 : ℝ) • ipEval s (iqAction q p) := by
  apply Prod.ext
  · simp only [qAction, ipEval, iqAction, ieval_add, ieval_sub,
      ieval_scale, ieval_mul s hs, Prod.smul_def, smul_eq_mul, Int.cast_ofNat]
    ring
  · apply Prod.ext <;>
      simp only [qAction, ipEval, iqAction, ieval_add, ieval_sub,
        ieval_scale, ieval_mul s hs, Prod.smul_def,
        smul_eq_mul, Int.cast_ofNat] <;> ring

/-- Rational export and integer evaluation use exactly the same denominator. -/
theorem ipEval_rational (s : ℝ) (p : IP) :
    evalPoint s
      (((p.1.1 : ℚ)/800, (p.1.2 : ℚ)/800),
       ((p.2.1.1 : ℚ)/800, (p.2.1.2 : ℚ)/800),
       ((p.2.2.1 : ℚ)/800, (p.2.2.2 : ℚ)/800)) = ipEval s p := by
  ext <;> simp [evalPoint, eval, ipEval, ieval] <;> ring

/-- The homogeneous quaternion action is linear even without unit norm. -/
noncomputable def qActionLinear (q : QuaternionCoords) : Point →ₗ[ℝ] Point where
  toFun := qAction q
  map_add' u v := by ext <;> simp [qAction] <;> ring
  map_smul' a u := by ext <;> simp [qAction] <;> ring

theorem qAction_point_neg (q : QuaternionCoords) (p : Point) :
    qAction q (-p) = -qAction q p :=
  (qActionLinear q).map_neg p

theorem qAction_injective_of_unit (q : QuaternionCoords) (hq : qNormSq q = 1) :
    Function.Injective (qAction q) := by
  intro u v huv
  by_contra hne
  have hpos := dot_self_positive (u - v) (sub_ne_zero.mpr hne)
  have hz : qAction q (u - v) = 0 := by
    change qActionLinear q (u - v) = 0
    rw [map_sub]
    exact sub_eq_zero.mpr huv
  have hd := qAction_dot_of_unit q hq (u - v) (u - v)
  rw [hz] at hd
  have hzero : dot (0 : Point) 0 = 0 := by norm_num [dot]
  rw [hzero] at hd
  linarith

theorem vertexSet_finite (s : ℝ) : (VertexSet s).Finite := by
  classical
  have he : VertexSet s = evalPoint s '' (↑vertices.toFinset : Set RawPoint) := by
    ext p
    simp [VertexSet]
  rw [he]
  exact vertices.toFinset.finite_toSet.image (evalPoint s)

/-- On a finite set, an injective action mapping into the set maps onto it. -/
theorem qAction_image_eq_of_finite (q : QuaternionCoords) (hq : qNormSq q = 1)
    (V : Set Point) (hV : V.Finite) (hm : Set.MapsTo (qAction q) V V) :
    qAction q '' V = V :=
  ((hV.injOn_iff_bijOn_of_mapsTo hm).mp
    (qAction_injective_of_unit q hq).injOn).image_eq

theorem qAction_convexHull_image (q : QuaternionCoords) (V : Set Point)
    (hV : qAction q '' V = V) :
    qAction q '' convexHull ℝ V = convexHull ℝ V := by
  change qActionLinear q '' convexHull ℝ V = convexHull ℝ V
  rw [(qActionLinear q).image_convexHull]
  change convexHull ℝ (qAction q '' V) = convexHull ℝ V
  rw [hV]

#print axioms Phinopert.ipEval_scale
#print axioms Phinopert.qAction_ieval
#print axioms Phinopert.ipEval_rational
#print axioms Phinopert.qAction_point_neg
#print axioms Phinopert.qAction_injective_of_unit
#print axioms Phinopert.vertexSet_finite
#print axioms Phinopert.qAction_image_eq_of_finite
#print axioms Phinopert.qAction_convexHull_image

-- END GENERIC

theorem evalPoint_icoRawPoint (s : ℝ) (p : IP) :
    evalPoint s (icoRawPoint p) = ipEval s p :=
  ipEval_rational s p

theorem iqEval_action (s : ℝ) (hs : s*s = 5) (q : IQ) (p : IP) :
    qAction (iqEval s q) (ipEval s p) =
      (1 / 16 : ℝ) • ipEval s (iqAction q p) :=
  qAction_ieval s hs q p

/-- Cancel the certificate's factor sixteen, retaining its vertex sign. -/
theorem iqEval_action_of_witness (s : ℝ) (hs : s*s = 5)
    (q : IQ) (p r : IP) (k : ℤ) (h : iqAction q p = ipScale (16*k) r) :
    qAction (iqEval s q) (ipEval s p) = (k : ℝ) • ipEval s r := by
  rw [iqEval_action s hs, h, ipEval_scale]
  ext <;> simp <;> ring

theorem icoVertexAt_mem_raw (j : Fin 90) : icoVertexAt j.val ∈ icoVertexRaw := by
  have hj : j.val < icoVertexRaw.length := by
    simpa only [ico_vertex_length] using j.isLt
  simp only [icoVertexAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj,
    Option.getD_some]
  exact List.getElem_mem hj

theorem icoVertexRaw_mem_index {p : IP} (hp : p ∈ icoVertexRaw) :
    ∃ j : Fin 90, icoVertexAt j.val = p := by
  obtain ⟨j, hj, he⟩ := List.mem_iff_getElem.mp hp
  refine ⟨⟨j, by simpa only [ico_vertex_length] using hj⟩, ?_⟩
  simpa only [icoVertexAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj,
    Option.getD_some] using he

theorem ipEval_mem_vertexSet (s : ℝ) {p : IP} (hp : p ∈ icoVertexRaw) :
    ipEval s p ∈ VertexSet s := by
  have hr : icoRawPoint p ∈ representatives := by
    rw [← ico_vertex_export_exact]
    exact List.mem_map.mpr ⟨p, hp, rfl⟩
  exact ⟨icoRawPoint p, List.mem_append_left _ hr, evalPoint_icoRawPoint s p⟩

/-- The exact export accounts for both signs of every real vertex. -/
theorem mem_vertexSet_iff_icoVertexRaw (s : ℝ) (x : Point) :
    x ∈ VertexSet s ↔ ∃ p ∈ icoVertexRaw, x = ipEval s p ∨ x = -ipEval s p := by
  constructor
  · rintro ⟨r, hr, rfl⟩
    change r ∈ representatives ++ representatives.map rawNeg at hr
    rcases List.mem_append.mp hr with hrep | hneg
    · rw [← ico_vertex_export_exact] at hrep
      obtain ⟨p, hp, he⟩ := List.mem_map.mp hrep
      refine ⟨p, hp, Or.inl ?_⟩
      rw [← he, evalPoint_icoRawPoint]
    · obtain ⟨r', hr', he⟩ := List.mem_map.mp hneg
      rw [← ico_vertex_export_exact] at hr'
      obtain ⟨p, hp, he'⟩ := List.mem_map.mp hr'
      refine ⟨p, hp, Or.inr ?_⟩
      rw [← he, ← he', eval_rawNeg, evalPoint_icoRawPoint] <;> rfl
  · rintro ⟨p, hp, rfl | rfl⟩
    · exact ipEval_mem_vertexSet s hp
    · exact vertex_set_centrally_symmetric s (ipEval_mem_vertexSet s hp)

theorem icoAt_action_vertex_mem_of_checks (s : ℝ) (hs : s*s = 5)
    (hchecks : ∀ i : Fin 60, IcoVertexRow i.val)
    (i : Fin 60) (j : Fin 90) :
    qAction (iqEval s (icoAt i.val)) (ipEval s (icoVertexAt j.val)) ∈ VertexSet s := by
  obtain ⟨ha, ht, hk⟩ := hchecks i j
  have he := iqEval_action_of_witness s hs _ _ _ _ ha
  have hm := ipEval_mem_vertexSet s
    (icoVertexAt_mem_raw ⟨(icoVertexWitness i.val j.val).1, ht⟩)
  rcases hk with hk | hk
  · simp only [hk, Int.cast_one, one_smul] at he
    rw [he]
    exact hm
  · simp only [hk, Int.cast_neg, Int.cast_one, neg_one_smul] at he
    rw [he]
    exact vertex_set_centrally_symmetric s hm

/-- Every evaluated signed quaternion sends every signed vertex to a vertex. -/
theorem icoReal_mapsTo_vertexSet_of_checks (s : ℝ) (hs : s*s = 5)
    (hchecks : ∀ i : Fin 60, IcoVertexRow i.val)
    {q : QuaternionCoords} (hq : q ∈ icoReal s) :
    Set.MapsTo (qAction q) (VertexSet s) (VertexSet s) := by
  have hbase : ∀ a ∈ icoRaw, ∀ x ∈ VertexSet s,
      qAction (iqEval s a) x ∈ VertexSet s := by
    intro a ha x hx
    obtain ⟨i, rfl⟩ := icoRaw_mem_index ha
    obtain ⟨p, hp, rfl | rfl⟩ := (mem_vertexSet_iff_icoVertexRaw s x).mp hx
    · obtain ⟨j, rfl⟩ := icoVertexRaw_mem_index hp
      exact icoAt_action_vertex_mem_of_checks s hs hchecks i j
    · obtain ⟨j, rfl⟩ := icoVertexRaw_mem_index hp
      rw [qAction_point_neg]
      exact vertex_set_centrally_symmetric s
        (icoAt_action_vertex_mem_of_checks s hs hchecks i j)
  obtain ⟨a, ha, rfl | rfl⟩ := (mem_icoReal_iff_base s q).mp hq
  · exact hbase a ha
  · intro x hx
    rw [qAction_neg]
    exact hbase a ha x hx

theorem icoReal_vertexSet_image_of_checks (s : ℝ) (hs : s*s = 5)
    (hchecks : ∀ i : Fin 60, IcoVertexRow i.val)
    {q : QuaternionCoords} (hq : q ∈ icoReal s) :
    qAction q '' VertexSet s = VertexSet s :=
  qAction_image_eq_of_finite q (icoReal_unit s hs hq) _ (vertexSet_finite s)
    (icoReal_mapsTo_vertexSet_of_checks s hs hchecks hq)

theorem icoReal_vertexSet_sqrt5_image_of_checks
    (hchecks : ∀ i : Fin 60, IcoVertexRow i.val) {q : QuaternionCoords}
    (hq : q ∈ icoReal (Real.sqrt 5)) :
    qAction q '' VertexSet (Real.sqrt 5) = VertexSet (Real.sqrt 5) :=
  icoReal_vertexSet_image_of_checks _ sqrt5_spec.1 hchecks hq

/-- Equality of the entire convex hull under every listed rotation. -/
theorem icoReal_solid_image_of_checks
    (hchecks : ∀ i : Fin 60, IcoVertexRow i.val) {q : QuaternionCoords}
    (hq : q ∈ icoReal (Real.sqrt 5)) : qAction q '' solid = solid :=
  qAction_convexHull_image q _ (icoReal_vertexSet_sqrt5_image_of_checks hchecks hq)

theorem icoReal_solid_mem_iff_of_checks
    (hchecks : ∀ i : Fin 60, IcoVertexRow i.val) {q : QuaternionCoords}
    (hq : q ∈ icoReal (Real.sqrt 5)) (p : Point) :
    qAction q p ∈ solid ↔ p ∈ solid := by
  constructor
  · intro hp
    rw [← icoReal_solid_image_of_checks hchecks hq] at hp
    obtain ⟨v, hv, he⟩ := hp
    have hvp := qAction_injective_of_unit q (icoReal_unit _ sqrt5_spec.1 hq) he
    rwa [hvp] at hv
  · intro hp
    rw [← icoReal_solid_image_of_checks hchecks hq]
    exact Set.mem_image_of_mem _ hp

end Phinopert

#print axioms Phinopert.evalPoint_icoRawPoint
#print axioms Phinopert.iqEval_action
#print axioms Phinopert.iqEval_action_of_witness
#print axioms Phinopert.icoVertexAt_mem_raw
#print axioms Phinopert.icoVertexRaw_mem_index
#print axioms Phinopert.ipEval_mem_vertexSet
#print axioms Phinopert.mem_vertexSet_iff_icoVertexRaw
#print axioms Phinopert.icoAt_action_vertex_mem_of_checks
#print axioms Phinopert.icoReal_mapsTo_vertexSet_of_checks
#print axioms Phinopert.icoReal_vertexSet_image_of_checks
#print axioms Phinopert.icoReal_vertexSet_sqrt5_image_of_checks
#print axioms Phinopert.icoReal_solid_image_of_checks
#print axioms Phinopert.icoReal_solid_mem_iff_of_checks
