import TwoBodyCoverage

/-! A coordinate definition of proper orthogonal linear maps, independent of
quaternions. The product topology/norm is not used to define orthogonality. -/
namespace Phinopert

def axisX : Point := (1,0,0)
def axisY : Point := (0,1,0)
def axisZ : Point := (0,0,1)

def IsProperRotation (R : Point →ₗ[ℝ] Point) : Prop :=
  (∀ u v, dot (R u) (R v) = dot u v) ∧ det (R axisX) (R axisY) (R axisZ) = 1

theorem qNormSq_smul (a : ℝ) (q : QuaternionCoords) :
    qNormSq (a • q) = a^2 * qNormSq q := by
  simp only [qNormSq, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

theorem normalising_scalar (D : ℝ) (hD : 0 < D) :
    (1 / Real.sqrt D)^2 * D = 1 := by
  have hs : (Real.sqrt D)^2 = D := Real.sq_sqrt (le_of_lt hD)
  rw [div_pow, one_pow, hs, div_mul_cancel₀ _ (ne_of_gt hD)]

theorem normalised_quaternion_unit (q : QuaternionCoords) (hq : 0 < qNormSq q) :
    qNormSq ((1 / Real.sqrt (qNormSq q)) • q) = 1 := by
  rw [qNormSq_smul]
  exact normalising_scalar _ hq

theorem normalised_quaternion_action (q : QuaternionCoords) (hq : 0 < qNormSq q)
    (p v : Point) (hv : qAction q p = qNormSq q • v) :
    qAction ((1 / Real.sqrt (qNormSq q)) • q) p = v := by
  rw [qAction_scale, hv, smul_smul]
  have hs := normalising_scalar _ hq
  rw [← sq, hs, one_smul]

theorem unit_first_coordinate (v : Point) (hv : dot v v = 1) : -1 ≤ v.1 := by
  dsimp [dot] at hv
  nlinarith [sq_nonneg v.2.1, sq_nonneg v.2.2, sq_nonneg (v.1+1)]

/-- Every unit vector is the image of the first axis, including its antipode. -/
theorem quaternion_maps_first_axis (v : Point) (hv : dot v v = 1) :
    ∃ q : QuaternionCoords, qNormSq q = 1 ∧ qAction q axisX = v := by
  by_cases hx : v.1 = -1
  · have hy : v.2.1 = 0 := by
      dsimp [dot] at hv
      rw [hx] at hv
      nlinarith [sq_nonneg v.2.2]
    have hz : v.2.2 = 0 := by
      dsimp [dot] at hv
      rw [hx,hy] at hv
      nlinarith
    refine ⟨(0,0,1,0),by norm_num [qNormSq],?_⟩
    ext <;> simp [qAction,axisX,hx,hy,hz]
  · let q : QuaternionCoords := (1+v.1,0,-v.2.2,v.2.1)
    have hn : qNormSq q = 2*(1+v.1) := by
      dsimp [qNormSq,q,dot] at *
      nlinarith
    have hp : 0 < qNormSq q := by
      rw [hn]
      have := unit_first_coordinate v hv
      have : -1 < v.1 := lt_of_le_of_ne this (Ne.symm hx)
      linarith
    refine ⟨(1 / Real.sqrt (qNormSq q)) • q, normalised_quaternion_unit q hp, ?_⟩
    apply normalised_quaternion_action q hp
    rw [hn]
    ext <;> dsimp [qAction,q,axisX] <;> dsimp [dot] at hv <;> nlinarith

/-- Every unit vector in the yz-plane is reached by a rotation fixing x. -/
theorem quaternion_fixes_first_maps_second (v : Point) (hx : v.1 = 0)
    (hv : dot v v = 1) : ∃ q : QuaternionCoords,
      qNormSq q = 1 ∧ qAction q axisX = axisX ∧ qAction q axisY = v := by
  by_cases hy : v.2.1 = -1
  · have hz : v.2.2 = 0 := by
      dsimp [dot] at hv
      rw [hx,hy] at hv
      nlinarith
    refine ⟨(0,1,0,0),by norm_num [qNormSq],?_,?_⟩
    · ext <;> norm_num [qAction,axisX]
    · ext <;> simp [qAction,axisY,hx,hy,hz]
  · let q : QuaternionCoords := (1+v.2.1,v.2.2,0,0)
    have hn : qNormSq q = 2*(1+v.2.1) := by
      dsimp [qNormSq,q,dot] at *
      rw [hx] at hv
      nlinarith
    have hp : 0 < qNormSq q := by
      rw [hn]
      have hb : -1 ≤ v.2.1 := by
        dsimp [dot] at hv
        nlinarith [sq_nonneg v.1, sq_nonneg v.2.2, sq_nonneg (v.2.1+1)]
      have : -1 < v.2.1 := lt_of_le_of_ne hb (Ne.symm hy)
      linarith
    refine ⟨(1 / Real.sqrt (qNormSq q)) • q,normalised_quaternion_unit q hp,?_,?_⟩
    · apply normalised_quaternion_action q hp
      ext <;> simp [qAction,qNormSq,q,axisX] <;> ring
    · apply normalised_quaternion_action q hp
      rw [hn]
      ext <;> dsimp [qAction,q,axisY] <;> dsimp [dot] at hv <;> simp only [hx] at hv ⊢ <;> nlinarith

theorem dot_cross_self (a b : Point) :
    dot (cross3 a b) (cross3 a b) = dot a a * dot b b - (dot a b)^2 := by
  dsimp [dot,cross3]
  ring

theorem dot_cross_det (a b c : Point) : dot (cross3 a b) c = det a b c := by
  dsimp [dot,cross3,det]
  ring

theorem unit_dot_eq_one (a b : Point) (ha : dot a a = 1) (hb : dot b b = 1)
    (hab : dot a b = 1) : a = b := by
  have he : dot (a-b) (a-b) = 0 := by
    have hid : dot (a-b) (a-b) = dot a a + dot b b - 2*dot a b := by
      simp only [dot,Prod.fst_sub,Prod.snd_sub]
      ring
    rw [hid,ha,hb,hab]
    norm_num
  by_contra hn
  have := dot_self_positive (a-b) (sub_ne_zero.mpr hn)
  linarith

theorem oriented_frame_third (a b c : Point)
    (ha : dot a a = 1) (hb : dot b b = 1) (hc : dot c c = 1)
    (hab : dot a b = 0) (hd : det a b c = 1) : cross3 a b = c := by
  apply unit_dot_eq_one _ c _ hc
  · rw [dot_cross_det,hd]
  · rw [dot_cross_self,ha,hb,hab]
    norm_num

set_option maxHeartbeats 800000 in
theorem qAction_cross (q : QuaternionCoords) (a b : Point) :
    cross3 (qAction q a) (qAction q b) = qNormSq q • qAction q (cross3 a b) := by
  ext <;> dsimp [cross3,qAction,qNormSq] <;> ring

/-- Euler--Rodrigues surjectivity for the full, independently defined proper
orthogonal linear-map predicate. No favourable trace or chart assumption. -/
theorem proper_rotation_has_quaternion (R : Point →ₗ[ℝ] Point) (hR : IsProperRotation R) :
    ∃ q : QuaternionCoords, qNormSq q = 1 ∧ ∀ x, qAction q x = R x := by
  have ha : dot (R axisX) (R axisX) = 1 := by rw [hR.1]; norm_num [axisX,dot]
  have hb : dot (R axisY) (R axisY) = 1 := by rw [hR.1]; norm_num [axisY,dot]
  have hc : dot (R axisZ) (R axisZ) = 1 := by rw [hR.1]; norm_num [axisZ,dot]
  have hab : dot (R axisX) (R axisY) = 0 := by rw [hR.1]; norm_num [axisX,axisY,dot]
  obtain ⟨q,hq,hqa⟩ := quaternion_maps_first_axis _ ha
  let b := qAction (qConjugate q) (R axisY)
  have hqb : qAction q b = R axisY := qConjugate_action_right q hq _
  have hbx : b.1 = 0 := by
    have h := qAction_dot_of_unit q hq axisX b
    rw [hqa,hqb,hab] at h
    simpa [axisX,dot] using h.symm
  have hbn : dot b b = 1 := by
    have h := qAction_dot_of_unit q hq b b
    rw [hqb,hb] at h
    exact h.symm
  obtain ⟨p,hp,hpx,hpy⟩ := quaternion_fixes_first_maps_second b hbx hbn
  let c := qProduct q p
  have hcn : qNormSq c = 1 := qProduct_unit q p hq hp
  have hcx : qAction c axisX = R axisX := by
    change qAction (qProduct q p) axisX = _
    rw [qAction_product,hpx,hqa]
  have hcy : qAction c axisY = R axisY := by
    change qAction (qProduct q p) axisY = _
    rw [qAction_product,hpy,hqb]
  have hcz : qAction c axisZ = R axisZ := by
    have hcross : cross3 axisX axisY = axisZ := by norm_num [cross3,axisX,axisY,axisZ]
    have h := qAction_cross c axisX axisY
    rw [hcx,hcy,hcross,hcn,one_smul] at h
    rw [← h]
    exact oriented_frame_third _ _ _ ha hb hc hab hR.2
  refine ⟨c,hcn,?_⟩
  intro x
  have hx : x = x.1 • axisX + x.2.1 • axisY + x.2.2 • axisZ := by
    ext <;> simp [axisX,axisY,axisZ]
  conv_lhs => rw [hx]
  change qActionLinear c (x.1 • axisX + x.2.1 • axisY + x.2.2 • axisZ) = R x
  simp only [map_add,map_smul]
  change x.1 • qAction c axisX + x.2.1 • qAction c axisY + x.2.2 • qAction c axisZ = R x
  rw [hcx,hcy,hcz,← map_smul,← map_smul,← map_smul,← map_add,← map_add,← hx]

theorem unit_quaternion_is_proper (q : QuaternionCoords) (hq : qNormSq q = 1) :
    IsProperRotation (qActionLinear q) := by
  constructor
  · exact qAction_dot_of_unit q hq
  · change det (qAction q axisX) (qAction q axisY) (qAction q axisZ) = 1
    rw [← dot_cross_det,qAction_cross,hq,one_smul]
    have hcross : cross3 axisX axisY = axisZ := by norm_num [cross3,axisX,axisY,axisZ]
    rw [hcross,qAction_dot_of_unit q hq]
    norm_num [axisZ,dot]

theorem proper_rotation_iff_quaternion (R : Point →ₗ[ℝ] Point) :
    IsProperRotation R ↔ ∃ q : QuaternionCoords, qNormSq q = 1 ∧ ∀ x, qAction q x = R x := by
  constructor
  · exact proper_rotation_has_quaternion R
  · rintro ⟨q,hq,he⟩
    have hm : qActionLinear q = R := LinearMap.ext he
    rw [← hm]
    exact unit_quaternion_is_proper q hq

end Phinopert
#print axioms Phinopert.qNormSq_smul
#print axioms Phinopert.normalising_scalar
#print axioms Phinopert.normalised_quaternion_unit
#print axioms Phinopert.normalised_quaternion_action
#print axioms Phinopert.unit_first_coordinate
#print axioms Phinopert.quaternion_maps_first_axis
#print axioms Phinopert.quaternion_fixes_first_maps_second
#print axioms Phinopert.dot_cross_self
#print axioms Phinopert.dot_cross_det
#print axioms Phinopert.unit_dot_eq_one
#print axioms Phinopert.oriented_frame_third
#print axioms Phinopert.qAction_cross
#print axioms Phinopert.proper_rotation_has_quaternion
#print axioms Phinopert.unit_quaternion_is_proper
#print axioms Phinopert.proper_rotation_iff_quaternion
