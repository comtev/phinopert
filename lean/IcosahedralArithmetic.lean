import Symmetry

/-! Integer arithmetic for exact quaternion data. Stored coordinates represent
(a+b*sqrt(5))/4. Products have denominator 16; witnesses are scaled by 4.
All finite checks use kernel `decide`, never `native_decide`. -/
namespace Phinopert
abbrev I5 := ℤ × ℤ
abbrev IQ := I5 × I5 × I5 × I5
abbrev IP := I5 × I5 × I5
def ia (x y : I5) : I5 := (x.1+y.1,x.2+y.2)
def ine (x : I5) : I5 := (-x.1,-x.2)
def isu (x y : I5) : I5 := ia x (ine y)
def im (x y : I5) : I5 := (x.1*y.1+5*x.2*y.2,x.1*y.2+x.2*y.1)
def isc (k : ℤ) (x : I5) : I5 := (k*x.1,k*x.2)
def iqScale (k : ℤ) (p : IQ) : IQ :=
  (isc k p.1,isc k p.2.1,isc k p.2.2.1,isc k p.2.2.2)
def iqMul (p q : IQ) : IQ :=
  (isu (isu (isu (im p.1 q.1) (im p.2.1 q.2.1)) (im p.2.2.1 q.2.2.1))
      (im p.2.2.2 q.2.2.2),
   isu (ia (ia (im p.1 q.2.1) (im p.2.1 q.1)) (im p.2.2.1 q.2.2.2))
      (im p.2.2.2 q.2.2.1),
   ia (ia (isu (im p.1 q.2.2.1) (im p.2.1 q.2.2.2)) (im p.2.2.1 q.1))
      (im p.2.2.2 q.2.1),
   ia (isu (ia (im p.1 q.2.2.2) (im p.2.1 q.2.2.1)) (im p.2.2.1 q.2.1))
      (im p.2.2.2 q.1))
def iqNorm (p : IQ) : I5 :=
  ia (ia (ia (im p.1 p.1) (im p.2.1 p.2.1)) (im p.2.2.1 p.2.2.1))
    (im p.2.2.2 p.2.2.2)
def ipScale (k : ℤ) (p : IP) : IP := (isc k p.1,isc k p.2.1,isc k p.2.2)
def iqAction (q : IQ) (p : IP) : IP :=
  (ia (ia (im (isu (isu (ia (im q.1 q.1) (im q.2.1 q.2.1))
      (im q.2.2.1 q.2.2.1)) (im q.2.2.2 q.2.2.2)) p.1)
    (im (isc 2 (isu (im q.2.1 q.2.2.1) (im q.1 q.2.2.2))) p.2.1))
    (im (isc 2 (ia (im q.2.1 q.2.2.2) (im q.1 q.2.2.1))) p.2.2),
   ia (ia (im (isc 2 (ia (im q.2.1 q.2.2.1) (im q.1 q.2.2.2))) p.1)
    (im (isu (ia (isu (im q.1 q.1) (im q.2.1 q.2.1))
      (im q.2.2.1 q.2.2.1)) (im q.2.2.2 q.2.2.2)) p.2.1))
    (im (isc 2 (isu (im q.2.2.1 q.2.2.2) (im q.1 q.2.1))) p.2.2),
   ia (ia (im (isc 2 (isu (im q.2.1 q.2.2.2) (im q.1 q.2.2.1))) p.1)
    (im (isc 2 (ia (im q.2.2.1 q.2.2.2) (im q.1 q.2.1))) p.2.1))
    (im (ia (isu (isu (im q.1 q.1) (im q.2.1 q.2.1))
      (im q.2.2.1 q.2.2.1)) (im q.2.2.2 q.2.2.2)) p.2.2))
def ieval (s : ℝ) (c : I5) : ℝ := c.1+c.2*s

theorem ieval_add (s : ℝ) (p q : I5) : ieval s (ia p q)=ieval s p+ieval s q := by
  simp [ieval,ia]; ring
theorem ieval_neg (s : ℝ) (p : I5) : ieval s (ine p)= -ieval s p := by
  simp [ieval,ine]; ring
theorem ieval_sub (s : ℝ) (p q : I5) : ieval s (isu p q)=ieval s p-ieval s q := by
  simp [isu,ieval_add,ieval_neg,sub_eq_add_neg]
theorem ieval_scale (s : ℝ) (k : ℤ) (p : I5) : ieval s (isc k p)=k*ieval s p := by
  simp [ieval,isc]; ring
theorem ieval_mul (s : ℝ) (hs : s*s=5) (p q : I5) :
    ieval s (im p q)=ieval s p*ieval s q := by
  simp only [ieval,im,Int.cast_add,Int.cast_mul,Int.cast_ofNat]
  have hs2 : s^2=5 := by nlinarith
  ring_nf
  rw [hs2]

end Phinopert
#print axioms Phinopert.ieval_add
#print axioms Phinopert.ieval_neg
#print axioms Phinopert.ieval_sub
#print axioms Phinopert.ieval_scale
#print axioms Phinopert.ieval_mul
