import IdealArithmetic.Examples.NF4_4_54381317_1.PrimesBelow4_4_54381317_1F0
import IdealArithmetic.Examples.NF4_4_54381317_1.PrimesBelow4_4_54381317_1F1
import IdealArithmetic.Examples.NF4_4_54381317_1.PrimesBelow4_4_54381317_1F2
import IdealArithmetic.Examples.NF4_4_54381317_1.PrimesBelow4_4_54381317_1F3
import IdealArithmetic.Examples.NF4_4_54381317_1.PrimesBelow4_4_54381317_1F4
import IdealArithmetic.Examples.NF4_4_54381317_1.PrimesBelow4_4_54381317_1F5
import IdealArithmetic.Examples.NF4_4_54381317_1.PrimesBelow4_4_54381317_1F6
import IdealArithmetic.Examples.NF4_4_54381317_1.PrimesBelow4_4_54381317_1F7
import IdealArithmetic.Examples.NF4_4_54381317_1.PrimesBelow4_4_54381317_1F8
import IdealArithmetic.Examples.NF4_4_54381317_1.PrimesBelow4_4_54381317_1F9
import IdealArithmetic.Examples.NF4_4_54381317_1.PrimesBelow4_4_54381317_1F10
import IdealArithmetic.Examples.NF4_4_54381317_1.PrimesBelow4_4_54381317_1F11
import IdealArithmetic.Examples.NF4_4_54381317_1.PrimesBelow4_4_54381317_1F12

noncomputable section
abbrev eC := ![1, 29, 71, 113, 173, 229, 281, 349, 409, 463, 541, 601, 659, 691]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 692 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB692I0
  exact PB692I1
  exact PB692I2
  exact PB692I3
  exact PB692I4
  exact PB692I5
  exact PB692I6
  exact PB692I7
  exact PB692I8
  exact PB692I9
  exact PB692I10
  exact PB692I11
  exact PB692I12

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB692 : PrimesBelowBoundCertificate O 692 := by
  refine primesBelowBoundCertificate_of_Interval O eC 691 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 691 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 691 hC

lemma cert_eq_𝔭 : PB692.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 691 rfl rfl hel hC
