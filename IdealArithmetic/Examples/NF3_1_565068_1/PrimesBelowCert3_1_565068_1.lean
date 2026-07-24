import IdealArithmetic.Examples.NF3_1_565068_1.PrimesBelow3_1_565068_1F0
import IdealArithmetic.Examples.NF3_1_565068_1.PrimesBelow3_1_565068_1F1
import IdealArithmetic.Examples.NF3_1_565068_1.PrimesBelow3_1_565068_1F2
import IdealArithmetic.Examples.NF3_1_565068_1.PrimesBelow3_1_565068_1F3
import IdealArithmetic.Examples.NF3_1_565068_1.PrimesBelow3_1_565068_1F4

noncomputable section
abbrev eC := ![1, 31, 79, 137, 193, 212]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 213 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB213I0
  exact PB213I1
  exact PB213I2
  exact PB213I3
  exact PB213I4

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB213 : PrimesBelowBoundCertificate O 213 := by
  refine primesBelowBoundCertificate_of_Interval O eC 212 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 212 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 212 hC

lemma cert_eq_𝔭 : PB213.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 212 rfl rfl hel hC
