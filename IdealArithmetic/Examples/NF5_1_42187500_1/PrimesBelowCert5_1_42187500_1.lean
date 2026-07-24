import IdealArithmetic.Examples.NF5_1_42187500_1.PrimesBelow5_1_42187500_1F0
import IdealArithmetic.Examples.NF5_1_42187500_1.PrimesBelow5_1_42187500_1F1
import IdealArithmetic.Examples.NF5_1_42187500_1.PrimesBelow5_1_42187500_1F2
import IdealArithmetic.Examples.NF5_1_42187500_1.PrimesBelow5_1_42187500_1F3
import IdealArithmetic.Examples.NF5_1_42187500_1.PrimesBelow5_1_42187500_1F4
import IdealArithmetic.Examples.NF5_1_42187500_1.PrimesBelow5_1_42187500_1F5
import IdealArithmetic.Examples.NF5_1_42187500_1.PrimesBelow5_1_42187500_1F6
import IdealArithmetic.Examples.NF5_1_42187500_1.PrimesBelow5_1_42187500_1F7
import IdealArithmetic.Examples.NF5_1_42187500_1.PrimesBelow5_1_42187500_1F8

noncomputable section
abbrev eC := ![1, 23, 61, 103, 151, 197, 251, 307, 359, 404]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 405 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB405I0
  exact PB405I1
  exact PB405I2
  exact PB405I3
  exact PB405I4
  exact PB405I5
  exact PB405I6
  exact PB405I7
  exact PB405I8

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB405 : PrimesBelowBoundCertificate O 405 := by
  refine primesBelowBoundCertificate_of_Interval O eC 404 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 404 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 404 hC

lemma cert_eq_𝔭 : PB405.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 404 rfl rfl hel hC
