import IdealArithmetic.Examples.NF5_1_25312500_1.PrimesBelow5_1_25312500_1F0
import IdealArithmetic.Examples.NF5_1_25312500_1.PrimesBelow5_1_25312500_1F1
import IdealArithmetic.Examples.NF5_1_25312500_1.PrimesBelow5_1_25312500_1F2
import IdealArithmetic.Examples.NF5_1_25312500_1.PrimesBelow5_1_25312500_1F3
import IdealArithmetic.Examples.NF5_1_25312500_1.PrimesBelow5_1_25312500_1F4
import IdealArithmetic.Examples.NF5_1_25312500_1.PrimesBelow5_1_25312500_1F5
import IdealArithmetic.Examples.NF5_1_25312500_1.PrimesBelow5_1_25312500_1F6
import IdealArithmetic.Examples.NF5_1_25312500_1.PrimesBelow5_1_25312500_1F7

noncomputable section
abbrev eC := ![1, 23, 61, 103, 151, 197, 251, 307, 313]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 314 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB314I0
  exact PB314I1
  exact PB314I2
  exact PB314I3
  exact PB314I4
  exact PB314I5
  exact PB314I6
  exact PB314I7

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB314 : PrimesBelowBoundCertificate O 314 := by
  refine primesBelowBoundCertificate_of_Interval O eC 313 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 313 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 313 hC

lemma cert_eq_𝔭 : PB314.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 313 rfl rfl hel hC
