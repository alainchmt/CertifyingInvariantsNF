import IdealArithmetic.Examples.NF5_1_8100000_3.PrimesBelow5_1_8100000_3F0
import IdealArithmetic.Examples.NF5_1_8100000_3.PrimesBelow5_1_8100000_3F1
import IdealArithmetic.Examples.NF5_1_8100000_3.PrimesBelow5_1_8100000_3F2
import IdealArithmetic.Examples.NF5_1_8100000_3.PrimesBelow5_1_8100000_3F3
import IdealArithmetic.Examples.NF5_1_8100000_3.PrimesBelow5_1_8100000_3F4

noncomputable section
abbrev eC := ![1, 23, 61, 103, 151, 177]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 178 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB178I0
  exact PB178I1
  exact PB178I2
  exact PB178I3
  exact PB178I4

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB178 : PrimesBelowBoundCertificate O 178 := by
  refine primesBelowBoundCertificate_of_Interval O eC 177 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 177 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 177 hC

lemma cert_eq_𝔭 : PB178.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 177 rfl rfl hel hC
