import IdealArithmetic.Examples.NF5_1_24300000_2.PrimesBelow5_1_24300000_2F0
import IdealArithmetic.Examples.NF5_1_24300000_2.PrimesBelow5_1_24300000_2F1
import IdealArithmetic.Examples.NF5_1_24300000_2.PrimesBelow5_1_24300000_2F2
import IdealArithmetic.Examples.NF5_1_24300000_2.PrimesBelow5_1_24300000_2F3
import IdealArithmetic.Examples.NF5_1_24300000_2.PrimesBelow5_1_24300000_2F4
import IdealArithmetic.Examples.NF5_1_24300000_2.PrimesBelow5_1_24300000_2F5
import IdealArithmetic.Examples.NF5_1_24300000_2.PrimesBelow5_1_24300000_2F6

noncomputable section
abbrev eC := ![1, 23, 61, 103, 151, 197, 251, 306]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 307 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB307I0
  exact PB307I1
  exact PB307I2
  exact PB307I3
  exact PB307I4
  exact PB307I5
  exact PB307I6

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB307 : PrimesBelowBoundCertificate O 307 := by
  refine primesBelowBoundCertificate_of_Interval O eC 306 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 306 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 306 hC

lemma cert_eq_𝔭 : PB307.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 306 rfl rfl hel hC
