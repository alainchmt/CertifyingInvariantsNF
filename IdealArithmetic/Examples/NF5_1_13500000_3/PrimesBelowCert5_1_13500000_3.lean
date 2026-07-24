import IdealArithmetic.Examples.NF5_1_13500000_3.PrimesBelow5_1_13500000_3F0
import IdealArithmetic.Examples.NF5_1_13500000_3.PrimesBelow5_1_13500000_3F1
import IdealArithmetic.Examples.NF5_1_13500000_3.PrimesBelow5_1_13500000_3F2
import IdealArithmetic.Examples.NF5_1_13500000_3.PrimesBelow5_1_13500000_3F3
import IdealArithmetic.Examples.NF5_1_13500000_3.PrimesBelow5_1_13500000_3F4
import IdealArithmetic.Examples.NF5_1_13500000_3.PrimesBelow5_1_13500000_3F5

noncomputable section
abbrev eC := ![1, 23, 61, 103, 151, 197, 228]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 229 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB229I0
  exact PB229I1
  exact PB229I2
  exact PB229I3
  exact PB229I4
  exact PB229I5

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB229 : PrimesBelowBoundCertificate O 229 := by
  refine primesBelowBoundCertificate_of_Interval O eC 228 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 228 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 228 hC

lemma cert_eq_𝔭 : PB229.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 228 rfl rfl hel hC
