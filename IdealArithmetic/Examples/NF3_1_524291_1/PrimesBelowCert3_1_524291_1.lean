import IdealArithmetic.Examples.NF3_1_524291_1.PrimesBelow3_1_524291_1F0
import IdealArithmetic.Examples.NF3_1_524291_1.PrimesBelow3_1_524291_1F1
import IdealArithmetic.Examples.NF3_1_524291_1.PrimesBelow3_1_524291_1F2
import IdealArithmetic.Examples.NF3_1_524291_1.PrimesBelow3_1_524291_1F3
import IdealArithmetic.Examples.NF3_1_524291_1.PrimesBelow3_1_524291_1F4

noncomputable section
abbrev eC := ![1, 31, 79, 137, 193, 204]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 205 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB205I0
  exact PB205I1
  exact PB205I2
  exact PB205I3
  exact PB205I4

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB205 : PrimesBelowBoundCertificate O 205 := by
  refine primesBelowBoundCertificate_of_Interval O eC 204 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 204 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 204 hC

lemma cert_eq_𝔭 : PB205.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 204 rfl rfl hel hC
