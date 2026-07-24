import IdealArithmetic.Examples.NF3_1_470372_1.PrimesBelow3_1_470372_1F0
import IdealArithmetic.Examples.NF3_1_470372_1.PrimesBelow3_1_470372_1F1
import IdealArithmetic.Examples.NF3_1_470372_1.PrimesBelow3_1_470372_1F2
import IdealArithmetic.Examples.NF3_1_470372_1.PrimesBelow3_1_470372_1F3

noncomputable section
abbrev eC := ![1, 31, 79, 137, 194]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 195 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB195I0
  exact PB195I1
  exact PB195I2
  exact PB195I3

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB195 : PrimesBelowBoundCertificate O 195 := by
  refine primesBelowBoundCertificate_of_Interval O eC 194 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 194 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 194 hC

lemma cert_eq_𝔭 : PB195.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 194 rfl rfl hel hC
