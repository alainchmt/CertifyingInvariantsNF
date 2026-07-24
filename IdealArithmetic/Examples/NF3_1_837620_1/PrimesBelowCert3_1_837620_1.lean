import IdealArithmetic.Examples.NF3_1_837620_1.PrimesBelow3_1_837620_1F0
import IdealArithmetic.Examples.NF3_1_837620_1.PrimesBelow3_1_837620_1F1
import IdealArithmetic.Examples.NF3_1_837620_1.PrimesBelow3_1_837620_1F2
import IdealArithmetic.Examples.NF3_1_837620_1.PrimesBelow3_1_837620_1F3
import IdealArithmetic.Examples.NF3_1_837620_1.PrimesBelow3_1_837620_1F4

noncomputable section
abbrev eC := ![1, 31, 79, 137, 193, 258]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 259 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB259I0
  exact PB259I1
  exact PB259I2
  exact PB259I3
  exact PB259I4

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB259 : PrimesBelowBoundCertificate O 259 := by
  refine primesBelowBoundCertificate_of_Interval O eC 258 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 258 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 258 hC

lemma cert_eq_𝔭 : PB259.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 258 rfl rfl hel hC
