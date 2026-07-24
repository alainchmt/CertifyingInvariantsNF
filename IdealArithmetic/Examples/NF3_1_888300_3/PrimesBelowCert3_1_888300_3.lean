import IdealArithmetic.Examples.NF3_1_888300_3.PrimesBelow3_1_888300_3F0
import IdealArithmetic.Examples.NF3_1_888300_3.PrimesBelow3_1_888300_3F1
import IdealArithmetic.Examples.NF3_1_888300_3.PrimesBelow3_1_888300_3F2
import IdealArithmetic.Examples.NF3_1_888300_3.PrimesBelow3_1_888300_3F3
import IdealArithmetic.Examples.NF3_1_888300_3.PrimesBelow3_1_888300_3F4
import IdealArithmetic.Examples.NF3_1_888300_3.PrimesBelow3_1_888300_3F5

noncomputable section
abbrev eC := ![1, 31, 79, 137, 193, 257, 266]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 267 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB267I0
  exact PB267I1
  exact PB267I2
  exact PB267I3
  exact PB267I4
  exact PB267I5

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB267 : PrimesBelowBoundCertificate O 267 := by
  refine primesBelowBoundCertificate_of_Interval O eC 266 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 266 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 266 hC

lemma cert_eq_𝔭 : PB267.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 266 rfl rfl hel hC
