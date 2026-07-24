import IdealArithmetic.Examples.NF3_1_905324_3.PrimesBelow3_1_905324_3F0
import IdealArithmetic.Examples.NF3_1_905324_3.PrimesBelow3_1_905324_3F1
import IdealArithmetic.Examples.NF3_1_905324_3.PrimesBelow3_1_905324_3F2
import IdealArithmetic.Examples.NF3_1_905324_3.PrimesBelow3_1_905324_3F3
import IdealArithmetic.Examples.NF3_1_905324_3.PrimesBelow3_1_905324_3F4
import IdealArithmetic.Examples.NF3_1_905324_3.PrimesBelow3_1_905324_3F5

noncomputable section
abbrev eC := ![1, 31, 79, 137, 193, 257, 269]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 270 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB270I0
  exact PB270I1
  exact PB270I2
  exact PB270I3
  exact PB270I4
  exact PB270I5

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB270 : PrimesBelowBoundCertificate O 270 := by
  refine primesBelowBoundCertificate_of_Interval O eC 269 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 269 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 269 hC

lemma cert_eq_𝔭 : PB270.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 269 rfl rfl hel hC
