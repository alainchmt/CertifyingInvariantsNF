import IdealArithmetic.Examples.NF3_1_692259_1.PrimesBelow3_1_692259_1F0
import IdealArithmetic.Examples.NF3_1_692259_1.PrimesBelow3_1_692259_1F1
import IdealArithmetic.Examples.NF3_1_692259_1.PrimesBelow3_1_692259_1F2
import IdealArithmetic.Examples.NF3_1_692259_1.PrimesBelow3_1_692259_1F3
import IdealArithmetic.Examples.NF3_1_692259_1.PrimesBelow3_1_692259_1F4

noncomputable section
abbrev eC := ![1, 31, 79, 137, 193, 235]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 236 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB236I0
  exact PB236I1
  exact PB236I2
  exact PB236I3
  exact PB236I4

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB236 : PrimesBelowBoundCertificate O 236 := by
  refine primesBelowBoundCertificate_of_Interval O eC 235 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 235 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 235 hC

lemma cert_eq_𝔭 : PB236.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 235 rfl rfl hel hC
