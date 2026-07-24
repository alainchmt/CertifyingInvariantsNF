import IdealArithmetic.Examples.NF5_1_3515625_1.PrimesBelow5_1_3515625_1F0
import IdealArithmetic.Examples.NF5_1_3515625_1.PrimesBelow5_1_3515625_1F1
import IdealArithmetic.Examples.NF5_1_3515625_1.PrimesBelow5_1_3515625_1F2
import IdealArithmetic.Examples.NF5_1_3515625_1.PrimesBelow5_1_3515625_1F3

noncomputable section
abbrev eC := ![1, 23, 61, 103, 116]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 117 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB117I0
  exact PB117I1
  exact PB117I2
  exact PB117I3

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB117 : PrimesBelowBoundCertificate O 117 := by
  refine primesBelowBoundCertificate_of_Interval O eC 116 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 116 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 116 hC

lemma cert_eq_𝔭 : PB117.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 116 rfl rfl hel hC
