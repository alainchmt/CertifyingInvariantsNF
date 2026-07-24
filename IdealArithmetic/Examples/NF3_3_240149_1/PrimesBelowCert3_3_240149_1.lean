import IdealArithmetic.Examples.NF3_3_240149_1.PrimesBelow3_3_240149_1F0
import IdealArithmetic.Examples.NF3_3_240149_1.PrimesBelow3_3_240149_1F1
import IdealArithmetic.Examples.NF3_3_240149_1.PrimesBelow3_3_240149_1F2

noncomputable section
abbrev eC := ![1, 31, 79, 108]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 109 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB109I0
  exact PB109I1
  exact PB109I2

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB109 : PrimesBelowBoundCertificate O 109 := by
  refine primesBelowBoundCertificate_of_Interval O eC 108 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 108 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 108 hC

lemma cert_eq_𝔭 : PB109.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 108 rfl rfl hel hC
