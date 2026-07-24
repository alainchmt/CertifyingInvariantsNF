import IdealArithmetic.Examples.NF3_1_343980_3.PrimesBelow3_1_343980_3F0
import IdealArithmetic.Examples.NF3_1_343980_3.PrimesBelow3_1_343980_3F1
import IdealArithmetic.Examples.NF3_1_343980_3.PrimesBelow3_1_343980_3F2
import IdealArithmetic.Examples.NF3_1_343980_3.PrimesBelow3_1_343980_3F3

noncomputable section
abbrev eC := ![1, 31, 79, 137, 165]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 166 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB166I0
  exact PB166I1
  exact PB166I2
  exact PB166I3

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB166 : PrimesBelowBoundCertificate O 166 := by
  refine primesBelowBoundCertificate_of_Interval O eC 165 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 165 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 165 hC

lemma cert_eq_𝔭 : PB166.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 165 rfl rfl hel hC
