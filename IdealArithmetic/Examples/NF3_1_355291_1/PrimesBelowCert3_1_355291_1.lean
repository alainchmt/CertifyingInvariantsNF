import IdealArithmetic.Examples.NF3_1_355291_1.PrimesBelow3_1_355291_1F0
import IdealArithmetic.Examples.NF3_1_355291_1.PrimesBelow3_1_355291_1F1
import IdealArithmetic.Examples.NF3_1_355291_1.PrimesBelow3_1_355291_1F2
import IdealArithmetic.Examples.NF3_1_355291_1.PrimesBelow3_1_355291_1F3

noncomputable section
abbrev eC := ![1, 31, 79, 137, 168]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 169 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB169I0
  exact PB169I1
  exact PB169I2
  exact PB169I3

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB169 : PrimesBelowBoundCertificate O 169 := by
  refine primesBelowBoundCertificate_of_Interval O eC 168 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 168 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 168 hC

lemma cert_eq_𝔭 : PB169.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 168 rfl rfl hel hC
