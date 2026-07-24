import IdealArithmetic.Examples.NF3_1_371640_1.PrimesBelow3_1_371640_1F0
import IdealArithmetic.Examples.NF3_1_371640_1.PrimesBelow3_1_371640_1F1
import IdealArithmetic.Examples.NF3_1_371640_1.PrimesBelow3_1_371640_1F2
import IdealArithmetic.Examples.NF3_1_371640_1.PrimesBelow3_1_371640_1F3

noncomputable section
abbrev eC := ![1, 31, 79, 137, 172]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 173 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB173I0
  exact PB173I1
  exact PB173I2
  exact PB173I3

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB173 : PrimesBelowBoundCertificate O 173 := by
  refine primesBelowBoundCertificate_of_Interval O eC 172 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 172 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 172 hC

lemma cert_eq_𝔭 : PB173.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 172 rfl rfl hel hC
