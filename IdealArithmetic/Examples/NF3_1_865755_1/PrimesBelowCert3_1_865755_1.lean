import IdealArithmetic.Examples.NF3_1_865755_1.PrimesBelow3_1_865755_1F0
import IdealArithmetic.Examples.NF3_1_865755_1.PrimesBelow3_1_865755_1F1
import IdealArithmetic.Examples.NF3_1_865755_1.PrimesBelow3_1_865755_1F2
import IdealArithmetic.Examples.NF3_1_865755_1.PrimesBelow3_1_865755_1F3
import IdealArithmetic.Examples.NF3_1_865755_1.PrimesBelow3_1_865755_1F4
import IdealArithmetic.Examples.NF3_1_865755_1.PrimesBelow3_1_865755_1F5

noncomputable section
abbrev eC := ![1, 31, 79, 137, 193, 257, 263]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 264 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB264I0
  exact PB264I1
  exact PB264I2
  exact PB264I3
  exact PB264I4
  exact PB264I5

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB264 : PrimesBelowBoundCertificate O 264 := by
  refine primesBelowBoundCertificate_of_Interval O eC 263 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 263 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 263 hC

lemma cert_eq_𝔭 : PB264.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 263 rfl rfl hel hC
