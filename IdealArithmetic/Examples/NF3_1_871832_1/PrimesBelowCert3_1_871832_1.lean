import IdealArithmetic.Examples.NF3_1_871832_1.PrimesBelow3_1_871832_1F0
import IdealArithmetic.Examples.NF3_1_871832_1.PrimesBelow3_1_871832_1F1
import IdealArithmetic.Examples.NF3_1_871832_1.PrimesBelow3_1_871832_1F2
import IdealArithmetic.Examples.NF3_1_871832_1.PrimesBelow3_1_871832_1F3
import IdealArithmetic.Examples.NF3_1_871832_1.PrimesBelow3_1_871832_1F4
import IdealArithmetic.Examples.NF3_1_871832_1.PrimesBelow3_1_871832_1F5

noncomputable section
abbrev eC := ![1, 31, 79, 137, 193, 257, 264]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 265 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB265I0
  exact PB265I1
  exact PB265I2
  exact PB265I3
  exact PB265I4
  exact PB265I5

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB265 : PrimesBelowBoundCertificate O 265 := by
  refine primesBelowBoundCertificate_of_Interval O eC 264 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 264 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 264 hC

lemma cert_eq_𝔭 : PB265.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 264 rfl rfl hel hC
