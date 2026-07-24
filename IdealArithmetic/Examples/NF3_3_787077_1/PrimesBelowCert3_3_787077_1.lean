import IdealArithmetic.Examples.NF3_3_787077_1.PrimesBelow3_3_787077_1F0
import IdealArithmetic.Examples.NF3_3_787077_1.PrimesBelow3_3_787077_1F1
import IdealArithmetic.Examples.NF3_3_787077_1.PrimesBelow3_3_787077_1F2
import IdealArithmetic.Examples.NF3_3_787077_1.PrimesBelow3_3_787077_1F3
import IdealArithmetic.Examples.NF3_3_787077_1.PrimesBelow3_3_787077_1F4

noncomputable section
abbrev eC := ![1, 31, 79, 137, 193, 197]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 198 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB198I0
  exact PB198I1
  exact PB198I2
  exact PB198I3
  exact PB198I4

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB198 : PrimesBelowBoundCertificate O 198 := by
  refine primesBelowBoundCertificate_of_Interval O eC 197 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 197 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 197 hC

lemma cert_eq_𝔭 : PB198.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 197 rfl rfl hel hC
