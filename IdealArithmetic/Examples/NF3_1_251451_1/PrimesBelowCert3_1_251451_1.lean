import IdealArithmetic.Examples.NF3_1_251451_1.PrimesBelow3_1_251451_1F0
import IdealArithmetic.Examples.NF3_1_251451_1.PrimesBelow3_1_251451_1F1
import IdealArithmetic.Examples.NF3_1_251451_1.PrimesBelow3_1_251451_1F2
import IdealArithmetic.Examples.NF3_1_251451_1.PrimesBelow3_1_251451_1F3

noncomputable section
abbrev eC := ![1, 31, 79, 137, 141]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 142 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB142I0
  exact PB142I1
  exact PB142I2
  exact PB142I3

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB142 : PrimesBelowBoundCertificate O 142 := by
  refine primesBelowBoundCertificate_of_Interval O eC 141 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 141 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 141 hC

lemma cert_eq_𝔭 : PB142.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 141 rfl rfl hel hC
