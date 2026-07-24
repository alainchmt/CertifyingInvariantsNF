import IdealArithmetic.Examples.NF3_1_703080_1.PrimesBelow3_1_703080_1F0
import IdealArithmetic.Examples.NF3_1_703080_1.PrimesBelow3_1_703080_1F1
import IdealArithmetic.Examples.NF3_1_703080_1.PrimesBelow3_1_703080_1F2
import IdealArithmetic.Examples.NF3_1_703080_1.PrimesBelow3_1_703080_1F3
import IdealArithmetic.Examples.NF3_1_703080_1.PrimesBelow3_1_703080_1F4

noncomputable section
abbrev eC := ![1, 31, 79, 137, 193, 237]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 238 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB238I0
  exact PB238I1
  exact PB238I2
  exact PB238I3
  exact PB238I4

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB238 : PrimesBelowBoundCertificate O 238 := by
  refine primesBelowBoundCertificate_of_Interval O eC 237 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 237 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 237 hC

lemma cert_eq_𝔭 : PB238.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 237 rfl rfl hel hC
