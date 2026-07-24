import IdealArithmetic.Examples.NF3_1_528447_1.PrimesBelow3_1_528447_1F0
import IdealArithmetic.Examples.NF3_1_528447_1.PrimesBelow3_1_528447_1F1
import IdealArithmetic.Examples.NF3_1_528447_1.PrimesBelow3_1_528447_1F2
import IdealArithmetic.Examples.NF3_1_528447_1.PrimesBelow3_1_528447_1F3
import IdealArithmetic.Examples.NF3_1_528447_1.PrimesBelow3_1_528447_1F4

noncomputable section
abbrev eC := ![1, 31, 79, 137, 193, 205]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 206 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB206I0
  exact PB206I1
  exact PB206I2
  exact PB206I3
  exact PB206I4

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB206 : PrimesBelowBoundCertificate O 206 := by
  refine primesBelowBoundCertificate_of_Interval O eC 205 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 205 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 205 hC

lemma cert_eq_𝔭 : PB206.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 205 rfl rfl hel hC
