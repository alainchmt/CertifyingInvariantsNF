import IdealArithmetic.Examples.NF3_1_463091_1.PrimesBelow3_1_463091_1F0
import IdealArithmetic.Examples.NF3_1_463091_1.PrimesBelow3_1_463091_1F1
import IdealArithmetic.Examples.NF3_1_463091_1.PrimesBelow3_1_463091_1F2
import IdealArithmetic.Examples.NF3_1_463091_1.PrimesBelow3_1_463091_1F3

noncomputable section
abbrev eC := ![1, 31, 79, 137, 192]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 193 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB193I0
  exact PB193I1
  exact PB193I2
  exact PB193I3

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB193 : PrimesBelowBoundCertificate O 193 := by
  refine primesBelowBoundCertificate_of_Interval O eC 192 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 192 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 192 hC

lemma cert_eq_𝔭 : PB193.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 192 rfl rfl hel hC
