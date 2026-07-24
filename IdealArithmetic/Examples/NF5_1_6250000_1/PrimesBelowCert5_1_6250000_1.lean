import IdealArithmetic.Examples.NF5_1_6250000_1.PrimesBelow5_1_6250000_1F0
import IdealArithmetic.Examples.NF5_1_6250000_1.PrimesBelow5_1_6250000_1F1
import IdealArithmetic.Examples.NF5_1_6250000_1.PrimesBelow5_1_6250000_1F2
import IdealArithmetic.Examples.NF5_1_6250000_1.PrimesBelow5_1_6250000_1F3

noncomputable section
abbrev eC := ![1, 23, 61, 103, 155]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 156 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB156I0
  exact PB156I1
  exact PB156I2
  exact PB156I3

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB156 : PrimesBelowBoundCertificate O 156 := by
  refine primesBelowBoundCertificate_of_Interval O eC 155 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 155 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 155 hC

lemma cert_eq_𝔭 : PB156.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 155 rfl rfl hel hC
