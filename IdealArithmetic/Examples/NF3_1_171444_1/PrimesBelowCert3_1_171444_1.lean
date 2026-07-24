import IdealArithmetic.Examples.NF3_1_171444_1.PrimesBelow3_1_171444_1F0
import IdealArithmetic.Examples.NF3_1_171444_1.PrimesBelow3_1_171444_1F1
import IdealArithmetic.Examples.NF3_1_171444_1.PrimesBelow3_1_171444_1F2

noncomputable section
abbrev eC := ![1, 31, 79, 117]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 118 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB118I0
  exact PB118I1
  exact PB118I2

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB118 : PrimesBelowBoundCertificate O 118 := by
  refine primesBelowBoundCertificate_of_Interval O eC 117 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 117 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 117 hC

lemma cert_eq_𝔭 : PB118.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 117 rfl rfl hel hC
