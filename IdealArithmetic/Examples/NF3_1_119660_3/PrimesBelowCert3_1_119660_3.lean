import IdealArithmetic.Examples.NF3_1_119660_3.PrimesBelow3_1_119660_3F0
import IdealArithmetic.Examples.NF3_1_119660_3.PrimesBelow3_1_119660_3F1
import IdealArithmetic.Examples.NF3_1_119660_3.PrimesBelow3_1_119660_3F2

noncomputable section
abbrev eC := ![1, 31, 79, 97]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 98 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB98I0
  exact PB98I1
  exact PB98I2

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB98 : PrimesBelowBoundCertificate O 98 := by
  refine primesBelowBoundCertificate_of_Interval O eC 97 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 97 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 97 hC

lemma cert_eq_𝔭 : PB98.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 97 rfl rfl hel hC
