import IdealArithmetic.Examples.NF3_1_401464_1.PrimesBelow3_1_401464_1F0
import IdealArithmetic.Examples.NF3_1_401464_1.PrimesBelow3_1_401464_1F1
import IdealArithmetic.Examples.NF3_1_401464_1.PrimesBelow3_1_401464_1F2
import IdealArithmetic.Examples.NF3_1_401464_1.PrimesBelow3_1_401464_1F3

noncomputable section
abbrev eC := ![1, 31, 79, 137, 179]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 180 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB180I0
  exact PB180I1
  exact PB180I2
  exact PB180I3

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB180 : PrimesBelowBoundCertificate O 180 := by
  refine primesBelowBoundCertificate_of_Interval O eC 179 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 179 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 179 hC

lemma cert_eq_𝔭 : PB180.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 179 rfl rfl hel hC
