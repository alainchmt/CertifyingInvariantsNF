import IdealArithmetic.Examples.NF3_1_132020_1.PrimesBelow3_1_132020_1F0
import IdealArithmetic.Examples.NF3_1_132020_1.PrimesBelow3_1_132020_1F1
import IdealArithmetic.Examples.NF3_1_132020_1.PrimesBelow3_1_132020_1F2

noncomputable section
abbrev eC := ![1, 31, 79, 102]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 103 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB103I0
  exact PB103I1
  exact PB103I2

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB103 : PrimesBelowBoundCertificate O 103 := by
  refine primesBelowBoundCertificate_of_Interval O eC 102 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 102 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 102 hC

lemma cert_eq_𝔭 : PB103.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 102 rfl rfl hel hC
