import IdealArithmetic.Examples.NF3_1_205556_1.PrimesBelow3_1_205556_1F0
import IdealArithmetic.Examples.NF3_1_205556_1.PrimesBelow3_1_205556_1F1
import IdealArithmetic.Examples.NF3_1_205556_1.PrimesBelow3_1_205556_1F2

noncomputable section
abbrev eC := ![1, 31, 79, 128]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 129 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB129I0
  exact PB129I1
  exact PB129I2

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB129 : PrimesBelowBoundCertificate O 129 := by
  refine primesBelowBoundCertificate_of_Interval O eC 128 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 128 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 128 hC

lemma cert_eq_𝔭 : PB129.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 128 rfl rfl hel hC
