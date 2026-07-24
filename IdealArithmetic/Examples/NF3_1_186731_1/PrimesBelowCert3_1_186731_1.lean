import IdealArithmetic.Examples.NF3_1_186731_1.PrimesBelow3_1_186731_1F0
import IdealArithmetic.Examples.NF3_1_186731_1.PrimesBelow3_1_186731_1F1
import IdealArithmetic.Examples.NF3_1_186731_1.PrimesBelow3_1_186731_1F2

noncomputable section
abbrev eC := ![1, 31, 79, 122]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 123 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB123I0
  exact PB123I1
  exact PB123I2

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB123 : PrimesBelowBoundCertificate O 123 := by
  refine primesBelowBoundCertificate_of_Interval O eC 122 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 122 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 122 hC

lemma cert_eq_𝔭 : PB123.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 122 rfl rfl hel hC
