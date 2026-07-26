import IdealArithmetic.Examples.NF5_1_3790297_2.PrimesBelow5_1_3790297_2F0
import IdealArithmetic.Examples.NF5_1_3790297_2.PrimesBelow5_1_3790297_2F1
import IdealArithmetic.Examples.NF5_1_3790297_2.PrimesBelow5_1_3790297_2F2
import IdealArithmetic.Examples.NF5_1_3790297_2.PrimesBelow5_1_3790297_2F3

noncomputable section
abbrev eC := ![1, 23, 61, 103, 121]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 122 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB122I0
  exact PB122I1
  exact PB122I2
  exact PB122I3

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB122 : PrimesBelowBoundCertificate O 122 := by
  refine primesBelowBoundCertificate_of_Interval O eC 121 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 121 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 121 hC

lemma cert_eq_𝔭 : PB122.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 121 rfl rfl hel hC
