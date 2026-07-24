import IdealArithmetic.Examples.NF3_1_767839_1.PrimesBelow3_1_767839_1F0
import IdealArithmetic.Examples.NF3_1_767839_1.PrimesBelow3_1_767839_1F1
import IdealArithmetic.Examples.NF3_1_767839_1.PrimesBelow3_1_767839_1F2
import IdealArithmetic.Examples.NF3_1_767839_1.PrimesBelow3_1_767839_1F3
import IdealArithmetic.Examples.NF3_1_767839_1.PrimesBelow3_1_767839_1F4

noncomputable section
abbrev eC := ![1, 31, 79, 137, 193, 247]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 248 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB248I0
  exact PB248I1
  exact PB248I2
  exact PB248I3
  exact PB248I4

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB248 : PrimesBelowBoundCertificate O 248 := by
  refine primesBelowBoundCertificate_of_Interval O eC 247 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 247 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 247 hC

lemma cert_eq_𝔭 : PB248.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 247 rfl rfl hel hC
