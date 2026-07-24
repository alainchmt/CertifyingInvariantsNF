import IdealArithmetic.Examples.NF3_1_337635_1.PrimesBelow3_1_337635_1F0
import IdealArithmetic.Examples.NF3_1_337635_1.PrimesBelow3_1_337635_1F1
import IdealArithmetic.Examples.NF3_1_337635_1.PrimesBelow3_1_337635_1F2
import IdealArithmetic.Examples.NF3_1_337635_1.PrimesBelow3_1_337635_1F3

noncomputable section
abbrev eC := ![1, 31, 79, 137, 164]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 165 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB165I0
  exact PB165I1
  exact PB165I2
  exact PB165I3

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB165 : PrimesBelowBoundCertificate O 165 := by
  refine primesBelowBoundCertificate_of_Interval O eC 164 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 164 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 164 hC

lemma cert_eq_𝔭 : PB165.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 164 rfl rfl hel hC
