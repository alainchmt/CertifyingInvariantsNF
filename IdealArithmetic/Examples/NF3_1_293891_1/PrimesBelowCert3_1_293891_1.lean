import IdealArithmetic.Examples.NF3_1_293891_1.PrimesBelow3_1_293891_1F0
import IdealArithmetic.Examples.NF3_1_293891_1.PrimesBelow3_1_293891_1F1
import IdealArithmetic.Examples.NF3_1_293891_1.PrimesBelow3_1_293891_1F2
import IdealArithmetic.Examples.NF3_1_293891_1.PrimesBelow3_1_293891_1F3

noncomputable section
abbrev eC := ![1, 31, 79, 137, 153]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 154 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB154I0
  exact PB154I1
  exact PB154I2
  exact PB154I3

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB154 : PrimesBelowBoundCertificate O 154 := by
  refine primesBelowBoundCertificate_of_Interval O eC 153 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 153 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 153 hC

lemma cert_eq_𝔭 : PB154.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 153 rfl rfl hel hC
