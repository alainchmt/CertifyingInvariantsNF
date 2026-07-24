import IdealArithmetic.Examples.NF3_1_280904_4.PrimesBelow3_1_280904_4F0
import IdealArithmetic.Examples.NF3_1_280904_4.PrimesBelow3_1_280904_4F1
import IdealArithmetic.Examples.NF3_1_280904_4.PrimesBelow3_1_280904_4F2
import IdealArithmetic.Examples.NF3_1_280904_4.PrimesBelow3_1_280904_4F3

noncomputable section
abbrev eC := ![1, 31, 79, 137, 149]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 150 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB150I0
  exact PB150I1
  exact PB150I2
  exact PB150I3

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB150 : PrimesBelowBoundCertificate O 150 := by
  refine primesBelowBoundCertificate_of_Interval O eC 149 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 149 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 149 hC

lemma cert_eq_𝔭 : PB150.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 149 rfl rfl hel hC
