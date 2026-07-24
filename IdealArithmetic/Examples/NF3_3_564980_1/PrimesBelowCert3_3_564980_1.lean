import IdealArithmetic.Examples.NF3_3_564980_1.PrimesBelow3_3_564980_1F0
import IdealArithmetic.Examples.NF3_3_564980_1.PrimesBelow3_3_564980_1F1
import IdealArithmetic.Examples.NF3_3_564980_1.PrimesBelow3_3_564980_1F2
import IdealArithmetic.Examples.NF3_3_564980_1.PrimesBelow3_3_564980_1F3

noncomputable section
abbrev eC := ![1, 31, 79, 137, 167]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 168 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB168I0
  exact PB168I1
  exact PB168I2
  exact PB168I3

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB168 : PrimesBelowBoundCertificate O 168 := by
  refine primesBelowBoundCertificate_of_Interval O eC 167 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 167 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 167 hC

lemma cert_eq_𝔭 : PB168.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 167 rfl rfl hel hC
