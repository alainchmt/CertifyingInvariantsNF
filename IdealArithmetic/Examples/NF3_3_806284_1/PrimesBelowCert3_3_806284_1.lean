import IdealArithmetic.Examples.NF3_3_806284_1.PrimesBelow3_3_806284_1F0
import IdealArithmetic.Examples.NF3_3_806284_1.PrimesBelow3_3_806284_1F1
import IdealArithmetic.Examples.NF3_3_806284_1.PrimesBelow3_3_806284_1F2
import IdealArithmetic.Examples.NF3_3_806284_1.PrimesBelow3_3_806284_1F3
import IdealArithmetic.Examples.NF3_3_806284_1.PrimesBelow3_3_806284_1F4

noncomputable section
abbrev eC := ![1, 31, 79, 137, 193, 199]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 200 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB200I0
  exact PB200I1
  exact PB200I2
  exact PB200I3
  exact PB200I4

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB200 : PrimesBelowBoundCertificate O 200 := by
  refine primesBelowBoundCertificate_of_Interval O eC 199 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 199 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 199 hC

lemma cert_eq_𝔭 : PB200.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 199 rfl rfl hel hC
