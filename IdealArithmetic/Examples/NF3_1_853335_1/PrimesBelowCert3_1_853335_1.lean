import IdealArithmetic.Examples.NF3_1_853335_1.PrimesBelow3_1_853335_1F0
import IdealArithmetic.Examples.NF3_1_853335_1.PrimesBelow3_1_853335_1F1
import IdealArithmetic.Examples.NF3_1_853335_1.PrimesBelow3_1_853335_1F2
import IdealArithmetic.Examples.NF3_1_853335_1.PrimesBelow3_1_853335_1F3
import IdealArithmetic.Examples.NF3_1_853335_1.PrimesBelow3_1_853335_1F4

noncomputable section
abbrev eC := ![1, 31, 79, 137, 193, 261]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 262 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB262I0
  exact PB262I1
  exact PB262I2
  exact PB262I3
  exact PB262I4

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB262 : PrimesBelowBoundCertificate O 262 := by
  refine primesBelowBoundCertificate_of_Interval O eC 261 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 261 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 261 hC

lemma cert_eq_𝔭 : PB262.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 261 rfl rfl hel hC
