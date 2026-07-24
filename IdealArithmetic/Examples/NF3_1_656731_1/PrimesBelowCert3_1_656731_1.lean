import IdealArithmetic.Examples.NF3_1_656731_1.PrimesBelow3_1_656731_1F0
import IdealArithmetic.Examples.NF3_1_656731_1.PrimesBelow3_1_656731_1F1
import IdealArithmetic.Examples.NF3_1_656731_1.PrimesBelow3_1_656731_1F2
import IdealArithmetic.Examples.NF3_1_656731_1.PrimesBelow3_1_656731_1F3
import IdealArithmetic.Examples.NF3_1_656731_1.PrimesBelow3_1_656731_1F4

noncomputable section
abbrev eC := ![1, 31, 79, 137, 193, 229]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 230 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB230I0
  exact PB230I1
  exact PB230I2
  exact PB230I3
  exact PB230I4

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB230 : PrimesBelowBoundCertificate O 230 := by
  refine primesBelowBoundCertificate_of_Interval O eC 229 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 229 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 229 hC

lemma cert_eq_𝔭 : PB230.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 229 rfl rfl hel hC
