import IdealArithmetic.Examples.NF3_1_965796_1.PrimesBelow3_1_965796_1F0
import IdealArithmetic.Examples.NF3_1_965796_1.PrimesBelow3_1_965796_1F1
import IdealArithmetic.Examples.NF3_1_965796_1.PrimesBelow3_1_965796_1F2
import IdealArithmetic.Examples.NF3_1_965796_1.PrimesBelow3_1_965796_1F3
import IdealArithmetic.Examples.NF3_1_965796_1.PrimesBelow3_1_965796_1F4
import IdealArithmetic.Examples.NF3_1_965796_1.PrimesBelow3_1_965796_1F5

noncomputable section
abbrev eC := ![1, 31, 79, 137, 193, 257, 278]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 279 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB279I0
  exact PB279I1
  exact PB279I2
  exact PB279I3
  exact PB279I4
  exact PB279I5

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB279 : PrimesBelowBoundCertificate O 279 := by
  refine primesBelowBoundCertificate_of_Interval O eC 278 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 278 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 278 hC

lemma cert_eq_𝔭 : PB279.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 278 rfl rfl hel hC
