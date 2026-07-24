import IdealArithmetic.Examples.NF3_1_317044_1.PrimesBelow3_1_317044_1F0
import IdealArithmetic.Examples.NF3_1_317044_1.PrimesBelow3_1_317044_1F1
import IdealArithmetic.Examples.NF3_1_317044_1.PrimesBelow3_1_317044_1F2
import IdealArithmetic.Examples.NF3_1_317044_1.PrimesBelow3_1_317044_1F3

noncomputable section
abbrev eC := ![1, 31, 79, 137, 159]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 160 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB160I0
  exact PB160I1
  exact PB160I2
  exact PB160I3

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB160 : PrimesBelowBoundCertificate O 160 := by
  refine primesBelowBoundCertificate_of_Interval O eC 159 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 159 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 159 hC

lemma cert_eq_𝔭 : PB160.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 159 rfl rfl hel hC
