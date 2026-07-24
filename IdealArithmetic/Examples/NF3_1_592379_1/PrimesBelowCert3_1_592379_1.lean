import IdealArithmetic.Examples.NF3_1_592379_1.PrimesBelow3_1_592379_1F0
import IdealArithmetic.Examples.NF3_1_592379_1.PrimesBelow3_1_592379_1F1
import IdealArithmetic.Examples.NF3_1_592379_1.PrimesBelow3_1_592379_1F2
import IdealArithmetic.Examples.NF3_1_592379_1.PrimesBelow3_1_592379_1F3
import IdealArithmetic.Examples.NF3_1_592379_1.PrimesBelow3_1_592379_1F4

noncomputable section
abbrev eC := ![1, 31, 79, 137, 193, 217]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 218 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB218I0
  exact PB218I1
  exact PB218I2
  exact PB218I3
  exact PB218I4

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB218 : PrimesBelowBoundCertificate O 218 := by
  refine primesBelowBoundCertificate_of_Interval O eC 217 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 217 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 217 hC

lemma cert_eq_𝔭 : PB218.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 217 rfl rfl hel hC
