import IdealArithmetic.Examples.NF10_0_21144617347_1.PrimesBelow10_0_21144617347_1F0
import IdealArithmetic.Examples.NF10_0_21144617347_1.PrimesBelow10_0_21144617347_1F1
import IdealArithmetic.Examples.NF10_0_21144617347_1.PrimesBelow10_0_21144617347_1F2
import IdealArithmetic.Examples.NF10_0_21144617347_1.PrimesBelow10_0_21144617347_1F3
import IdealArithmetic.Examples.NF10_0_21144617347_1.PrimesBelow10_0_21144617347_1F4
import IdealArithmetic.Examples.NF10_0_21144617347_1.PrimesBelow10_0_21144617347_1F5

noncomputable section
abbrev eC := ![1, 17, 43, 73, 107, 149, 176]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 177 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB177I0
  exact PB177I1
  exact PB177I2
  exact PB177I3
  exact PB177I4
  exact PB177I5

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB177 : PrimesBelowBoundCertificate O 177 := by
  refine primesBelowBoundCertificate_of_Interval O eC 176 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 176 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 176 hC

lemma cert_eq_𝔭 : PB177.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 176 rfl rfl hel hC
