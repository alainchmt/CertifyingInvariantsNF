import IdealArithmetic.Examples.NF3_1_975819_1.PrimesBelow3_1_975819_1F0
import IdealArithmetic.Examples.NF3_1_975819_1.PrimesBelow3_1_975819_1F1
import IdealArithmetic.Examples.NF3_1_975819_1.PrimesBelow3_1_975819_1F2
import IdealArithmetic.Examples.NF3_1_975819_1.PrimesBelow3_1_975819_1F3
import IdealArithmetic.Examples.NF3_1_975819_1.PrimesBelow3_1_975819_1F4
import IdealArithmetic.Examples.NF3_1_975819_1.PrimesBelow3_1_975819_1F5

noncomputable section
abbrev eC := ![1, 31, 79, 137, 193, 257, 279]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 280 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB280I0
  exact PB280I1
  exact PB280I2
  exact PB280I3
  exact PB280I4
  exact PB280I5

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB280 : PrimesBelowBoundCertificate O 280 := by
  refine primesBelowBoundCertificate_of_Interval O eC 279 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 279 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 279 hC

lemma cert_eq_𝔭 : PB280.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 279 rfl rfl hel hC
