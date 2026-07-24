import IdealArithmetic.Examples.NF3_1_925444_2.PrimesBelow3_1_925444_2F0
import IdealArithmetic.Examples.NF3_1_925444_2.PrimesBelow3_1_925444_2F1
import IdealArithmetic.Examples.NF3_1_925444_2.PrimesBelow3_1_925444_2F2
import IdealArithmetic.Examples.NF3_1_925444_2.PrimesBelow3_1_925444_2F3
import IdealArithmetic.Examples.NF3_1_925444_2.PrimesBelow3_1_925444_2F4
import IdealArithmetic.Examples.NF3_1_925444_2.PrimesBelow3_1_925444_2F5

noncomputable section
abbrev eC := ![1, 31, 79, 137, 193, 257, 272]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 273 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB273I0
  exact PB273I1
  exact PB273I2
  exact PB273I3
  exact PB273I4
  exact PB273I5

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB273 : PrimesBelowBoundCertificate O 273 := by
  refine primesBelowBoundCertificate_of_Interval O eC 272 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 272 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 272 hC

lemma cert_eq_𝔭 : PB273.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 272 rfl rfl hel hC
