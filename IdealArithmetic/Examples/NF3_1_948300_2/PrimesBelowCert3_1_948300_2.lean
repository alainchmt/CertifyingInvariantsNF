import IdealArithmetic.Examples.NF3_1_948300_2.PrimesBelow3_1_948300_2F0
import IdealArithmetic.Examples.NF3_1_948300_2.PrimesBelow3_1_948300_2F1
import IdealArithmetic.Examples.NF3_1_948300_2.PrimesBelow3_1_948300_2F2
import IdealArithmetic.Examples.NF3_1_948300_2.PrimesBelow3_1_948300_2F3
import IdealArithmetic.Examples.NF3_1_948300_2.PrimesBelow3_1_948300_2F4
import IdealArithmetic.Examples.NF3_1_948300_2.PrimesBelow3_1_948300_2F5

noncomputable section
abbrev eC := ![1, 31, 79, 137, 193, 257, 275]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 276 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB276I0
  exact PB276I1
  exact PB276I2
  exact PB276I3
  exact PB276I4
  exact PB276I5

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB276 : PrimesBelowBoundCertificate O 276 := by
  refine primesBelowBoundCertificate_of_Interval O eC 275 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 275 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 275 hC

lemma cert_eq_𝔭 : PB276.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 275 rfl rfl hel hC
