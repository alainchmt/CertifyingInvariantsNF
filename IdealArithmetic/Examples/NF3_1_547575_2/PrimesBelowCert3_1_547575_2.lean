import IdealArithmetic.Examples.NF3_1_547575_2.PrimesBelow3_1_547575_2F0
import IdealArithmetic.Examples.NF3_1_547575_2.PrimesBelow3_1_547575_2F1
import IdealArithmetic.Examples.NF3_1_547575_2.PrimesBelow3_1_547575_2F2
import IdealArithmetic.Examples.NF3_1_547575_2.PrimesBelow3_1_547575_2F3
import IdealArithmetic.Examples.NF3_1_547575_2.PrimesBelow3_1_547575_2F4

noncomputable section
abbrev eC := ![1, 31, 79, 137, 193, 209]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 210 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB210I0
  exact PB210I1
  exact PB210I2
  exact PB210I3
  exact PB210I4

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB210 : PrimesBelowBoundCertificate O 210 := by
  refine primesBelowBoundCertificate_of_Interval O eC 209 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 209 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 209 hC

lemma cert_eq_𝔭 : PB210.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 209 rfl rfl hel hC
