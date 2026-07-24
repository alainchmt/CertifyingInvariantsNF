import IdealArithmetic.Examples.NF3_3_370548_2.PrimesBelow3_3_370548_2F0
import IdealArithmetic.Examples.NF3_3_370548_2.PrimesBelow3_3_370548_2F1
import IdealArithmetic.Examples.NF3_3_370548_2.PrimesBelow3_3_370548_2F2

noncomputable section
abbrev eC := ![1, 31, 79, 135]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 136 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB136I0
  exact PB136I1
  exact PB136I2

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB136 : PrimesBelowBoundCertificate O 136 := by
  refine primesBelowBoundCertificate_of_Interval O eC 135 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 135 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 135 hC

lemma cert_eq_𝔭 : PB136.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 135 rfl rfl hel hC
