import IdealArithmetic.Examples.NF3_1_383732_1.PrimesBelow3_1_383732_1F0
import IdealArithmetic.Examples.NF3_1_383732_1.PrimesBelow3_1_383732_1F1
import IdealArithmetic.Examples.NF3_1_383732_1.PrimesBelow3_1_383732_1F2
import IdealArithmetic.Examples.NF3_1_383732_1.PrimesBelow3_1_383732_1F3

noncomputable section
abbrev eC := ![1, 31, 79, 137, 175]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 176 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB176I0
  exact PB176I1
  exact PB176I2
  exact PB176I3

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB176 : PrimesBelowBoundCertificate O 176 := by
  refine primesBelowBoundCertificate_of_Interval O eC 175 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 175 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 175 hC

lemma cert_eq_𝔭 : PB176.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 175 rfl rfl hel hC
