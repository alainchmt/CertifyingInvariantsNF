import IdealArithmetic.Examples.NF3_3_418605_1.PrimesBelow3_3_418605_1F0
import IdealArithmetic.Examples.NF3_3_418605_1.PrimesBelow3_3_418605_1F1
import IdealArithmetic.Examples.NF3_3_418605_1.PrimesBelow3_3_418605_1F2
import IdealArithmetic.Examples.NF3_3_418605_1.PrimesBelow3_3_418605_1F3

noncomputable section
abbrev eC := ![1, 31, 79, 137, 143]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 144 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB144I0
  exact PB144I1
  exact PB144I2
  exact PB144I3

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB144 : PrimesBelowBoundCertificate O 144 := by
  refine primesBelowBoundCertificate_of_Interval O eC 143 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 143 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 143 hC

lemma cert_eq_𝔭 : PB144.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 143 rfl rfl hel hC
