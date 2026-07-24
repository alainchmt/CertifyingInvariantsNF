import IdealArithmetic.Examples.NF3_1_817516_2.PrimesBelow3_1_817516_2F0
import IdealArithmetic.Examples.NF3_1_817516_2.PrimesBelow3_1_817516_2F1
import IdealArithmetic.Examples.NF3_1_817516_2.PrimesBelow3_1_817516_2F2
import IdealArithmetic.Examples.NF3_1_817516_2.PrimesBelow3_1_817516_2F3
import IdealArithmetic.Examples.NF3_1_817516_2.PrimesBelow3_1_817516_2F4

noncomputable section
abbrev eC := ![1, 31, 79, 137, 193, 255]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 256 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB256I0
  exact PB256I1
  exact PB256I2
  exact PB256I3
  exact PB256I4

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB256 : PrimesBelowBoundCertificate O 256 := by
  refine primesBelowBoundCertificate_of_Interval O eC 255 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 255 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 255 hC

lemma cert_eq_𝔭 : PB256.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 255 rfl rfl hel hC
