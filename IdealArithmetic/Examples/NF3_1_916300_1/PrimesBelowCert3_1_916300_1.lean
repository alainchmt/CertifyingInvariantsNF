import IdealArithmetic.Examples.NF3_1_916300_1.PrimesBelow3_1_916300_1F0
import IdealArithmetic.Examples.NF3_1_916300_1.PrimesBelow3_1_916300_1F1
import IdealArithmetic.Examples.NF3_1_916300_1.PrimesBelow3_1_916300_1F2
import IdealArithmetic.Examples.NF3_1_916300_1.PrimesBelow3_1_916300_1F3
import IdealArithmetic.Examples.NF3_1_916300_1.PrimesBelow3_1_916300_1F4
import IdealArithmetic.Examples.NF3_1_916300_1.PrimesBelow3_1_916300_1F5

noncomputable section
abbrev eC := ![1, 31, 79, 137, 193, 257, 270]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 271 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB271I0
  exact PB271I1
  exact PB271I2
  exact PB271I3
  exact PB271I4
  exact PB271I5

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB271 : PrimesBelowBoundCertificate O 271 := by
  refine primesBelowBoundCertificate_of_Interval O eC 270 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 270 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 270 hC

lemma cert_eq_𝔭 : PB271.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 270 rfl rfl hel hC
