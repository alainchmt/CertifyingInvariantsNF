import IdealArithmetic.Examples.NF3_1_903756_2.PrimesBelow3_1_903756_2F0
import IdealArithmetic.Examples.NF3_1_903756_2.PrimesBelow3_1_903756_2F1
import IdealArithmetic.Examples.NF3_1_903756_2.PrimesBelow3_1_903756_2F2
import IdealArithmetic.Examples.NF3_1_903756_2.PrimesBelow3_1_903756_2F3
import IdealArithmetic.Examples.NF3_1_903756_2.PrimesBelow3_1_903756_2F4
import IdealArithmetic.Examples.NF3_1_903756_2.PrimesBelow3_1_903756_2F5

noncomputable section
abbrev eC := ![1, 31, 79, 137, 193, 257, 268]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 269 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB269I0
  exact PB269I1
  exact PB269I2
  exact PB269I3
  exact PB269I4
  exact PB269I5

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB269 : PrimesBelowBoundCertificate O 269 := by
  refine primesBelowBoundCertificate_of_Interval O eC 268 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 268 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 268 hC

lemma cert_eq_𝔭 : PB269.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 268 rfl rfl hel hC
