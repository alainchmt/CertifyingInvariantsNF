import IdealArithmetic.Examples.NF3_1_933107_2.PrimesBelow3_1_933107_2F0
import IdealArithmetic.Examples.NF3_1_933107_2.PrimesBelow3_1_933107_2F1
import IdealArithmetic.Examples.NF3_1_933107_2.PrimesBelow3_1_933107_2F2
import IdealArithmetic.Examples.NF3_1_933107_2.PrimesBelow3_1_933107_2F3
import IdealArithmetic.Examples.NF3_1_933107_2.PrimesBelow3_1_933107_2F4
import IdealArithmetic.Examples.NF3_1_933107_2.PrimesBelow3_1_933107_2F5

noncomputable section
abbrev eC := ![1, 31, 79, 137, 193, 257, 273]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 274 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB274I0
  exact PB274I1
  exact PB274I2
  exact PB274I3
  exact PB274I4
  exact PB274I5

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB274 : PrimesBelowBoundCertificate O 274 := by
  refine primesBelowBoundCertificate_of_Interval O eC 273 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 273 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 273 hC

lemma cert_eq_𝔭 : PB274.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 273 rfl rfl hel hC
