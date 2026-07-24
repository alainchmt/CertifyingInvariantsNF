import IdealArithmetic.Examples.NF3_1_894348_3.PrimesBelow3_1_894348_3F0
import IdealArithmetic.Examples.NF3_1_894348_3.PrimesBelow3_1_894348_3F1
import IdealArithmetic.Examples.NF3_1_894348_3.PrimesBelow3_1_894348_3F2
import IdealArithmetic.Examples.NF3_1_894348_3.PrimesBelow3_1_894348_3F3
import IdealArithmetic.Examples.NF3_1_894348_3.PrimesBelow3_1_894348_3F4
import IdealArithmetic.Examples.NF3_1_894348_3.PrimesBelow3_1_894348_3F5

noncomputable section
abbrev eC := ![1, 31, 79, 137, 193, 257, 267]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 268 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB268I0
  exact PB268I1
  exact PB268I2
  exact PB268I3
  exact PB268I4
  exact PB268I5

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB268 : PrimesBelowBoundCertificate O 268 := by
  refine primesBelowBoundCertificate_of_Interval O eC 267 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 267 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 267 hC

lemma cert_eq_𝔭 : PB268.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 267 rfl rfl hel hC
