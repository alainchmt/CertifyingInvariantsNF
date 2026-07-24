import IdealArithmetic.Examples.NF3_3_936117_1.PrimesBelow3_3_936117_1F0
import IdealArithmetic.Examples.NF3_3_936117_1.PrimesBelow3_3_936117_1F1
import IdealArithmetic.Examples.NF3_3_936117_1.PrimesBelow3_3_936117_1F2
import IdealArithmetic.Examples.NF3_3_936117_1.PrimesBelow3_3_936117_1F3
import IdealArithmetic.Examples.NF3_3_936117_1.PrimesBelow3_3_936117_1F4

noncomputable section
abbrev eC := ![1, 31, 79, 137, 193, 215]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 216 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB216I0
  exact PB216I1
  exact PB216I2
  exact PB216I3
  exact PB216I4

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB216 : PrimesBelowBoundCertificate O 216 := by
  refine primesBelowBoundCertificate_of_Interval O eC 215 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 215 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 215 hC

lemma cert_eq_𝔭 : PB216.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 215 rfl rfl hel hC
