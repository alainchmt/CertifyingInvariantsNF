import IdealArithmetic.Examples.NF3_1_720575_1.PrimesBelow3_1_720575_1F0
import IdealArithmetic.Examples.NF3_1_720575_1.PrimesBelow3_1_720575_1F1
import IdealArithmetic.Examples.NF3_1_720575_1.PrimesBelow3_1_720575_1F2
import IdealArithmetic.Examples.NF3_1_720575_1.PrimesBelow3_1_720575_1F3
import IdealArithmetic.Examples.NF3_1_720575_1.PrimesBelow3_1_720575_1F4

noncomputable section
abbrev eC := ![1, 31, 79, 137, 193, 240]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 241 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB241I0
  exact PB241I1
  exact PB241I2
  exact PB241I3
  exact PB241I4

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB241 : PrimesBelowBoundCertificate O 241 := by
  refine primesBelowBoundCertificate_of_Interval O eC 240 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 240 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 240 hC

lemma cert_eq_𝔭 : PB241.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 240 rfl rfl hel hC
