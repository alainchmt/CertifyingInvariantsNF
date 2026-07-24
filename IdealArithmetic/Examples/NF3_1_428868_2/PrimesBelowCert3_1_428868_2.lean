import IdealArithmetic.Examples.NF3_1_428868_2.PrimesBelow3_1_428868_2F0
import IdealArithmetic.Examples.NF3_1_428868_2.PrimesBelow3_1_428868_2F1
import IdealArithmetic.Examples.NF3_1_428868_2.PrimesBelow3_1_428868_2F2
import IdealArithmetic.Examples.NF3_1_428868_2.PrimesBelow3_1_428868_2F3

noncomputable section
abbrev eC := ![1, 31, 79, 137, 185]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 186 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB186I0
  exact PB186I1
  exact PB186I2
  exact PB186I3

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB186 : PrimesBelowBoundCertificate O 186 := by
  refine primesBelowBoundCertificate_of_Interval O eC 185 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 185 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 185 hC

lemma cert_eq_𝔭 : PB186.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 185 rfl rfl hel hC
