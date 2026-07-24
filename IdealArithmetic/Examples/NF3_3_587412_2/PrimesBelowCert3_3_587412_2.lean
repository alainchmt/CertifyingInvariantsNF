import IdealArithmetic.Examples.NF3_3_587412_2.PrimesBelow3_3_587412_2F0
import IdealArithmetic.Examples.NF3_3_587412_2.PrimesBelow3_3_587412_2F1
import IdealArithmetic.Examples.NF3_3_587412_2.PrimesBelow3_3_587412_2F2
import IdealArithmetic.Examples.NF3_3_587412_2.PrimesBelow3_3_587412_2F3

noncomputable section
abbrev eC := ![1, 31, 79, 137, 170]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 171 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB171I0
  exact PB171I1
  exact PB171I2
  exact PB171I3

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB171 : PrimesBelowBoundCertificate O 171 := by
  refine primesBelowBoundCertificate_of_Interval O eC 170 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 170 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 170 hC

lemma cert_eq_𝔭 : PB171.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 170 rfl rfl hel hC
